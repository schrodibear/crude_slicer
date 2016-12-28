(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016                                                    *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "-4-9-44-42"]

open Extlib

open Cil_types
open Cil_datatype
open Cil
open Cil_printer
open Format
open Visitor

module Console = Options

let (%) f g x = f (g x)
let (%>) f g x = g (f x)
let const f _x = f
let const' f x _y = f x

module Primitive_type : sig
  type t = private typ

  val of_typ : typ -> t option
  val of_typ_exn : typ -> t
  val pp : formatter -> t -> unit
end = struct
  type t = typ

  let of_typ t =
    let t = unrollTypeDeep t in
    if isArithmeticOrPointerType t then Some t
    else None

  let of_typ_exn t =
    if isArithmeticOrPointerType @@ unrollType t then t
    else invalid_arg "Primitive_type.of_typ_exn"

  let pp fmt = fprintf fmt "%a" pp_typ
end

module Make_var (C : sig val is_ok : varinfo -> bool end) : sig
  type t = private varinfo

  val of_varinfo : varinfo -> t option
  val of_varinfo_exn : varinfo -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val pp : formatter -> t -> unit
end = struct
  type t = varinfo

  let of_varinfo vi = if C.is_ok vi then Some vi else None

  let of_varinfo_exn vi =
    if C.is_ok vi then vi
    else invalid_arg "Formal_var.of_varinfo_exn"

  let compare v1 v2 = Varinfo.compare (v1 :> varinfo) (v2 :> varinfo)
  let equal v1 v2 = Varinfo.equal (v1 :> varinfo) (v2 :> varinfo)
  let hash v = Varinfo.hash (v :> varinfo)
  let pp fmt = fprintf fmt "%a" pp_varinfo
end

module Global_var = Make_var (struct let is_ok vi = vi.vglob end)

module Struct_field : sig
  type t = private fieldinfo

  val of_fieldinfo : fieldinfo -> t option
  val of_fieldinfo_exn : fieldinfo -> t
  val pp : formatter -> t -> unit
end = struct
  type t = fieldinfo

  let of_fieldinfo fi = if fi.fcomp.cstruct then Some fi else None

  let of_fieldinfo_exn fi =
    if fi.fcomp.cstruct then fi
    else invalid_arg "Struct_field.of_fieldinfo_exn"

  let pp fmt fi = fprintf fmt "%s.%s" fi.fcomp.cname fi.fname
end

module Region = struct
  type t =
    | Variable of Global_var.t
    | Field of Struct_field.t
    | Type_approximation of Primitive_type.t

  let compare r1 r2 =
    match r1, r2 with
    | Variable v1, Variable v2 -> Varinfo.compare (v1 :> varinfo) (v2 :> varinfo)
    | Variable _, _ -> -1
    | Field f1, Field f2 -> Fieldinfo.compare (f1 :> fieldinfo) (f2 :> fieldinfo)
    | Field _, Variable _ -> 1
    | Field _, _ -> -1
    | Type_approximation t1, Type_approximation t2 -> Typ.compare (t1 :> typ) (t2 :> typ)
    | Type_approximation _, _ -> 1

  let equal r1 r2 =
    match r1, r2 with
    | Variable v1, Variable v2 -> Varinfo.equal (v1 :> varinfo) (v2 :> varinfo)
    | Field f1, Field f2 -> Fieldinfo.equal (f1 :> fieldinfo) (f2 :> fieldinfo)
    | Type_approximation t1, Type_approximation t2 -> Typ.equal (t1 :> typ) (t2 :> typ)
    | Variable _, (Field _ | Type_approximation _)
    | Field _, (Variable _ | Type_approximation _)
    | Type_approximation _, (Variable _ | Field _) -> false

  let hash =
    function
    | Variable v1 -> 7 * Varinfo.hash (v1 :> varinfo)
    | Field f -> 7 * Fieldinfo.hash (f :> fieldinfo) + 1
    | Type_approximation t -> 7 * Typ.hash (t :> typ) + 2

  let pp fmttr =
    let pp fmt = fprintf fmttr fmt in
    function
    | Variable v -> pp "%a" Global_var.pp v
    | Field f -> pp "%a" Struct_field.pp f
    | Type_approximation t -> pp "(%a)" Primitive_type.pp t
end

module Flag : sig
  type t
  val create : unit -> t
  val report : t -> unit
  val reported : t -> bool
  val clear : t -> unit
end = struct
  type t = bool ref
  let create () = ref false
  let report f = f := true
  let reported f = !f
  let clear f = f := false
end

module type Printable_hashed_type = sig
  include Hashtbl.HashedType
  val pp : formatter -> t -> unit
end

module type Reporting_bithashset = sig
  type elt
  type t
  val create : Flag.t -> t
  val clear : t -> unit
  val copy : Flag.t -> t -> t
  val add : elt -> t -> unit
  val import : from:t -> t -> unit
  val remove : elt -> t -> unit
  val mem : elt -> t -> bool
  val intersects : t -> t -> bool
  val iter : (elt -> unit) -> t -> unit
  val filter_inplace : (elt -> bool) -> t -> unit
  val fold : (elt -> 'b -> 'b) -> t -> 'b -> 'b
  val length : t -> int
  val is_empty : t -> bool
  val flag : t -> Flag.t
  val stats : unit -> Hashtbl.statistics
  val pp : formatter -> t -> unit
end

module Make_reporting_hashset (M : Printable_hashed_type) : Reporting_bithashset with type elt = M.t =
struct
  type elt = M.t
  module H = Hashtbl.Make (M)
  module H' = Hashtbl.Make (struct type t = int let hash = id let equal : int -> _ -> _ = (=) end)

  let size = 5000

  let index, elem, stats =
    let h = H.create size and h' = H'.create size in
    let i = ref ~-1 in
    (fun e ->
       try
         H.find h e
       with
       | Not_found ->
         incr i;
         H.replace h e !i;
         H'.replace h' !i e;
         !i),
    (fun i ->
       try
         H'.find h' i
       with
       | Not_found -> failwith "Reporting_bithashset.elem: Can't find element"),
    fun () -> H.stats h

  type nonrec t = Bv.t * Flag.t
  let create f = Bv.create ~size false, f
  let clear (v, f) =
    if Bv.is_empty v then Flag.report f;
    Bv.clear v
  let copy f (v, _) = Bv.copy v, f
  let add e (v, f) =
    let i = index e in
    if not (Bv.get v i) then Flag.report f;
    Bv.set v i
  let import ~from:(from, _) (v, f) =
    if not (Bv.subset from v) then Flag.report f;
    Bv.union_into ~into:v from
  let remove e (v, f) =
    let i = index e in
    if Bv.get v i then Flag.report f;
    Bv.reset v i
  let mem e (v, _) = Bv.get v (index e)
  let intersects (v1, _) (v2, _) = Bv.inters v1 v2
  let iter f (v, _) = Bv.iter_true v (fun i -> f (elem i))
  let filter_inplace f (v, fl) = Bv.filter v (fun i -> if not @@ f (elem i) then (Flag.report fl; false) else true)
  let fold f (v, _) x =
    let r = ref x in
    Bv.iter_true v (fun i -> r := f (elem i) !r);
    !r
  let length (v, _) = Bv.cardinal v
  let is_empty (v, _) = Bv.is_empty v
  let flag (_, f) = f
  let pp fmt v =
    fprintf fmt "{@[%a@]}"
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") M.pp) (fold List.cons v [])
end

module type Set = sig
  type t
  type 'a kind
  val create : Flag.t -> t
  val add : 'a kind -> 'a -> t -> unit
  val import : from:t -> t -> unit
  val flag : t -> Flag.t
  val copy : Flag.t -> t -> t
  val pp : formatter -> t -> unit
end

module Make_reporting_hashmap (M_key : Printable_hashed_type) (S : Set) : sig
  type key = M_key.t
  type set = S.t
  type 'a kind = 'a S.kind
  type t
  val create : Flag.t -> t
  val clear : t -> unit
  val copy : Flag.t -> t -> t
  val shallow_copy : Flag.t -> t -> t
  val add : key -> 'a kind -> 'a -> t -> unit
  val import : from:t -> t -> unit
  val import_values : key -> set -> t -> unit
  val remove : key -> t -> unit
  val mem : key -> t -> bool
  val iter : (key -> set -> unit) -> t -> unit
  exception Different_flag
  val filter_map_inplace : ?check:bool -> (key -> set -> set option) -> t -> unit
  val find : key -> t -> set
  val fold : (key -> set -> 'b -> 'b) -> t -> 'b -> 'b
  val length : t -> int
  val flag : t -> Flag.t
  val stats : t -> Hashtbl.statistics
  val pp : formatter -> t -> unit
end = struct
  type key = M_key.t
  type set = S.t
  type 'a kind = 'a S.kind
  module H = Hashtbl.Make(M_key)
  type nonrec t = S.t H.t * Flag.t
  let create f =
    H.create 32, f
  let clear (h, f) =
    if H.length h > 0 then Flag.report f;
    H.clear h
  let copy f (h, _) =
    let r = H.copy h in
    H.filter_map_inplace (fun _ r -> Some (S.copy f r)) r;
    r, f
  let shallow_copy f (h, _) = H.copy h, f
  let add k kind e (h, f) =
    if not (H.mem h k) then (Flag.report f; H.replace h k (S.create f));
    S.add kind e (H.find h k)
  let import ~from:(from, _) (h, f) =
    H.iter
      (fun k from ->
         if not (H.mem h k) then (Flag.report f; H.replace h k (S.create f));
         S.import ~from (H.find h k))
      from
  let import_values k from (h, f) =
    if not (H.mem h k) then (Flag.report f; H.replace h k (S.create f));
    S.import ~from (H.find h k)
  let remove k (h, f) =
    if H.mem h k then Flag.report f;
    H.remove h k
  let mem k (h, _) = H.mem h k
  let iter f (h, _) =
    H.iter f h
  let find k (h, f) =
    try H.find h k
    with Not_found ->
      let r = S.create f in
      Flag.report f;
      H.replace h k r;
      r
  exception Different_flag
  let filter_map_inplace ?(check=true) f (h, fl) =
    H.filter_map_inplace
      (fun e set ->
         let r = f e set in
         match r with
         | None -> Flag.report fl; None
         | Some s -> if check && S.flag s != fl then raise Different_flag else (if s != set then Flag.report fl; r))
      h
  let fold f (h, _) x =
    H.fold f h x
  let length (h, _) = H.length h
  let flag (_, f) = f
  let stats (h, _) = H.stats h
  let pp fmt (h, _) =
    fprintf fmt "  [@[%a@]]"
      (pp_print_list
         ~pp_sep:(fun fmt () -> fprintf fmt ";@;")
         (fun fmt (k, h) -> fprintf fmt "@[%a@ ->@ @[%a@]@]" M_key.pp k S.pp h))
      (H.fold (fun k h -> List.cons (k, h)) h [])
end

module H_region = Make_reporting_hashset (Region)

module Formal_var = Make_var (struct let is_ok vi = vi.vformal end)

module H_formal_var = Make_reporting_hashset (Formal_var)

module Local_var = Make_var (struct let is_ok vi = not vi.vglob && not vi.vformal end)

module H_local_var = Make_reporting_hashset (Local_var)

module Writes = struct
  type t =
    | Global of Region.t
    | Local of Local_var.t
    | Poly of Formal_var.t
    | Result

  let compare w1 w2 =
    match w1, w2 with
    | Global r1, Global r2 -> Region.compare r1 r2
    | Global _, _ -> -1
    | Local _, Global _ -> 1
    | Local v1, Local v2 -> Local_var.compare v1 v2
    | Local _, _ -> -1
    | Poly v1, Poly v2 -> Formal_var.compare v1 v2
    | Poly _, Result -> -1
    | Poly _, _ -> 1
    | Result, Result -> 0
    | Result, _ -> 1

  let equal w1 w2 =
    match w1, w2 with
    | Global r1, Global r2 -> Region.equal r1 r2
    | Local v1, Local v2 -> Local_var.equal v1 v2
    | Poly v1, Poly v2 -> Formal_var.equal v1 v2
    | Result, Result -> true
    | _ -> false

  let hash =
    function
    | Global r -> Region.hash r * 11
    | Local v -> 3 * Local_var.hash v + 1
    | Poly v -> 5 * Formal_var.hash v + 3
    | Result -> 7

  let pp fmttr =
    let pp fmt = fprintf fmttr fmt in
    function
    | Global r -> pp "%a" Region.pp r
    | Local v -> pp "~%a" Local_var.pp v
    | Poly v -> pp "\'%a" Formal_var.pp v
    | Result -> pp "R"
end

module Reads : sig
  type t

  type _ kind =
    | Global : Region.t kind
    | Poly : Formal_var.t kind
    | Local : Local_var.t kind

  type some = Some : 'a kind * 'a -> some

  val of_writes : Writes.t -> some option

  val create : Flag.t -> t
  val clear : t -> unit
  val import : from:t -> t -> unit
  val add_global : Region.t -> t -> unit
  val add_poly : Formal_var.t -> t -> unit
  val add_local : Local_var.t -> t -> unit
  val add : 'a kind -> 'a -> t -> unit
  val mem : 'a kind -> 'a -> t -> bool
  val intersects : t -> t -> bool
  val flag : t -> Flag.t
  val copy : Flag.t -> t -> t

  val iter_global : (Region.t -> unit) -> t -> unit
  val iter_poly : (Formal_var.t -> unit) -> t -> unit
  val iter_local : (Local_var.t -> unit) -> t -> unit

  val pp : formatter -> t -> unit
end = struct
  type t =
    {
      global : H_region.t;
      poly   : H_formal_var.t;
      local  : H_local_var.t
    }

  type _ kind =
    | Global : Region.t kind
    | Poly : Formal_var.t kind
    | Local : Local_var.t kind

  type some = Some : 'a kind * 'a -> some

  let of_writes : _ -> some option =
    function
    | Writes.Global r -> Some (Some (Global, r))
    | Writes.Local v -> Some (Some (Local, v))
    | Writes.Poly v -> Some (Some (Poly, v))
    | Writes.Result -> None

  let create f = { global = H_region.create f; poly = H_formal_var.create f; local = H_local_var.create f }
  let clear r = H_region.clear r.global; H_formal_var.clear r.poly; H_local_var.clear r.local
  let import ~from r =
    H_region.import ~from:from.global r.global;
    H_formal_var.import ~from:from.poly r.poly;
    H_local_var.import ~from:from.local r.local
  let add_global g r = H_region.add g r.global
  let add_poly v r = H_formal_var.add v r.poly
  let add_local v r = H_local_var.add v r.local
  let add : type a. a kind -> a -> _ = fun k x r ->
    match k with
    | Global -> H_region.add x r.global
    | Poly -> H_formal_var.add x r.poly
    | Local -> H_local_var.add x r.local
  let mem : type a. a kind -> a -> _ = fun k x r ->
    match k with
    | Global -> H_region.mem x r.global
    | Poly -> H_formal_var.mem x r.poly
    | Local -> H_local_var.mem x r.local
  let intersects r1 r2 =
    H_region.intersects r1.global r2.global ||
    H_formal_var.intersects r1.poly r2.poly ||
    H_local_var.intersects r1.local r2.local
  let flag r = H_region.flag r.global
  let copy f r =
    { global = H_region.copy f r.global; poly = H_formal_var.copy f r.poly; local = H_local_var.copy f r.local }

  let iter_global f r = H_region.iter f r.global
  let iter_poly f r = H_formal_var.iter f r.poly
  let iter_local f r = H_local_var.iter f r.local

  let pp fmt r =
    fprintf fmt "  @[gl:%a,@ @,pol:%a,@ @,loc:%a@]" H_region.pp r.global H_formal_var.pp r.poly H_local_var.pp r.local
end

module Fundec = struct include Fundec let pp = pretty end
module Stmt = struct include Stmt let pp = pretty end

module H_fundec = Make_reporting_hashset (Fundec)
module H_stmt = Make_reporting_hashset (Stmt)

module Requires : sig
  type t

  val create : Flag.t -> t
  val import : from:t -> t -> unit
  val add_body : fundec -> t -> unit
  val add_stmt : stmt -> t -> unit
  val copy : Flag.t -> t -> t

  val iter_bodies : (fundec -> unit) -> t -> unit
  val iter_stmts : (stmt -> unit) -> t -> unit
  val has_body : fundec -> t -> bool
  val has_stmt : stmt -> t -> bool
end = struct
  type t =
    {
      bodies : H_fundec.t;
      stmts  : H_stmt.t
    }

  let create f = { bodies = H_fundec.create f; stmts = H_stmt.create f }
  let import ~from r =
    H_fundec.import ~from:from.bodies r.bodies;
    H_stmt.import ~from:from.stmts r.stmts
  let add_body f r = H_fundec.add f r.bodies
  let add_stmt s r = H_stmt.add s r.stmts
  let copy f r = { bodies = H_fundec.copy f r.bodies; stmts = H_stmt.copy f r.stmts }

  let iter_bodies f r = H_fundec.iter f r.bodies
  let iter_stmts f r = H_stmt.iter f r.stmts
  let has_body f r = H_fundec.mem f r.bodies
  let has_stmt s r = H_stmt.mem s r.stmts
end

module H_write = Make_reporting_hashmap (Writes) (Reads)

module Effect : sig
  type t

  val create : Flag.t -> t
  val reads : Writes.t -> t -> Reads.t
  val depends : t -> Reads.t
  val add_reads : Writes.t -> Reads.t -> t -> unit
  val add_writes : H_write.t -> t -> unit
  val add_global_read : Writes.t -> Region.t -> t -> unit
  val add_poly_read : Writes.t -> Formal_var.t -> t -> unit
  val add_local_read : Writes.t -> Local_var.t -> t -> unit
  val add_global_dep : Region.t -> t -> unit
  val add_poly_dep : Formal_var.t -> t -> unit
  val add_local_dep : Local_var.t -> t -> unit
  val add_depends : Reads.t -> t -> unit
  val add_result_dep : t -> unit
  val add_requires : Requires.t -> t -> unit
  val add_body_req : fundec -> t -> unit
  val add_stmt_req : stmt -> t -> unit
  val set_is_target : t -> unit
  val shallow_copy_writes : Flag.t -> t -> H_write.t
  val copy : Flag.t -> t -> t

  val iter_writes : (Writes.t -> Reads.t -> unit) -> t -> unit
  val is_target : t -> bool
  val iter_global_deps : (Region.t -> unit) -> t -> unit
  val iter_poly_deps : (Formal_var.t -> unit) -> t -> unit
  val iter_local_deps : (Local_var.t -> unit) -> t -> unit
  val has_result_dep : t -> bool
  val iter_body_reqs : (fundec -> unit) -> t -> unit
  val iter_stmt_reqs : (stmt -> unit) -> t -> unit
  val has_body_req : fundec -> t -> bool
  val has_stmt_req : stmt -> t -> bool
  val flag : t -> Flag.t

  val pp : formatter -> t -> unit
end = struct
  type t =
    {
              writes     : H_write.t;
      mutable is_target  : bool;
              depends    : Reads.t;
      mutable result_dep : bool;
              requires   : Requires.t;
              flag       : Flag.t;
    }

  let create f =
    {
      writes = H_write.create f;
      is_target = false;
      depends = Reads.create f;
      result_dep = false;
      requires = Requires.create f;
      flag = f
    }

  let reads w e = H_write.find w e.writes
  let depends e = e.depends
  let add_writes from e = H_write.import ~from e.writes
  let add_reads w from e = H_write.import_values w from e.writes
  let add_global_read w r e = Reads.add_global r (reads w e)
  let add_poly_read w p e = Reads.add_poly p (reads w e)
  let add_local_read w l e = Reads.add_local l (reads w e)
  let add_global_dep d e = Reads.add_global d e.depends
  let add_poly_dep d e = Reads.add_poly d e.depends
  let add_local_dep d e = Reads.add_local d e.depends
  let add_depends d e = Reads.import ~from:d e.depends
  let add_result_dep e = if not e.result_dep then Flag.report e.flag; e.result_dep <- true
  let add_requires d e = Requires.import ~from:d e.requires
  let set_is_target e = if not e.is_target then Flag.report e.flag; e.is_target <- true

  let add_body_req f e = Requires.add_body f e.requires
  let add_stmt_req s e = Requires.add_stmt s e.requires
  let has_body_req f e = Requires.has_body f e.requires
  let has_stmt_req s e = Requires.has_stmt s e.requires
  let shallow_copy_writes f e = H_write.shallow_copy f e.writes
  let copy f e =
    {
      writes = H_write.copy f e.writes;
      is_target = e.is_target;
      depends = Reads.copy f e.depends;
      result_dep = e.result_dep;
      requires = Requires.copy f e.requires;
      flag = f
    }

  let iter_writes f e = H_write.iter f e.writes
  let is_target e = e.is_target
  let iter_global_deps f e = Reads.iter_global f e.depends
  let iter_poly_deps f e = Reads.iter_poly f e.depends
  let iter_local_deps f e = Reads.iter_local f e.depends
  let has_result_dep e = e.result_dep
  let iter_body_reqs f e = Requires.iter_bodies f e.requires
  let iter_stmt_reqs f e = Requires.iter_stmts f e.requires
  let flag e = e.flag

  let pp fmt e =
    fprintf fmt "@[w:@;@[%a@];@.tar:%B;@.deps:@;%a;@.RD:%B@]"
      H_write.pp e.writes e.is_target Reads.pp e.depends e.result_dep
end

module File_info = struct
  module H = Fundec.Hashtbl
  type t = Effect.t H.t

  let create () = H.create 256
  let get fi fl f = try H.find fi f with Not_found -> let r = Effect.create fl in H.replace fi f r; r
end

let rec until_convergence f fi scc fl =
  f fi scc;
  if not (Flag.reported fl) then ()
  else (Flag.clear fl; until_convergence f fi scc fl)

let until_convergence f fi scc fl =
  Flag.clear fl;
  until_convergence f fi scc fl

class type ['a] frama_c_collector = object inherit frama_c_inplace method finish : 'a end

let visit_until_convergence ~order (v : _ -> _ -> _ -> _ #frama_c_collector) fi sccs =
  let iter =
    match order with
    | `topological -> List.iter
    | `reversed -> fun f l -> List.(iter f (rev l))
  in
  let fl = Flag.create () in
  iter
    (fun scc ->
       let scc = List.(Kernel_function.(scc |> filter is_definition |> map get_definition)) in
       until_convergence
         (fun fi ->
            List.iter
              (fun d ->
                 Console.debug "Analysing function %s..." d.svar.vname;
                 let v = v fl fi d in
                 ignore @@ visitFramacFunction (v :> frama_c_visitor) d;
                 v#finish;
                 Console.debug "Resulting effect is:@.%a@." Effect.pp @@ File_info.get fi fl d))
         fi
         scc
         fl)
    sccs

let rec add_from_lval acc =
  let add_parameter vi = Reads.add_poly (Formal_var.of_varinfo_exn vi) acc in
  let add_global vi = Reads.add_global (Region.Variable (Global_var.of_varinfo_exn vi)) acc in
  let add_local vi = Reads.add_local (Local_var.of_varinfo_exn vi) acc in
  let add_field fi = Reads.add_global (Region.Field (Struct_field.of_fieldinfo_exn fi)) acc in
  let add_type typ =
    let typ = typeDeepDropAllAttributes @@ unrollTypeDeep typ in
    Reads.add_global (Region.Type_approximation (Primitive_type.of_typ_exn typ)) acc
  in
  fun lv ->
    let typ = typeOfLval lv in
    if isArithmeticOrPointerType typ then
      match lv with
      | Var ({ vformal = true; vaddrof = false; _ } as vi), NoOffset                    -> add_parameter vi
      | Var ({ vglob = true; vaddrof = false; _ } as vi), NoOffset                      -> add_global vi
      | Var ({ vaddrof = false; _ } as vi), NoOffset                                    -> add_local vi
      | _, off ->
        match lastOffset off with
        | Field ({ fcomp = { cstruct = true; _ }; faddrof = false; _ } as fi, NoOffset) -> add_field fi
        | _                                                                             -> add_type typ
    else
      match unrollType typ with
      | TInt _
      | TEnum _
      | TFloat _
      | TPtr _
      | TNamed _                                                                        -> assert false
      (* Unrolled, not a pointer or arithmetic *)
      | TVoid _                                                                         -> add_type charType
      | TArray _                                                                        ->
        add_from_lval acc @@ addOffsetLval (Index (integer ~loc:Location.unknown 0, NoOffset)) lv
      | TFun _ as t                                                                     -> add_type (TPtr (t, []))
      | TComp (ci, _, _)                                                                ->
        List.iter (fun fi -> add_from_lval acc @@ addOffsetLval (Field (fi, NoOffset)) lv) ci.cfields
      | TBuiltin_va_list _                                                              -> add_type voidPtrType

class vertex_collector vertices =
  object
    inherit frama_c_inplace
    method! vlval lv =
      add_from_lval vertices lv;
      DoChildren
  end

let add_from_expr acc =
  let o = new vertex_collector acc in
  fun e -> ignore (visitFramacExpr (o :> frama_c_visitor) e)

let add_from_lval lv acc = add_from_lval acc lv
let add_from_expr lv acc = add_from_expr acc lv

let get_addressed_kfs =
  let cache = ref None in
  fun () ->
    let fill () =
      let o =
        object(self)
          val mutable result = []
          method add vi = result <- Globals.Functions.get vi :: result
          method get = result

          inherit frama_c_inplace
          method !vexpr e =
            match e.enode with
            | AddrOf (Var vi, NoOffset) when isFunctionType vi.vtype ->
              self#add vi;
              SkipChildren
            | _ ->
              DoChildren
          method! vlval (lv, _) =
            match lv with
            | Var ({ vaddrof = true; vtype } as vi) when isFunctionType vtype ->
              self#add vi;
              SkipChildren
            | _ -> DoChildren
        end
      in
      Visitor.visitFramacFileSameGlobals (o :> frama_c_visitor) @@ Ast.get ();
      o#get
    in
    match !cache with
    | None ->
      let r = fill () in
      cache := Some r;
      r
    | Some r -> r

let filter_matching_kfs params =
  get_addressed_kfs () |>
  List.filter
    (fun kf ->
       let formals = Kernel_function.get_formals kf in
       if Kernel_function.is_definition kf && List.(length formals = length params) then
         List.for_all2 (fun vi e -> not @@ need_cast vi.vtype @@ typeOf e) formals params
       else false)

let take n l =
  let rec loop n dst = function
    | h :: t when n > 0 ->
      loop (n - 1) (h :: dst) t
    | _ -> List.rev dst
  in
  loop n [] l

let project_reads ~fundec ~params =
  let params =
    if
      match unrollType fundec.svar.vtype with
      | TFun (_, _, true, _) -> true
      | _ -> false
    then take (List.length fundec.sformals) params
    else params
  in
  let params = List.(combine fundec.sformals @@ map add_from_expr params) in
  fun from acc ->
    Reads.iter_poly (fun fv -> (List.assoc (fv :> varinfo) params) acc) from;
    Reads.iter_global (fun r -> Reads.add_global r acc) from

let add_transitive_closure =
  let module Vertex = struct
    type t = Writes.t * Reads.t
    let compare (a, _) (b, _) = Writes.compare a b
    let equal (a, _) (b, _) = Writes.equal a b
    let hash (x, _) = Writes.hash x
  end in
  let module Deps = Graph.Imperative.Digraph.Concrete (Vertex) in
  let module Sccs = Graph.Components.Make (Deps) in
  fun e ->
    let g = Deps.create () in
    Effect.iter_writes (fun w r -> Deps.add_vertex g (w, r)) e;
    Deps.iter_vertex
      (fun (w_from, _ as v_from) ->
        if w_from <> Writes.Result then
          Deps.iter_vertex
            (fun (_, r_to as v_to) ->
               if not (Vertex.equal v_from v_to) then
                 may
                   (fun (Reads.Some (kind, r)) -> if Reads.mem kind r r_to then Deps.add_edge g v_from v_to)
                   (Reads.of_writes w_from))

          g)
      g;
    let sccs = Sccs.scc_list g in
    List.iter
      (fun scc ->
         let scc' = scc @ [List.hd scc] in
         let rec round =
           function
           | [] -> assert false
           | (_, from) :: _ as h ->
             function
             | [] -> ()
             | (_, r_c as c) :: t ->
               Reads.import ~from r_c;
               round (c :: h) t
         in
         round [List.hd scc'] (List.tl scc');
         List.iter (fun (_, from as v) -> Deps.iter_succ (fun (_, r) -> Reads.import ~from r) g v) scc)
      sccs

class effect_collector fl file_info def =
  let eff = File_info.get file_info fl def in
  object
    method finish = add_transitive_closure eff

    val all_reads = Reads.create (Flag.create ())
    val curr_reads = Stack.create ()

    inherit frama_c_inplace

    method! vstmt =
      let collect_reads acc =
        Reads.import ~from:all_reads acc;
        Stack.iter (fun from -> Reads.import ~from acc) curr_reads
      in
      let add_edges =
        let h_lv = Reads.create (Flag.create ()) and h_from = Reads.create (Flag.create ()) in
        fun ?lv ~from ->
          Reads.clear h_lv;
          Reads.clear h_from;
          from h_from;
          collect_reads h_from;
          match lv with
          | Some lv ->
            lv h_lv;
            Reads.iter_global (fun r -> Effect.add_reads (Writes.Global r) h_from eff) h_lv;
            Reads.iter_poly (fun v -> Effect.add_reads (Writes.Poly v) h_from eff) h_lv;
            Reads.iter_local (fun v -> Effect.add_reads (Writes.Local v) h_from eff) h_lv
          | None -> Effect.add_reads Writes.Result h_from eff
      in
      let add_depends ~reach_target =
        if reach_target then Effect.set_is_target eff;
        if Effect.is_target eff then collect_reads (Effect.depends eff)
      in
      let handle_call lvo fundec params =
        let eff' = File_info.get file_info fl fundec in
        if Effect.is_target eff' then begin
          add_depends ~reach_target:true;
          project_reads ~fundec ~params (Effect.depends eff') (Effect.depends eff)
        end;
        let lvo = may_map add_from_lval lvo ~dft:(const ()) in
        let project_reads = project_reads ~fundec ~params in
        Effect.iter_writes
          (fun w from ->
             let lv = may_map (fun (Reads.Some (k, x)) r -> Reads.add k x r) ~dft:lvo (Reads.of_writes w) in
             add_edges ~lv ~from:(project_reads from))
        eff'
      in
      let handle_all_reads =
        let from = Reads.create (Flag.create ()) in
        fun () ->
          Reads.clear from;
          collect_reads from;
          add_depends ~reach_target:false;
          Effect.iter_writes (fun _ r -> Reads.import ~from r) eff;
          Reads.import ~from all_reads
      in
      let continue_under vs =
        Stack.push vs curr_reads;
        DoChildrenPost (fun s -> ignore @@ Stack.pop curr_reads; s)
      in
      fun s ->
        match s.skind with
        | Instr (Set (lv, e, _)) ->
          add_edges ~lv:(add_from_lval lv) ~from:(add_from_expr e);
          SkipChildren
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _)) when Options.Target_functions.mem vi.vname ->
          add_depends ~reach_target:true;
          SkipChildren
        | Instr (Call (lvo, { enode = Lval (Var vi, NoOffset) }, _, loc)) when Options.Alloc_functions.mem vi.vname ->
          begin match lvo with
          | Some lv ->
            let lv = Mem (new_exp ~loc @@ Lval lv), NoOffset in
            add_edges ~lv:(add_from_lval lv) ~from:(const ())
          | None -> ()
          end;
          SkipChildren
        | Instr (Call (lvo, { enode = Lval (Var vi, NoOffset) }, params, _)) when isFunctionType vi.vtype ->
          begin try
           handle_call lvo (Kernel_function.get_definition (Globals.Functions.find_by_name vi.vname)) params;
          with
          | Kernel_function.No_Definition -> ()
          end;
          SkipChildren
        (* call by pointer *)
        | Instr (Call (lvo, _, params, _)) ->
          List.iter
            (fun kf -> handle_call lvo (Kernel_function.get_definition kf) params)
            (filter_matching_kfs params);
          SkipChildren
        | Instr (Asm _ | Skip _ | Code_annot _) ->
          SkipChildren
        | Return (eo, _) ->
          handle_all_reads ();
          add_edges
            ?lv:None
            ~from:(may_map add_from_expr eo ~dft:(const ()));
          SkipChildren
        | Goto _ | Break _ | Continue _ ->
          handle_all_reads ();
          SkipChildren
        | If (e, _, _, _) | Switch (e, _, _, _) ->
          continue_under (let r = Reads.create (Flag.create ()) in add_from_expr e r; r)
        | Loop _ | Block _ | UnspecifiedSequence _ -> DoChildren
        | Throw _ | TryCatch _ | TryFinally _ | TryExcept _  ->
          failwith "Unsupported features: exceptions and their handling"
  end

let collect_effects =
  visit_until_convergence
    ~order:`topological
    (new effect_collector)

class marker fl file_info def =
  let eff = File_info.get file_info fl def in
  object(self)
    method add_stmt s = Effect.add_stmt_req s eff
    method add_body f = Effect.add_body_req f eff
    method finish = ()

    inherit frama_c_inplace
    method! vstmt =
      let handle_call ~s lvo fundec params =
        let mark () = self#add_body fundec; self#add_stmt s in
        let eff' = File_info.get file_info fl fundec in
        (* first project writes *)
        let writes = Effect.shallow_copy_writes (Flag.create ()) eff' in
        H_write.filter_map_inplace
          ~check:false
          (fun w reads ->
             match w with
             | Writes.Global r ->
               if Reads.mem Reads.Global r (Effect.depends eff) then Some reads else None
             | Writes.Result when has_some lvo ->
               let r = Reads.create (Flag.create ()) in
               may (fun lv -> add_from_lval lv r) lvo;
               if Reads.intersects (Effect.depends eff) r then Some reads
               else None
             | Writes.Local _
             | Writes.Poly _
             | Writes.Result -> None)
          writes;
        if Effect.is_target eff' then mark ();
        if H_write.length writes > 0 then begin
          (* propagate projected writes to callee depends *)
          H_write.iter
            (const' @@
              function
              | Writes.Global r -> Effect.add_global_dep r eff'
              | Writes.Result -> Effect.add_result_dep eff'
              | Writes.Local _
              | Writes.Poly _ -> assert false)
            writes;
          (* project reads and propagate them to our (caller) depends *)
          let reads = Reads.create (Flag.create ()) in
          H_write.iter (fun _ from -> Reads.import ~from reads) writes;
          project_reads ~fundec ~params reads (Effect.depends eff);
          mark ()
        end
      in
      let handle_assignment =
        let r = Reads.create (Flag.create ()) in
        fun ~s ~lv ~from ->
          Reads.clear r;
          add_from_lval lv r;
        if Reads.intersects (Effect.depends eff) r then begin
          from (Effect.depends eff);
          self#add_stmt s
        end;
        SkipChildren
      in
      let handle_stmt_list ~from ~s stmts =
        if List.exists (fun s -> Effect.has_stmt_req s eff) stmts then begin
          self#add_stmt s;
          from (Effect.depends eff)
        end
      in
      fun s ->
        match s.skind with
        | Instr (Set (lv, e, _)) ->
          handle_assignment ~s ~lv ~from:(add_from_expr e)
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _)) when Options.Target_functions.mem vi.vname ->
          self#add_stmt s;
          begin try
            self#add_body (Kernel_function.get_definition @@ Globals.Functions.find_by_name vi.vname)
          with
          | Kernel_function.No_Definition -> ()
          end;
          SkipChildren
        | Instr (Call (lvo, { enode = Lval (Var vi, NoOffset) }, _, loc)) when Options.Alloc_functions.mem vi.vname ->
          let d = Globals.Functions.find_by_name vi.vname in
          if Kernel_function.is_definition d then self#add_body (Kernel_function.get_definition d);
          begin match lvo with
          | Some lv ->
            let lv = Mem (new_exp ~loc @@ Lval lv), NoOffset in
            handle_assignment ~s ~lv ~from:(const ())
          | None -> SkipChildren
          end
        | Instr (Call (lvo, { enode = Lval (Var vi, NoOffset) }, params, _)) when isFunctionType vi.vtype ->
          begin try
            handle_call ~s lvo (Kernel_function.get_definition (Globals.Functions.find_by_name vi.vname)) params
          with
          | Kernel_function.No_Definition -> self#add_stmt s
          end;
          SkipChildren
        (* call by pointer *)
        | Instr (Call (lvo, _, params, _)) ->
          List.iter
            (fun kf -> handle_call ~s lvo (Kernel_function.get_definition kf) params)
            (filter_matching_kfs params);
          SkipChildren
        | Instr (Asm _ | Skip _ | Code_annot _) ->
          SkipChildren
        | Return (eo, _) ->
          self#add_stmt s;
          may (fun e -> if Effect.has_result_dep eff then add_from_expr e (Effect.depends eff)) eo;
          SkipChildren
        | Goto _ | Break _ | Continue _ ->
          self#add_stmt s;
          SkipChildren
        | If (e, block1, block2, _) ->
          DoChildrenPost (fun s -> handle_stmt_list ~from:(add_from_expr e) ~s @@ block1.bstmts @ block2.bstmts; s)
        | Switch (e, block, _, _) ->
          DoChildrenPost (fun s -> handle_stmt_list ~from:(add_from_expr e) ~s block.bstmts; s)
        | Loop (_, block, _, _, _)
        | Block block ->
          DoChildrenPost (fun s -> handle_stmt_list ~from:ignore ~s block.bstmts; s)
        | UnspecifiedSequence l ->
          DoChildrenPost (fun s -> handle_stmt_list ~from:ignore ~s @@ List.map (fun (s, _ ,_ ,_, _) -> s) l; s)
        | Throw _ | TryCatch _ | TryFinally _ | TryExcept _  ->
          failwith "Unsupported features: exceptions and their handling"
  end

let mark =
  visit_until_convergence
    ~order:`reversed
    (new marker)

class sweeper fl file_info =
  let required_bodies =
    let result = Fundec.Hashtbl.create 256 in
    Fundec.Hashtbl.iter
      (fun _ e -> Effect.iter_body_reqs (fun f -> Fundec.Hashtbl.replace result f ()) e)
      file_info;
    List.iter
      (fun kf ->
         try Fundec.Hashtbl.replace result (Kernel_function.get_definition kf) ()
         with Kernel_function.No_Definition -> ())
      (get_addressed_kfs ());
    let main = Globals.Functions.find_by_name @@ Kernel.MainFunction.get () in
    if Kernel_function.is_definition main then Fundec.Hashtbl.add result (Kernel_function.get_definition main) ();
    result
  in
  object
    val mutable eff = Effect.create (Flag.create ())

    inherit frama_c_inplace
    method! vfunc f =
      eff <- File_info.get file_info fl f;
      DoChildren
    method! vstmt_aux s =
      if not (Effect.has_stmt_req s eff) then
        if Options.Use_ghosts.is_set () then begin
          s.ghost <- true;
          DoChildren
        end else begin
          let rec collect_labels acc s =
            let acc =
              List.fold_right Label.Set.add (List.filter (function Label _ -> true | _ -> false) s.labels) acc
            in
            match s.skind with
            | If (_, block1, block2, _) ->
              List.fold_left collect_labels acc @@ block1.bstmts @ block2.bstmts
            | Switch (_, block, _, _)
            | Loop (_, block, _, _, _)
            | Block block ->
              List.fold_left collect_labels acc block.bstmts
            | UnspecifiedSequence l ->
              List.fold_left collect_labels acc @@ List.map (fun (s, _ ,_ ,_, _) -> s) l
            | _ -> acc
          in
          let collect_labels s = Label.Set.(elements @@ collect_labels (Label.Set.of_list s.labels) s) in
          ChangeTo { s with skind = Instr (Skip (Stmt.loc s)); labels = collect_labels s }
        end
      else
        DoChildren

    method! vglob_aux  =
      function
      | GFun (f, _) when not (Fundec.Hashtbl.mem required_bodies f) ->
        ChangeTo []
      | _ -> DoChildren
  end

let sweep fl file_info = visitFramacFile (new sweeper fl file_info) @@ Ast.get ()

let condensate () =
  let module Cg = Callgraph.Cg in
  Console.debug "...computing callgraph...";
  let cg = Cg.get () in
  Console.debug "..syntactic slicing...";
  let module H = Kernel_function.Hashtbl in
  let module Traverse = Graph.Traverse.Bfs (Cg.G) in
  let h = H.create 512 in
  let main = Globals.Functions.find_by_name @@ Kernel.MainFunction.get () in
  Traverse.iter_component (fun v -> H.replace h v ()) cg main;
  let module G = Graph.Imperative.Digraph.Concrete (Kernel_function) in
  let module Components = Graph.Components.Make (G) in
  let g = G.create ~size:(H.length h) () in
  Cg.G.iter_edges (fun f t -> if H.mem h f && H.mem h t then G.add_edge g f t) cg;
  Console.debug "...sccs...";
  let r = Components.scc_list g in
  Console.debug "...finished sccs...";
  r

let slice () =
  let sccs = condensate () in
  let fi = File_info.create () in
  collect_effects fi sccs;
  mark fi sccs;
  sweep (Flag.create ()) fi
