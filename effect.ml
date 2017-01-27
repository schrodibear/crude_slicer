(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Cil
open Cil_types
open Cil_printer
open Cil_datatype

open Format
open Extlib
open Common

module type Criterion = sig
  type t
  val is_ok : t -> bool
end

module Memory_field : sig
  type t = private fieldinfo

  include Criterion with type t := t
  val of_fieldinfo : fieldinfo -> t option
  val of_fieldinfo_exn : fieldinfo -> t
  include Hashed_ordered_printable with type t := t
end = struct
  type t = fieldinfo

  let is_ok fi = fi.fcomp.cstruct && isArithmeticOrPointerType fi.ftype

  let of_fieldinfo fi = if is_ok fi then Some fi else None

  let of_fieldinfo_exn fi =
    if is_ok fi then fi
    else
      Console.fatal
        "Memory_field.of_fieldinfo_exn: not ok: %s.%s : %a"
        (compFullName fi.fcomp) fi.fname pp_typ fi.ftype

  include (Fieldinfo : Hashed_ordered with type t := t)
  let pp fmt fi = fprintf fmt "%s" fi.fname
end

module type Representant = sig
  module Kind : sig
    type t =
      | Global
      | Poly of string
      | Local of string
      | Dummy

    include Printable with type t := t
  end

  type t =
    {
      name : string;
      typ  : typ;
      kind : Kind.t
    }

  include Hashed_ordered_printable with type t := t
end

module type Unifiable = sig
  type t
  type repr
  val repr : t -> repr
end

module type Memory = sig
  type t
  type u
  val mk : ?fi: fieldinfo -> u -> t
  include Hashed_ordered_printable with type t := t
end

module Make_memory (R : Representant) (U : Unifiable with type repr = R.t) (C : Criterion with type t := R.t)
  : Memory with type u = U.t = struct
  type t = R.t * Memory_field.t option
  type u = U.t

  let mk ?fi u =
    let r = U.repr u in
    if C.is_ok r then
      Console.fatal "Memory.mk: wrong region (not OK): %s : %a vs. %a" r.R.name pp_typ r.R.typ R.Kind.pp r.R.kind;
    if isArithmeticOrPointerType r.R.typ then
      match fi with
      | None -> r, None
      | Some fi ->
        Console.fatal
          "Memory.mk: fields can't be specified for primitive regions: %s.%s for %s"
          fi.fcomp.cname fi.fname (U.repr u).R.name
    else
      match unrollTypeDeep r.R.typ, fi with
      | TComp (ci, _ ,_), Some fi when Compinfo.equal ci fi.fcomp ->
        r, Some (Memory_field.of_fieldinfo_exn fi)
      | _, None ->
        Console.fatal "Memory.mk: improper region (with no field): %s : %a" r.R.name pp_typ r.R.typ
      | _, Some fi ->
        Console.fatal
          "Memory.mk: improper combination of region and field: %s : %a and %s.%s : %a"
          r.R.name pp_typ r.R.typ (compFullName fi.fcomp) fi.fname pp_typ fi.ftype

  let equal (r1, fo1) (r2, fo2) = R.equal r1 r2 && opt_equal Memory_field.equal fo1 fo2

  let hash (r, fo) = 997 * R.hash r + opt_hash Memory_field.hash fo

  let compare (r1, fo1) (r2, fo2) =
    let r = R.compare r1 r2 in
    if r <> 0 then r else opt_compare Memory_field.compare fo1 fo2

  let pp fmttr =
    let pp fmt = fprintf fmttr fmt in
    function
    | r, Some fi -> pp "%a->%a" R.pp r Memory_field.pp fi
    | r, None    -> pp "*%a" R.pp r
end

module Make_var (C : Criterion with type t := varinfo) : sig
  type t = private varinfo

  include Criterion with type t := t
  val of_varinfo : varinfo -> t option
  val of_varinfo_exn : varinfo -> t
  include Hashed_ordered_printable with type t := t
end = struct
  type t = varinfo

  include C

  let of_varinfo vi = if C.is_ok vi then Some vi else None

  let of_varinfo_exn vi =
    if C.is_ok vi then vi
    else invalid_arg "Formal_var.of_varinfo_exn"

  include (Varinfo : Hashed_ordered with type t := t)
  let pp = pp_varinfo
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
  val sub : t -> from:t -> unit
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

module Make_reporting_bithashset (M : Hashed_printable) () : Reporting_bithashset with type elt = M.t =
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
  let sub (s, _) ~from:(from, f) =
    if Bv.inters from s then Flag.report f;
    Bv.sub_from ~from s
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

module Make_reporting_hashmap (M_key : Hashed_printable) (S : Set) : sig
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

module Global_var = Make_var (struct let is_ok vi = isArithmeticOrPointerType vi.vtype && vi.vglob end)

module Formal_var = Make_var (struct let is_ok vi = isArithmeticOrPointerType vi.vtype && vi.vformal end)

module Local_var =
  Make_var (struct let is_ok vi = isArithmeticOrPointerType vi.vtype && not vi.vglob && not vi.vformal end)

module type Memories = sig
  type u
  module Global_mem : Memory with type u := u
  module Poly_mem : Memory with type u := u
  module Local_mem : Memory with type u := u
  module H_global_mem : Reporting_bithashset with type elt := Global_mem.t
  module H_poly_mem : functor () -> Reporting_bithashset with type elt := Poly_mem.t
  module H_local_mem : functor () -> Reporting_bithashset with type elt := Local_mem.t
end

module Make_memories (R : Representant) (U : Unifiable with type repr = R.t) () = struct
  type u = U.t
  module Global_mem = Make_memory (R) (U) (struct let is_ok r = r.R.kind = R.Kind.Global end)
  module Poly_mem =
    Make_memory (R) (U) (struct let is_ok = function R.{ kind = Kind.Poly _; _ } -> true | _ -> false end)
  module Local_mem =
    Make_memory (R) (U) (struct let is_ok = function R.{ kind = Kind.Local _; _ } -> true | _ -> false end)
  module H_global_mem = Make_reporting_bithashset (Global_mem) ()
  module H_poly_mem = Make_reporting_bithashset (Poly_mem)
  module H_local_mem = Make_reporting_bithashset (Local_mem)
end

module type Writes = sig
  module Memories : Memories

  open Memories
  type t =
    | Global_var of Global_var.t
    | Poly_var of Formal_var.t
    | Local_var of Local_var.t
    | Global_mem of Global_mem.t
    | Poly_mem of Poly_mem.t
    | Local_mem of Local_mem.t
    | Result

  include Hashed_ordered_printable with type t := t
end

module Make_writes (M : Memories) : Writes with module Memories = M = struct
  module Memories = M

  open M

  type t =
    | Global_var of Global_var.t
    | Poly_var of Formal_var.t
    | Local_var of Local_var.t
    | Global_mem of Global_mem.t
    | Poly_mem of Poly_mem.t
    | Local_mem of Local_mem.t
    | Result

  let compare w1 w2 =
    match w1, w2 with
    | Global_var v1, Global_var v2 -> Global_var.compare v1 v2
    | Global_var _, _ -> -1
    | Poly_var _, Global_var _ -> 1
    | Poly_var v1, Poly_var v2 -> Formal_var.compare v1 v2
    | Poly_var _, _ -> -1
    | Local_var _, (Global_var _ | Poly_var _) -> 1
    | Local_var v1, Local_var v2 -> Local_var.compare v1 v2
    | Local_var _, _ -> -1
    | Global_mem _, (Global_var _ | Poly_var _ | Local_var _) -> 1
    | Global_mem m1, Global_mem m2 -> Global_mem.compare m1 m2
    | Global_mem _, _ -> -1
    | Poly_mem _, (Global_var _ | Poly_var _ | Local_var _ | Global_mem _) -> 1
    | Poly_mem m1, Poly_mem m2 -> Poly_mem.compare m1 m2
    | Poly_mem _, _ -> -1
    | Local_mem _, (Global_var _ | Poly_var _ | Local_var _ | Global_mem _ | Poly_mem _) -> 1
    | Local_mem m1, Local_mem m2 -> Local_mem.compare m1 m2
    | Local_mem _, _ -> -1
    | Result, Result -> 0
    | Result, _ -> 1

  let equal w1 w2 =
    match w1, w2 with
    | Global_var v1, Global_var v2 -> Global_var.equal v1 v2
    | Poly_var v1, Poly_var v2 -> Formal_var.equal v1 v2
    | Local_var v1, Local_var v2 -> Local_var.equal v1 v2
    | Global_mem m1, Global_mem m2 -> Global_mem.equal m1 m2
    | Poly_mem m1, Poly_mem m2 -> Poly_mem.equal m1 m2
    | Local_mem m1, Local_mem m2 -> Local_mem.equal m1 m2
    | Result, Result -> true
    | _ -> false

  let hash =
    function
    | Global_var v -> 7 * Global_var.hash v
    | Poly_var v -> 7 * Formal_var.hash v + 1
    | Local_var v -> 7 * Local_var.hash v + 2
    | Global_mem m -> 7 * Global_mem.hash m + 3
    | Poly_mem m -> 7 * Poly_mem.hash m + 4
    | Local_mem m -> 7 * Local_mem.hash m + 5
    | Result -> 6

  let pp fmttr =
    let pp fmt = fprintf fmttr fmt in
    function
    | Global_var v -> pp "%a" Global_var.pp v
    | Poly_var v -> pp "'%a" Formal_var.pp v
    | Local_var v -> pp "~%a" Local_var.pp v
    | Global_mem m -> pp "%a" Global_mem.pp m
    | Poly_mem m -> pp "'%a" Poly_mem.pp m
    | Local_mem m -> pp "~%a" Local_mem.pp m
    | Result -> pp "!R!"
end

module H_global_var = Make_reporting_bithashset (Global_var) ()
module H_formal_var = Make_reporting_bithashset (Formal_var)
module H_local_var = Make_reporting_bithashset (Local_var)

module Reads (W : Writes) () : sig
  type t

  open W.Memories

  type _ kind =
    | Global_var : Global_var.t kind
    | Poly_var : Formal_var.t kind
    | Local_var : Local_var.t kind
    | Global_mem : Global_mem.t kind
    | Poly_mem : Poly_mem.t kind
    | Local_mem : Local_mem.t kind

  type some = Some : 'a kind * 'a -> some

  val of_writes : W.t -> some option

  val create : Flag.t -> t
  val clear : t -> unit
  val import : from:t -> t -> unit
  val add_global_var : Global_var.t -> t -> unit
  val add_poly_var : Formal_var.t -> t -> unit
  val add_local_mem : Local_var.t -> t -> unit
  val add_global_mem : Global_mem.t -> t -> unit
  val add_poly_mem : Poly_mem.t -> t -> unit
  val add_local_mem : Local_mem.t -> t -> unit
  val add : 'a kind -> 'a -> t -> unit
  val sub : t -> from:t -> unit
  val mem : 'a kind -> 'a -> t -> bool
  val intersects : t -> t -> bool
  val flag : t -> Flag.t
  val copy : Flag.t -> t -> t

  val iter_global_vars : (Global_var.t -> unit) -> t -> unit
  val iter_poly_vars : (Formal_var.t -> unit) -> t -> unit
  val iter_local_vars : (Local_var.t -> unit) -> t -> unit
  val iter_global_mems : (Global_mem.t -> unit) -> t -> unit
  val iter_poly_mems : (Poly_mem.t -> unit) -> t -> unit
  val iter_lcoal_mems : (Local_mem.t -> unit) -> t -> unit
  val is_empty : t -> bool
  val is_singleton : t -> bool
  val has_vars : t -> bool
  val length : t -> int

  val pp : formatter -> t -> unit
end = struct
  open W.Memories

  module H_formal_var = H_formal_var ()
  module H_local_var = H_local_var ()
  module H_poly_mem = H_poly_mem ()
  module H_local_mem = H_local_mem ()

  type t =
    {
      global_vars : H_global_var.t;
      poly_vars   : H_formal_var.t;
      local_vars  : H_local_var.t;
      global_mems : H_global_mem.t;
      poly_mems   : H_poly_mem.t;
      local_mems  : H_local_mem.t
    }

  type _ kind =
    | Global_var : Global_var.t kind
    | Poly_var : Formal_var.t kind
    | Local_var : Local_var.t kind
    | Global_mem : Global_mem.t kind
    | Poly_mem : Poly_mem.t kind
    | Local_mem : Local_mem.t kind

  type some = Some : 'a kind * 'a -> some

  let of_writes : _ -> some option =
    function
    | W.Global_var v -> Some (Some (Global_var, v))
    | W.Local_var v -> Some (Some (Local_var, v))
    | W.Poly_var v -> Some (Some (Poly_var, v))
    | W.Global_mem m -> Some (Some (Global_mem, m))
    | W.Local_mem m -> Some (Some (Local_mem, m))
    | W.Poly_mem m -> Some (Some (Poly_mem, m))
    | W.Result -> None

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
  let sub r ~from =
    H_region.sub r.global ~from:from.global;
    H_local_var.sub r.local ~from:from.local;
    H_formal_var.sub r.poly ~from:from.poly
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
  let is_empty r = H_region.is_empty r.global && H_formal_var.is_empty r.poly && H_local_var.is_empty r.local
  let is_singleton r =
    H_region.length r.global = 1 && H_formal_var.is_empty r.poly && H_local_var.is_empty r.local ||
    H_formal_var.length r.poly = 1 && H_region.is_empty r.global && H_local_var.is_empty r.local ||
    H_local_var.length r.local = 1 && H_formal_var.is_empty r.poly && H_region.is_empty r.global
  let length r = H_region.length r.global + H_formal_var.length r.poly + H_local_var.length r.local
  let has_vars r = not (H_formal_var.is_empty r.poly && H_local_var.is_empty r.local)

  let pp fmt r =
    fprintf fmt "  @[gl:%a,@ @,pol:%a,@ @,loc:%a@]" H_region.pp r.global H_formal_var.pp r.poly H_local_var.pp r.local
end

module Fundec = struct include Fundec let pp = pretty end
module Stmt = struct include Stmt let pp = pretty end

module H_fundec = Make_reporting_bithashset (Fundec)
module H_stmt = Make_reporting_bithashset (Stmt)

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

module Void_ptr_var = Make_var (struct let is_ok vi = isVoidPtrType vi.vtype end)

module H_void_ptr_var = Make_reporting_bithashset (Void_ptr_var)

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
  val add_tracking_var : Void_ptr_var.t -> t -> unit
  val shallow_copy_writes : Flag.t -> t -> H_write.t
  val copy : Flag.t -> t -> t

  val iter_writes : (Writes.t -> Reads.t -> unit) -> t -> unit
  val is_target : t -> bool
  val is_tracking_var : Void_ptr_var.t -> t -> bool
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
              tracking   : H_void_ptr_var.t;
      mutable is_target  : bool;
              depends    : Reads.t;
      mutable result_dep : bool;
              requires   : Requires.t;
              flag       : Flag.t;
    }

  let create f =
    {
      writes = H_write.create f;
      tracking = H_void_ptr_var.create f;
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
  let add_tracking_var v e = H_void_ptr_var.add v e.tracking
  let shallow_copy_writes f e = H_write.shallow_copy f e.writes
  let copy f e =
    {
      writes = H_write.copy f e.writes;
      tracking = H_void_ptr_var.copy f e.tracking;
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
  let is_tracking_var v e = H_void_ptr_var.mem v e.tracking
  let iter_body_reqs f e = Requires.iter_bodies f e.requires
  let iter_stmt_reqs f e = Requires.iter_stmts f e.requires
  let flag e = e.flag

  let pp fmt e =
    fprintf fmt "@[w:@;@[%a@];@.track:%a;@.tar:%B;@.deps:@;%a;@.RD:%B@]"
      H_write.pp e.writes H_void_ptr_var.pp e.tracking e.is_target Reads.pp e.depends e.result_dep
end
