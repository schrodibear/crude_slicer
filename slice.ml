(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016                                                    *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "-4-9-44"]

open Extlib

open Cil_types
open Cil_datatype
open Cil
open Visitor

module Console = Options

let (%>) f g x = f (g x)

let const f _x = f
let const' f x _y = f x

let opt_iter f o = opt_fold (const' f) o ()

module Primitive_type : sig
  type t = private typ

  val of_typ : typ -> t option
  val of_typ_exn : typ -> t
end = struct
  type t = typ

  let of_typ t =
    let t = unrollTypeDeep t in
    if isArithmeticOrPointerType t then Some t
    else None

  let of_typ_exn t =
    let t = unrollTypeDeep t in
    if isArithmeticOrPointerType t then t
    else invalid_arg "Primitive_type.of_typ_exn"
end

module Make_var (C : sig val is_ok : varinfo -> bool end) : sig
  type t = private varinfo

  val of_varinfo : varinfo -> t option
  val of_varinfo_exn : varinfo -> t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end = struct
  type t = varinfo

  let of_varinfo vi = if C.is_ok vi then Some vi else None

  let of_varinfo_exn vi =
    if C.is_ok vi then vi
    else invalid_arg "Formal_var.of_varinfo_exn"

  let compare v1 v2 = Varinfo.compare (v1 :> varinfo) (v2 :> varinfo)
  let equal v1 v2 = Varinfo.equal (v1 :> varinfo) (v2 :> varinfo)
  let hash v = Varinfo.hash (v :> varinfo)
end

module Global_var = Make_var (struct let is_ok vi = vi.vglob end)

module Struct_field : sig
  type t = private fieldinfo

  val of_fieldinfo : fieldinfo -> t option
  val of_fieldinfo_exn : fieldinfo -> t
end = struct
  type t = fieldinfo

  let of_fieldinfo fi = if fi.fcomp.cstruct then Some fi else None

  let of_fieldinfo_exn fi =
    if fi.fcomp.cstruct then fi
    else invalid_arg "Struct_field.of_fieldinfo_exn"
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

module type Reporting_hashset = sig
  type elt
  type t
  val create : Flag.t -> t
  val clear : t -> unit
  val copy :  Flag.t -> t -> t
  val add : t -> elt -> unit
  val import : from:t -> t -> unit
  val remove : t -> elt -> unit
  val mem : t -> elt -> bool
  val iter : (elt -> unit) -> t -> unit
  val filter_inplace : (elt -> bool) -> t -> unit
  val fold : (elt -> 'b -> 'b) -> t -> 'b -> 'b
  val length : t -> int
  val flag : t -> Flag.t
  val stats : t -> Hashtbl.statistics
end

module Make_reporting_hashset (M : Hashtbl.HashedType) : Reporting_hashset with type elt = M.t =
struct
  type elt = M.t
  module H = Hashtbl.Make(M)
  open H
  type nonrec t = unit t * Flag.t
  let create f =
    H.create 32, f
  let clear (h, f) =
    if H.length h > 0 then Flag.report f;
    H.clear h
  let copy f (h, _) = H.copy h, f
  let add (h, f) e =
    if not (H.mem h e) then Flag.report f;
    H.replace h e ()
  let import ~from:(from, _) (h, f) =
    H.iter (fun e () -> if not (H.mem h e) then Flag.report f; H.replace h e ()) from
  let remove (h, f) e =
    if H.mem h e then Flag.report f;
    H.remove h e
  let mem (h, _) e = H.mem h e
  let iter f (h, _) =
    H.iter (fun k () -> f k) h
  let filter_inplace f (h, fl) =
    H.filter_map_inplace (fun e () -> let r = f e in if not r then (Flag.report fl; None) else Some ()) h
  let fold f (h, _) x =
    H.fold (fun e () x -> f e x) h x
  let length (h, _) = H.length h
  let flag (_, f) = f
  let stats (h, _) = H.stats h
end

module type Set = sig
  type t
  type 'a kind
  val create : Flag.t -> t
  val add : t -> 'a kind -> 'a -> unit
  val import : from:t -> t -> unit
  val flag : t -> Flag.t
  val copy : Flag.t -> t -> t
end

module Make_reporting_hashmap (M_key : Hashtbl.HashedType) (S : Set) : sig
  type key = M_key.t
  type set = S.t
  type 'a kind = 'a S.kind
  type t
  val create : Flag.t -> t
  val clear : t -> unit
  val copy :  Flag.t -> t -> t
  val shallow_copy :  Flag.t -> t -> t
  val add : t -> key -> 'a kind -> 'a -> unit
  val import : from:t -> t -> unit
  val remove : t -> key -> unit
  val mem : t -> key -> bool
  val iter : (key -> set -> unit) -> t -> unit
  exception Different_flag
  val filter_map_inplace : (key -> set -> set option) -> t -> unit
  val find : t -> key -> set
  val fold : (key -> set -> 'b -> 'b) -> t -> 'b -> 'b
  val length : t -> int
  val flag : t -> Flag.t
  val stats : t -> Hashtbl.statistics
end = struct
  type key = M_key.t
  type set = S.t
  type 'a kind = 'a S.kind
  module H = Hashtbl.Make(M_key)
  open H
  type nonrec t = S.t t * Flag.t
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
  let add (h, f) k kind e  =
    if not (H.mem h k) then (Flag.report f; H.replace h k (S.create f));
    S.add (H.find h k) kind e
  let import ~from:(from, _) (h, f) =
    H.iter
      (fun k from ->
         if not (H.mem h k) then (Flag.report f; H.replace h k (S.create f));
         S.import ~from (H.find h k))
      from
  let remove (h, f) k =
    if H.mem h k then Flag.report f;
    H.remove h k
  let mem (h, _) k = H.mem h k
  let iter f (h, _) =
    H.iter f h
  let find (h, f) k =
    try H.find h k
    with Not_found ->
      let r = S.create f in
      Flag.report f;
      H.replace h k r;
      r
  exception Different_flag
  let filter_map_inplace f (h, fl) =
    H.filter_map_inplace
      (fun e set ->
         let r = f e set in
         match r with
         | None -> Flag.report fl; None
         | Some s -> if S.flag s != fl then raise Different_flag else (if s != set then Flag.report fl; r))
      h
  let fold f (h, _) x =
    H.fold f h x
  let length (h, _) = H.length h
  let flag (_, f) = f
  let stats (h, _) = H.stats h
end

module H_region = Make_reporting_hashset (Region)

module Formal_var = Make_var (struct let is_ok vi = vi.vformal end)

module H_formal_var = Make_reporting_hashset (Formal_var)

module Reads = struct
  type t =
    {
      global : H_region.t;
      poly   : H_formal_var.t
    }

  type _ kind =
    | Global : Region.t kind
    | Poly : Formal_var.t kind

  let create f = { global = H_region.create f; poly = H_formal_var.create f }
  let import ~from r =
    H_region.import ~from:from.global r.global;
    H_formal_var.import ~from:from.poly r.poly
  let add_global g r = H_region.add r.global g
  let add_poly p r = H_formal_var.add r.poly p
  let add : type a. _ -> a kind -> a -> _ = fun r ->
    function
    | Global -> H_region.add r.global
    | Poly -> H_formal_var.add r.poly
  let flag r = H_region.flag r.global
  let copy f r = { global = H_region.copy f r.global; poly = H_formal_var.copy f r.poly }
end

module H_fundec = Make_reporting_hashset (Fundec)
module H_stmt = Make_reporting_hashset (Stmt)

module Requires = struct
  type t =
    {
      bodies : H_fundec.t;
      stmts  : H_stmt.t
    }

  let create f = { bodies = H_fundec.create f; stmts = H_stmt.create f }
  let import ~from r =
    H_fundec.import ~from:from.bodies r.bodies;
    H_stmt.import ~from:from.stmts r.stmts
  let add_body f r = H_fundec.add r.bodies f
  let add_stmt s r = H_stmt.add r.stmts s
  let copy f r = { bodies = H_fundec.copy f r.bodies; stmts = H_stmt.copy f r.stmts }
end

module Writes = struct
  type t =
    | Region of Region.t
    | Result
  let compare w1 w2 =
    match w1, w2 with
    | Region r1, Region r2 -> Region.compare r1 r2
    | Region _, Result -> -1
    | Result, Result -> 0
    | Result, Region _ -> 1

  let equal w1 w2 =
    match w1, w2 with
    | Region r1, Region r2 -> Region.equal r1 r2
    | Result, Result -> true
    | Region _, Result
    | Result, Region _ -> false

  let hash =
    function
    | Region r -> 3 * Region.hash r
    | Result -> 1
end

module H_write = Make_reporting_hashmap (Writes) (Reads)

module Local_var = Make_var (struct let is_ok vi = not vi.vglob && not vi.vformal end)

module H_local_var = Make_reporting_hashset (Local_var)

module Effect = struct
  type t =
    {
              writes     : H_write.t;
      mutable is_target  : bool;
              depends    : Reads.t;
              local_deps : H_local_var.t;
      mutable result_dep : bool;
              requires   : Requires.t;
              flag       : Flag.t;
    }

  let create f =
    {
      writes = H_write.create f;
      is_target = false;
      depends = Reads.create f;
      local_deps = H_local_var.create f;
      result_dep = false;
      requires = Requires.create f;
      flag = f
    }

  let get_reads e w = H_write.find e.writes w
  let add_writes from e = H_write.import ~from e
  let add_global_read w r e = Reads.add_global r (get_reads e w)
  let add_poly_read w p e = Reads.add_poly p (get_reads e w)
  let add_global_dep d e = Reads.add_global d e.depends
  let add_poly_dep d e = Reads.add_poly d e.depends
  let add_depends d e = Reads.import ~from:d e.depends
  let add_local_dep d e = H_local_var.add e.local_deps d
  let add_local_deps from e = H_local_var.import ~from e.local_deps
  let add_result_dep e = if not e.result_dep then Flag.report e.flag; e.result_dep <- true
  let add_requires d e = Requires.import ~from:d e.requires
  let set_is_target e = if not e.is_target then Flag.report e.flag; e.is_target <- true

  let add_body_req f e = Requires.add_body f e.requires
  let add_stmt_req s e = Requires.add_stmt s e.requires
  let copy f e =
    {
      writes = H_write.copy f e.writes;
      is_target = e.is_target;
      depends = Reads.copy f e.depends;
      local_deps = H_local_var.copy f e.local_deps;
      result_dep = e.result_dep;
      requires = Requires.copy f e.requires;
      flag = f
    }
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
  else until_convergence f fi scc fl

let until_convergence f fi scc fl =
  Flag.clear fl;
  until_convergence f fi scc fl

class type ['a] frama_c_collector = object inherit frama_c_inplace method reflect : 'a end

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
                 v#reflect))
         fi
         scc
         fl)
    sccs

module Vertex = struct
  type t =
    | Region of Region.t
    | Result
    | Parameter of Formal_var.t
    | Local of Local_var.t

  let compare v1 v2 =
    match v1, v2 with
    | Region r1, Region r2 -> Region.compare r1 r2
    | Region _, _ -> -1
    | Result, Result -> 0
    | Result, Region _ -> 1
    | Result, _ -> -1
    | Parameter v1, Parameter v2 -> Varinfo.compare (v1 :> varinfo) (v2 :> varinfo)
    | Parameter _, Local _ -> -1
    | Parameter _, _ -> 1
    | Local v1, Local v2 -> Varinfo.compare (v1 :> varinfo) (v2 :> varinfo)
    | Local _, _ -> 1

  let hash =
    function
    | Region r -> 7 * Region.hash r
    | Result -> 1
    | Parameter v -> 7 * Varinfo.hash (v :> varinfo) + 3
    | Local v -> 7 * Varinfo.hash (v :> varinfo) + 5

  let equal v1 v2 =
    match v1, v2 with
    | Region r1, Region r2 -> Region.equal r1 r2
    | Result, Result -> true
    | Parameter v1, Parameter v2 -> Varinfo.equal (v1 :> varinfo) (v2 :> varinfo)
    | Local v1, Local v2 -> Varinfo.equal (v1 :> varinfo) (v2 :> varinfo)
    | _ -> false

  let of_writes =
    function
    | Writes.Region r -> Region r
    | Writes.Result -> Result

  let is_writable =
    function
    | Region _ | Result -> true
    | Parameter _ | Local _ -> false

  let to_writes =
    function
    | Region r -> Some (Writes.Region r)
    | Result -> Some Writes.Result
    | Parameter _ | Local _ -> None

  let to_writes_exn v =
    match to_writes v with
    | Some w -> w
    | None -> invalid_arg "Vertex.to_writes_exn"
end

module Deps = Graph.Imperative.Digraph.Concrete (Vertex)
module Oper = Graph.Oper.I (Deps)

module H_vertex = Hashtbl.Make (Vertex)

let rec add_vertices_of_lval acc =
  let add v = H_vertex.replace acc v () in
  let add_parameter vi = add @@ Vertex.Parameter (Formal_var.of_varinfo_exn vi) in
  let add_global vi = add @@ Vertex.Region (Region.Variable (Global_var.of_varinfo_exn vi)) in
  let add_local vi = add @@ Vertex.Local (Local_var.of_varinfo_exn vi) in
  let add_field fi = add @@ Vertex.Region (Region.Field (Struct_field.of_fieldinfo_exn fi)) in
  let add_type typ =
    let typ = typeDeepDropAllAttributes @@ unrollTypeDeep typ in
    add @@ Vertex.Region (Region.Type_approximation (Primitive_type.of_typ_exn typ))
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
        add_vertices_of_lval acc @@ addOffsetLval (Index (integer ~loc:Location.unknown 0, NoOffset)) lv
      | TFun _ as t                                                                     -> add_type (TPtr (t, []))
      | TComp (ci, _, _)                                                                ->
        List.iter (fun fi -> add_vertices_of_lval acc @@ addOffsetLval (Field (fi, NoOffset)) lv) ci.cfields
      | TBuiltin_va_list _                                                              -> add_type voidPtrType

class vertex_collector vertices =
  object
    inherit frama_c_inplace
    method! vlval lv =
      add_vertices_of_lval vertices lv;
      DoChildren
  end

let add_vertices_of_expr acc =
  let o = new vertex_collector acc in
  fun e -> ignore (visitFramacExpr (o :> frama_c_visitor) e)

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

let fail_on_result () = failwith "Should not happen: dependence on the return value"

let store_depends ?writes depends e =
  H_vertex.iter (function Vertex.Local lv -> const @@ Effect.add_local_dep lv e | _ -> const ()) depends;
  if H_vertex.mem depends Vertex.Result then Effect.add_result_dep e;
  H_vertex.iter
    (fun v () ->
       match v with
       | Vertex.Local _  ->
         opt_iter
           (fun writes ->
              Deps.iter_succ
                  (function
                     (* no need to recurse, because the transitive closure is already computed *)
                     | Vertex.Local _     -> ()
                     | Vertex.Parameter p -> Effect.add_poly_dep p e
                     | Vertex.Region r    -> Effect.add_global_dep r e
                     | Vertex.Result      -> fail_on_result ())
                   writes
                   v)
           writes
       | Vertex.Parameter p -> Effect.add_poly_dep p e
       | Vertex.Region r    -> Effect.add_global_dep r e
       | Vertex.Result      -> ())
    depends

let restore_depends eff =
  let open H_vertex in
  let acc = create 32 in
  H_region.iter (fun r -> replace acc (Vertex.Region r) ()) eff.Effect.depends.Reads.global;
  H_formal_var.iter (fun v -> replace acc (Vertex.Parameter v) ()) eff.Effect.depends.Reads.poly;
  H_local_var.iter (fun v -> replace acc (Vertex.Local v) ()) eff.Effect.local_deps;
  if eff.Effect.result_dep then replace acc (Vertex.Result) ();
  acc

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
  let params = List.(combine fundec.sformals @@ map (swap add_vertices_of_expr) params) in
  fun from acc ->
    H_formal_var.iter (fun fv -> (List.assoc (fv :> varinfo) params) acc) from.Reads.poly;
    H_region.iter (fun r -> H_vertex.replace acc (Vertex.Region r) ()) from.Reads.global

(* Imcomplete! Assumes no cycles present in the graph! But applicable in case we iterate until fixpoint anyway *)
let add_transitive_closure =
  let module H = Hashtbl.Make(Vertex) in
  let module Sccs = Graph.Components.Make (Deps) in
  fun g ->
    let n = Deps.nb_vertex g in
    let h = H.create n in
    let topo = List.flatten @@ Sccs.scc_list g in
    let sets = Array.init n (fun _ -> Bitset.create n) in
    ignore @@ List.fold_left (fun acc v -> H.add h v acc; acc + 1) 0 topo;
    Console.debug "...adding transitive closure...";
    ignore @@
    List.iter
      (fun v ->
         let i = H.find h v in
         Deps.iter_succ
           (fun v ->
              let j = H.find h v in
              Bitset.set sets.(i) j;
              Bitset.unite sets.(i) sets.(j))
           g
           v)
      topo;
    Console.debug "...propagating to the graph...";
    H.iter (fun k v -> H.iter (fun k' v' -> if Bitset.mem sets.(v) v' then Deps.add_edge g k k') h) h;
    Console.debug "...finished transitive closure..."

class effect_collector fl file_info def =
  let eff = File_info.get file_info fl def in
  object
    (* Since we visit *until convergence* we need to restore previously saved deps (from write effects) *)
    val writes =
      let g = Deps.create ~size:(H_write.length eff.Effect.writes) () in
      H_write.iter
        (fun x from ->
           let x = Vertex.of_writes x in
           H_region.iter (fun r -> Deps.add_edge g x (Vertex.Region r)) from.Reads.global;
           H_formal_var.iter (fun v -> Deps.add_edge g x (Vertex.Parameter v)) from.Reads.poly)
        eff.Effect.writes;
      g
    val mutable is_target = eff.Effect.is_target
    val mutable depends = restore_depends eff

    method reflect =
      (* ignore @@ Oper.add_transitive_closure writes; *)
      add_transitive_closure writes;
      store_depends ~writes depends eff;
      Deps.iter_vertex
        (fun v ->
           if Vertex.is_writable v then
             let w = Vertex.to_writes_exn v in
             Deps.iter_succ
               (function
                 | Vertex.Region r    -> Effect.add_global_read w r eff
                 | Vertex.Parameter v -> Effect.add_poly_read w v eff
                 | Vertex.Local _     -> ()
                 | Vertex.Result      -> fail_on_result ())
               writes
               v)
        writes;
      if is_target then Effect.set_is_target eff

    val all_reads = H_vertex.create 16
    val curr_reads = Stack.create ()

    inherit frama_c_inplace

    method! vstmt =
      let collect_reads acc =
        H_vertex.(iter (replace acc) all_reads);
        Stack.iter H_vertex.(iter (replace acc)) curr_reads
      in
      let add_edges =
        let h_lv = H_vertex.create 4 and h_from = H_vertex.create 16 in
        fun ~lv ~from ->
          H_vertex.clear h_lv;
          H_vertex.clear h_from;
          from h_from;
          collect_reads h_from;
          lv h_lv;
          H_vertex.iter
            (fun lv () -> Deps.add_vertex writes lv; H_vertex.iter (const' @@ Deps.add_edge writes lv) h_from)
            h_lv
      in
      let add_depends ~reach_target =
        if reach_target then is_target <- true;
        if is_target then collect_reads depends
      in
      let handle_call lvo fundec params =
        let eff = File_info.get file_info fl fundec in
        if eff.Effect.is_target then begin
          add_depends ~reach_target:true;
          project_reads ~fundec ~params eff.Effect.depends depends
        end;
        let lvo = may_map (swap add_vertices_of_lval) lvo ~dft:(const ()) in
        let project_reads = project_reads ~fundec ~params in
        H_write.iter
          (fun w from ->
             let lv =
               match w with
               | Writes.Region _ -> fun acc-> H_vertex.replace acc (Vertex.of_writes w) ()
               | Writes.Result   -> lvo
             in
             add_edges ~lv ~from:(project_reads from))
        eff.Effect.writes
      in
      let handle_all_reads =
        let h = H_vertex.create 16 in
        fun () ->
          H_vertex.clear h;
          collect_reads h;
          add_depends ~reach_target:false;
          Deps.iter_vertex (fun v -> H_vertex.iter (const' @@ Deps.add_edge writes v) h) writes;
          H_vertex.(iter (replace all_reads)) h
      in
      let continue_under vs =
        Stack.push vs curr_reads;
        DoChildrenPost (fun s -> ignore @@ Stack.pop curr_reads; s)
      in
      fun s ->
        match s.skind with
        | Instr (Set (lv, e, _)) ->
          add_edges ~lv:(fun acc -> add_vertices_of_lval acc lv) ~from:(fun acc -> add_vertices_of_expr acc e);
          SkipChildren
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _)) when Options.Target_functions.mem vi.vname ->
          add_depends ~reach_target:true;
          SkipChildren
        | Instr (Call (lvo, { enode = Lval (Var vi, NoOffset) }, _, loc)) when Options.Alloc_functions.mem vi.vname ->
          begin match lvo with
          | Some lv ->
            let lv = Mem (new_exp ~loc @@ Lval lv), NoOffset in
            add_edges ~lv:(fun acc -> add_vertices_of_lval acc lv) ~from:(const ())
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
            ~lv:(fun acc -> H_vertex.replace acc Vertex.Result ())
            ~from:(may_map (swap add_vertices_of_expr) eo ~dft:(const ()));
          SkipChildren
        | Goto _ | Break _ | Continue _ ->
          handle_all_reads ();
          SkipChildren
        | If (e, _, _, _) | Switch (e, _, _, _) ->
          continue_under (let h = H_vertex.create 4 in add_vertices_of_expr h e; h)
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
    val mutable depends = restore_depends eff
    val mutable requires = eff.Effect.requires
    method add_stmt s = Requires.add_stmt s requires
    method add_body f = Requires.add_body f requires
    method reflect =
      store_depends depends eff;
      Effect.add_requires requires eff

    inherit frama_c_inplace
    method! vstmt =
      let has_nonempty_intersection ~bigger ~smaller =
        H_vertex.(try iter (fun v () -> if mem bigger v then raise Exit) smaller; false with Exit -> true)
      in
      let handle_call ~s lvo fundec params =
        let mark () = self#add_body fundec; self#add_stmt s in
        let eff = File_info.get file_info fl fundec in
        (* first project writes *)
        let writes = H_write.shallow_copy (Flag.create ()) eff.Effect.writes in
        H_write.filter_map_inplace
          (fun w reads ->
             match w with
             | Writes.Region r ->
               let v = Vertex.Region r in
               if H_vertex.mem depends v then Some reads
               else None
             | Writes.Result when has_some lvo ->
               let h = H_vertex.create 4 in
               opt_iter (add_vertices_of_lval h) lvo;
               if has_nonempty_intersection ~bigger:depends ~smaller:h then Some reads
               else None
             | Writes.Result -> None)
          writes;
        if eff.Effect.is_target then mark ();
        if H_write.length writes > 0 then begin
          (* propagate projected writes to callee depends *)
          H_write.iter
            (const' @@
              function
              | Writes.Region r -> Effect.add_global_dep r eff
              | Writes.Result -> Effect.add_result_dep eff)
            writes;
          (* project reads and propagate them to our (caller) depends *)
          let reads = Reads.create (Flag.create ()) in
          H_write.iter (fun _ from -> Reads.import ~from reads) writes;
          project_reads ~fundec ~params reads depends;
          mark ()
        end
      in
      let handle_assignment =
        let h = H_vertex.create 16 in
        fun ~s ~lv ~from ->
          H_vertex.clear h;
          add_vertices_of_lval h lv;
        if has_nonempty_intersection ~bigger:depends ~smaller:h then begin
          from depends;
          self#add_stmt s
        end;
        SkipChildren
      in
      let handle_stmt_list ~s stmts =
        if List.exists (fun s -> H_stmt.mem requires.Requires.stmts s) stmts then
          self#add_stmt s
      in
      fun s ->
        match s.skind with
        | Instr (Set (lv, e, _)) ->
          handle_assignment ~s ~lv ~from:(fun acc -> add_vertices_of_expr acc e)
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
          opt_iter (fun e -> if H_vertex.mem depends Vertex.Result then add_vertices_of_expr depends e) eo;
          SkipChildren
        | Goto _ | Break _ | Continue _ ->
          self#add_stmt s;
          SkipChildren
        | If (_, block1, block2, _) ->
          DoChildrenPost (fun s -> handle_stmt_list ~s @@ block1.bstmts @ block2.bstmts; s)
        | Switch (_, block, _, _)
        | Loop (_, block, _, _, _)
        | Block block ->
          DoChildrenPost (fun s -> handle_stmt_list ~s block.bstmts; s)
        | UnspecifiedSequence l ->
          DoChildrenPost (fun s -> handle_stmt_list ~s @@ List.map (fun (s, _ ,_ ,_, _) -> s) l; s)
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
      (fun _ e -> H_fundec.iter (fun f -> Fundec.Hashtbl.replace result f ()) e.Effect.requires.Requires.bodies)
      file_info;
    List.iter
      (fun kf ->
         try Fundec.Hashtbl.replace result (Kernel_function.get_definition kf) ()
         with Kernel_function.No_Definition -> ())
      (get_addressed_kfs ());
    result
  in
  object
    val mutable required_stmts = H_stmt.create (Flag.create ())

    inherit frama_c_inplace
    method! vfunc f =
      required_stmts <- (File_info.get file_info fl f).Effect.requires.Requires.stmts;
      DoChildren
    method! vstmt_aux s =
      if not (H_stmt.mem required_stmts s) then
        if Options.Use_ghosts.is_set () then begin
          s.ghost <- true;
          DoChildren
        end else begin
          let rec collect_labels acc s =
            let acc = List.fold_right Label.Set.add s.labels acc in
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
          let collect_labels s = Label.Set.(elements @@ collect_labels empty s) in
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
