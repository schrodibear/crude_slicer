(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016                                                    *)
(*                                                                        *)
(**************************************************************************)

open Cil_types
open Cil_datatype
open Cil
open Visitor

let (%>) f g x = f (g x)

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
end = struct
  type t = varinfo

  let of_varinfo vi = if C.is_ok vi then Some vi else None

  let of_varinfo_exn vi =
    if C.is_ok vi then vi
    else invalid_arg "Formal_var.of_varinfo_exn"
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
    | _ -> false

  let hash =
    function
    | Variable v1 -> 7 * Varinfo.hash (v1 :> varinfo)
    | Field f -> 7 * Fieldinfo.hash (f :> fieldinfo) + 1
    | Type_approximation t -> Typ.hash (t :> typ) + 3
end

module Region_set =
  Set.Make
    (struct
      type t = Region.t
      let compare = Region.compare
    end)

module Formal_var = Make_var (struct let is_ok vi = vi.vformal end)

module Formal_var_set =
  Set.Make
    (struct
      type t = Formal_var.t
      let compare (v1 : t) (v2 : t) = Varinfo.compare (v1 :> varinfo) (v2 :> varinfo)
    end)

module Reads = struct
  type t =
    {
      global : Region_set.t;
      poly : Formal_var_set.t
    }

  let empty = { global = Region_set.empty; poly = Formal_var_set.empty }
  let union r1 r2 = { global = Region_set.union r1.global r2.global; poly = Formal_var_set.union r1.poly r2.poly }
  let with_global g r = { r with global = Region_set.add g r.global }
  let with_poly p r = { r with poly = Formal_var_set.add p r.poly }
  let equal r1 r2 = Region_set.equal r1.global r2.global && Formal_var_set.equal r1.poly r2.poly
end

module Requires = struct
  type t =
    {
      bodies : Fundec.Set.t;
      stmts : Stmt.Set.t
    }

  let empty = { bodies = Fundec.Set.empty; stmts = Stmt.Set.empty }
  let with_body f r = { r with bodies = Fundec.Set.add f r.bodies }
  let with_stmt s r = { r with stmts = Stmt.Set.add s r.stmts }
  let equal r1 r2 = Fundec.Set.equal r1.bodies r2.bodies && Stmt.Set.equal r1.stmts r2.stmts
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
    | _ -> false

  let hash =
    function
    | Region r -> 3 * Region.hash r
    | Result -> 1
end

module Writes_map =
  Map.Make
    (struct
      type t = Writes.t
      let compare = Writes.compare
    end)

module Effect = struct
  type t =
    {
      writes : Reads.t Writes_map.t;
      is_target : bool;
      depends : Reads.t;
      requires : Requires.t
    }

  let empty =
    {
      writes = Writes_map.empty;
      is_target = false;
      depends = Reads.empty;
      requires = Requires.empty
    }

  open Reads
  let with_writes w e = { e with writes = Writes_map.union (fun _ r1 r2 -> Some (Reads.union r1 r2)) e.writes w }
  let with_global_dep d e = { e with depends = with_global d e.depends }
  let with_poly_dep d e = { e with depends = with_poly d e.depends }
  let with_depends d e = { e with depends = union e.depends d }
  let with_target t e = if e.is_target == t then e else { e with is_target = t }

  open Requires
  let with_body_req f e = { e with requires = with_body f e.requires }
  let with_stmt_req s e = { e with requires = with_stmt s e.requires }
  let equal e1 e2 =
    Writes_map.equal Reads.equal e1.writes e2.writes &&
    Reads.equal e1.depends e2.depends &&
    Requires.equal e1.requires e2.requires &&
    e1.is_target = e2.is_target
end

module File_info = struct
  type t = Effect.t Fundec.Map.t

  let empty = Fundec.Map.empty
  let get fi f = try Fundec.Map.find f fi with Not_found -> Effect.empty
  let with_effect fi f e = Fundec.Map.add f (e @@ try Fundec.Map.find f fi with Not_found -> Effect.empty) fi
end

module Components = Graph.Components.Make (Cg.G)

let condensate () =
  Kernel.feedback "Computing callgraph...";
  let cg = Cg.get () in
  Kernel.feedback "Callgraph computed";
  Components.scc_list cg

let rec until_convergence ~fixpoint_reached f x =
  let x' = f x in
  if fixpoint_reached ~old:x ~fresh:x' then x'
  else until_convergence ~fixpoint_reached f x'

class type ['a] frama_c_collector = object inherit frama_c_inplace method result : 'a end

let visit_until_convergence =
  let sccs = condensate () in
  fun ~fixpoint_reached (v : _ -> _ -> _ #frama_c_collector) x ->
    List.fold_left
      (fun acc scc ->
         until_convergence
           ~fixpoint_reached:(fixpoint_reached scc)
           (fun acc ->
              List.fold_left
                (fun acc kf ->
                   if Kernel_function.is_definition kf then
                     let def = Kernel_function.get_definition kf in
                     let v = v acc def in
                     ignore @@ visitFramacFunction (v :> frama_c_visitor) def;
                     v#result
                 else acc)
              acc
              scc)
           acc)
      x
      sccs

module Local_var = Make_var (struct let is_ok vi = not vi.vglob && not vi.vformal end)

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

module Deps = Graph.Imperative.Graph.Concrete (Vertex)
module Oper = Graph.Oper.I (Deps)

let vertices_of_lval lv =
  let typ = typeOfLval lv in
  if isArithmeticOrPointerType typ then
    match lv with
    | Var ({ vformal = true; _ } as vi), NoOffset -> [Vertex.Parameter (Formal_var.of_varinfo_exn vi)]
    | Var ({ vglob = true; _ } as vi), NoOffset -> [Vertex.Region (Region.Variable (Global_var.of_varinfo_exn vi))]
    | Var vi, NoOffset -> [Vertex.Local (Local_var.of_varinfo_exn vi)]
    | _, off ->
      match Cil.lastOffset off with
      | Field ({ fcomp = { cstruct = true; _ }; faddrof = false; _ } as fi, NoOffset) ->
        [Vertex.Region (Region.Field (Struct_field.of_fieldinfo_exn fi))]
      | _ -> [Vertex.Region (Region.Type_approximation (Primitive_type.of_typ_exn typ))]
  else
    match unrollType typ with
    | TVoid _
    | TInt _
    | TEnum _
    | TFloat _
    | TPtr _
    | TNamed _ -> assert false (* Unrolled, not a pointer or arithmetic *)
    | TArray (typ,_,_,_) ->
      [Vertex.Region (Region.Type_approximation (Primitive_type.of_typ_exn (TPtr (typ, []))))]
    | TFun _ as t ->
      [Vertex.Region (Region.Type_approximation (Primitive_type.of_typ_exn (TPtr (t, []))))]
    | TComp (ci, _, _) ->
      
    | TBuiltin_va_list _ ->
      [Vertex.Region (Region.Type_approximation (Primitive_type.of_typ_exn voidPtrType))]

class effect_collector file_info def =
  let eff = File_info.get file_info def in
  object
    val writes =
      let g = Deps.create ~size:(Writes_map.cardinal eff.Effect.writes) () in
      Writes_map.iter
        (fun x from ->
           let x = Vertex.of_writes x in
           Region_set.iter
             (fun r -> Deps.add_edge g x (Vertex.Region r))
             from.Reads.global;
           Formal_var_set.iter
             (fun v -> Deps.add_edge g x (Vertex.Parameter v))
             from.Reads.poly)
        eff.Effect.writes;
      g
    val is_target = eff.Effect.is_target
    method result =
      ignore @@ Oper.add_transitive_closure writes;
      let writes =
        Writes_map.empty |>
        Deps.fold_vertex
          (fun v ->
             if Vertex.is_writable v then
               Reads.empty |>
               Deps.fold_succ
                 (function
                   | Vertex.Region r -> Reads.with_global r
                   | Vertex.Parameter v -> Reads.with_poly v
                   | Vertex.Local v -> Extlib.id
                   | Vertex.Result -> failwith "Should not happen: dependence on the return value")
                 writes
                 v |>
               Writes_map.add @@ Vertex.to_writes_exn v
             else
               Extlib.id)
          writes
      in
      File_info.with_effect file_info def (Effect.with_target is_target %> Effect.with_writes writes)

    inherit frama_c_inplace

    
  end
