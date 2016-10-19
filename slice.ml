(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016                                                    *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "-4-9"]

open Extlib

open Cil_types
open Cil_datatype
open Cil
open Visitor

module Console = Options

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
  val compare : t -> t -> int
end = struct
  type t = varinfo

  let of_varinfo vi = if C.is_ok vi then Some vi else None

  let of_varinfo_exn vi =
    if C.is_ok vi then vi
    else invalid_arg "Formal_var.of_varinfo_exn"

  let compare v1 v2 = Varinfo.compare (v1 :> varinfo) (v2 :> varinfo)
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
    | Type_approximation t -> Typ.hash (t :> typ) + 3
end

module Region_set = Set.Make (Region)

module Formal_var = Make_var (struct let is_ok vi = vi.vformal end)

module Formal_var_set = Set.Make (Formal_var)

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
  let union r1 r2 = { bodies = Fundec.Set.union r1.bodies r2.bodies; stmts = Stmt.Set.union r1.stmts r2.stmts }
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

module Writes_map = Map.Make (Writes)

module Local_var = Make_var (struct let is_ok vi = not vi.vglob && not vi.vformal end)

module Local_var_set = Set.Make (Local_var)

module Effect = struct
  type t =
    {
              writes     : Reads.t Writes_map.t;
              is_target  : bool;
      mutable depends    : Reads.t; (* Mutabilty should only be used for forward depends propagation! *)
              local_deps : Local_var_set.t;
      mutable result_dep : bool;
              requires   : Requires.t
    }

  let empty =
    {
      writes = Writes_map.empty;
      is_target = false;
      depends = Reads.empty;
      local_deps = Local_var_set.empty;
      result_dep = false;
      requires = Requires.empty
    }

  open Reads
  let with_writes w e = { e with writes = Writes_map.union (fun _ r1 r2 -> Some (Reads.union r1 r2)) e.writes w }
  let with_global_dep d e = { e with depends = with_global d e.depends }
  let with_poly_dep d e = { e with depends = with_poly d e.depends }
  let with_depends d e = { e with depends = union e.depends d }
  let with_local_deps d e = { e with local_deps = Local_var_set.union e.local_deps d }
  let with_result_dep d e = let d' = e.result_dep || d in if e.result_dep = d' then e else { e with result_dep = d' }
  let with_requires d e = { e with requires = Requires.union d e.requires }
  let with_target t e = let t' = e.is_target || t in if e.is_target = t' then e else { e with is_target = t' }

  open Requires
  let with_body_req f e = { e with requires = with_body f e.requires }
  let with_stmt_req s e = { e with requires = with_stmt s e.requires }
  let equal e1 e2 =
    Writes_map.equal Reads.equal e1.writes e2.writes &&
    Reads.equal e1.depends e2.depends &&
    Local_var_set.equal e1.local_deps e2.local_deps &&
    Requires.equal e1.requires e2.requires &&
    e1.is_target = e2.is_target
end

module File_info = struct
  type t = Effect.t Fundec.Map.t

  let empty = Fundec.Map.empty
  let get fi f = try Fundec.Map.find f fi with Not_found -> Effect.empty
  let with_effect fi f e = Fundec.Map.add f (e @@ try Fundec.Map.find f fi with Not_found -> Effect.empty) fi
end

module Cg = Callgraph.Cg

module Components = Graph.Components.Make (Cg.G)

let condensate () =
  let cg = Cg.get () in
  Components.scc_list cg

let rec until_convergence ~fixpoint_reached f x =
  let x' = f x in
  if fixpoint_reached ~old:x ~fresh:x' then x'
  else until_convergence ~fixpoint_reached f x'

class type ['a] frama_c_collector = object inherit frama_c_inplace method result : 'a end

let visit_until_convergence ~order ~fixpoint_reached (v : _ -> _ -> _ #frama_c_collector) x =
  let sccs = condensate () in
  let fold =
    match order with
    | `topological -> List.fold_left
    | `reversed ->
      fun f x l -> List.fold_right (fun x acc -> f acc x) l x
  in
  fold
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

module Vertex_set = Set.Make (Vertex)

let rec vertices_of_lval =
  let single = Vertex_set.singleton in
  let parameter vi = single @@ Vertex.Parameter (Formal_var.of_varinfo_exn vi) in
  let global vi = single @@ Vertex.Region (Region.Variable (Global_var.of_varinfo_exn vi)) in
  let local vi = single @@ Vertex.Local (Local_var.of_varinfo_exn vi) in
  let field fi = single @@ Vertex.Region (Region.Field (Struct_field.of_fieldinfo_exn fi)) in
  let type_ typ =
    let typ = typeDeepDropAllAttributes @@ unrollTypeDeep typ in
    single @@ Vertex.Region (Region.Type_approximation (Primitive_type.of_typ_exn typ))
  in
  fun lv ->
    let typ = typeOfLval lv in
    if isArithmeticOrPointerType typ then
      match lv with
      | Var ({ vformal = true; vaddrof = false; _ } as vi), NoOffset                    -> parameter vi
      | Var ({ vglob = true; vaddrof = false; _ } as vi), NoOffset                      -> global vi
      | Var ({ vaddrof = false; _ } as vi), NoOffset                                    -> local vi
      | _, off ->
        match lastOffset off with
        | Field ({ fcomp = { cstruct = true; _ }; faddrof = false; _ } as fi, NoOffset) -> field fi
        | _                                                                             -> type_ typ
    else
      match unrollType typ with
      | TInt _
      | TEnum _
      | TFloat _
      | TPtr _
      | TNamed _                                                                        -> assert false
      (* Unrolled, not a pointer or arithmetic *)
      | TVoid _                                                                         -> type_ charType
      | TArray _                                                                        ->
        vertices_of_lval @@ addOffsetLval (Index (integer ~loc:Location.unknown 0, NoOffset)) lv
      | TFun _ as t                                                                     -> type_ (TPtr (t, []))
      | TComp (ci, _, _)                                                                ->
        List.fold_left
          (fun acc fi -> Vertex_set.union acc @@ vertices_of_lval @@ addOffsetLval (Field (fi, NoOffset)) lv)
          Vertex_set.empty
          ci.cfields
      | TBuiltin_va_list _                                                              -> type_ voidPtrType

class vertex_collector =
  object
    val mutable vertices = Vertex_set.empty
    method get = vertices

    inherit frama_c_inplace
    method! vlval lv =
      vertices <- Vertex_set.union (vertices_of_lval lv) vertices;
      DoChildren
  end

let vertices_of_expr e =
  let o = new vertex_collector in
  ignore (visitFramacExpr (o :> frama_c_visitor) e);
  o#get

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

let store_depends ?writes depends =
  let local_deps =
    Vertex_set.fold (function Vertex.Local lv -> Local_var_set.add lv | _ -> id) depends Local_var_set.empty
  in
  let result_dep = Vertex_set.mem Vertex.Result depends in
  let depends =
    Reads.empty |>
    Vertex_set.fold
      (fun v ->
         match v with
         | Vertex.Local _  ->
           opt_fold
             (fun writes _ ->
                Reads.union
                  (Deps.fold_succ
                     (function
                       (* no need to recurse, because the transitive closure is already computed *)
                       | Vertex.Local _     -> id
                       | Vertex.Parameter p -> Reads.with_poly p
                       | Vertex.Region r    -> Reads.with_global r
                       | Vertex.Result      -> fail_on_result ())
                     writes
                     v
                     Reads.empty))
             writes
             id
         | Vertex.Parameter p -> Reads.with_poly p
         | Vertex.Region r    -> Reads.with_global r
         | Vertex.Result      -> id)
      depends
  in
  depends, local_deps, result_dep

let restore_depends eff =
  let open Vertex_set in
  Region_set.fold (fun r -> add @@ Vertex.Region r) eff.Effect.depends.Reads.global empty |>
  Formal_var_set.fold (fun v -> add @@ Vertex.Parameter v) eff.Effect.depends.Reads.poly |>
  Local_var_set.fold (fun v -> add @@ Vertex.Local v) eff.Effect.local_deps |>
  if eff.Effect.result_dep then add Vertex.Result else id

let project_reads ~fundec ~params =
  let params = List.(combine fundec.sformals @@ map vertices_of_expr params) in
  fun from ->
    Formal_var_set.fold
      (fun fv -> Vertex_set.union @@ List.assoc (fv :> varinfo) params) from.Reads.poly Vertex_set.empty |>
    Region_set.fold (fun r -> Vertex_set.add @@ Vertex.Region r) from.Reads.global

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
    H.iter (fun k v -> H.iter (fun k' v' -> if Bitset.mem sets.(v) v' then Deps.add_edge g k k') h) h

class effect_collector file_info def =
  let eff = File_info.get file_info def in
  object
    (* Since we visit *until convergence* we need to restore previously saved deps (from write effects) *)
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
    val mutable is_target = eff.Effect.is_target
    val mutable depends = restore_depends eff

    method result =
      (*ignore @@ Oper.add_transitive_closure writes;*)
      add_transitive_closure writes;
      let depends, local_deps, result_dep = store_depends ~writes depends in
      let writes =
        Writes_map.empty |>
        Deps.fold_vertex
          (fun v ->
             if Vertex.is_writable v then
               Reads.empty |>
               Deps.fold_succ
                 (function
                   | Vertex.Region r    -> Reads.with_global r
                   | Vertex.Parameter v -> Reads.with_poly v
                   | Vertex.Local _     -> id
                   | Vertex.Result      -> fail_on_result ())
                 writes
                 v |>
               Writes_map.add @@ Vertex.to_writes_exn v
             else
               id)
          writes
      in
      File_info.with_effect
        file_info
        def
        Effect.(
          with_target is_target %>
          with_writes writes %>
          with_depends depends %>
          with_local_deps local_deps %>
          with_result_dep result_dep)

    val mutable all_reads = Vertex_set.empty
    val curr_reads = Stack.create ()

    inherit frama_c_inplace

    method! vstmt =
      let collect_reads () = Stack.fold Vertex_set.union all_reads curr_reads in
      let add_edges ~lv ~from =
        let from = Vertex_set.union from @@ collect_reads () in
        Vertex_set.iter (fun lv -> Deps.add_vertex writes lv; Vertex_set.iter (Deps.add_edge writes lv) from) lv
      in
      let add_depends ~reach_target =
        if reach_target then is_target <- true;
        if is_target then depends <- Vertex_set.union depends @@ collect_reads ()
      in
      let handle_call lvo fundec params =
        let eff = File_info.get file_info fundec in
        if eff.Effect.is_target then begin
          add_depends ~reach_target:true;
          depends <- Vertex_set.union depends @@ project_reads ~fundec ~params eff.Effect.depends
        end;
        let lvo = opt_map vertices_of_lval lvo in
        let project_reads = project_reads ~fundec ~params in
        Writes_map.iter
          (fun w from ->
             let lv =
               match w with
               | Writes.Region _ -> Vertex_set.singleton @@ Vertex.of_writes w
               | Writes.Result   -> opt_conv Vertex_set.empty lvo
             in
             add_edges ~lv ~from:(project_reads from))
        eff.Effect.writes
      in
      let handle_all_reads () =
        let all_reads' = collect_reads () in
        add_depends ~reach_target:false;
        Deps.iter_vertex (fun v -> Vertex_set.iter (Deps.add_edge writes v) all_reads') writes;
        all_reads <- all_reads'
      in
      let continue_under vs =
        Stack.push vs curr_reads;
        DoChildrenPost (fun s -> ignore @@ Stack.pop curr_reads; s)
      in
      fun s ->
        match s.skind with
        | Instr (Set (lv, e, _)) ->
          add_edges ~lv:(vertices_of_lval lv) ~from:(vertices_of_expr e);
          SkipChildren
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _)) when Options.Target_functions.mem vi.vname ->
          add_depends ~reach_target:true;
          SkipChildren
        | Instr (Call (lvo, { enode = Lval (Var vi, NoOffset) }, _, loc)) when Options.Alloc_functions.mem vi.vname ->
          begin match lvo with
          | Some lv ->
            let lv = Mem (new_exp ~loc @@ Lval lv), NoOffset in
            add_edges ~lv:(vertices_of_lval lv) ~from:Vertex_set.empty
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
            ~lv:(Vertex_set.singleton Vertex.Result)
            ~from:(opt_fold (fun e _ -> vertices_of_expr e) eo Vertex_set.empty);
          SkipChildren
        | Goto _ | Break _ | Continue _ ->
          handle_all_reads ();
          SkipChildren
        | If (e, _, _, _) | Switch (e, _, _, _) ->
          continue_under (vertices_of_expr e)
        | Loop _ | Block _ | UnspecifiedSequence _ -> DoChildren
        | Throw _ | TryCatch _ | TryFinally _ | TryExcept _  ->
          failwith "Unsupported features: exceptions and their handling"
  end

let effects_settled fs ~old ~fresh =
  List.for_all
    (fun f ->
       match Kernel_function.get_definition f with
       | f -> Effect.equal (File_info.get old f) (File_info.get fresh f)
       | exception Kernel_function.No_Definition -> true)
    fs

let collect_effects () =
  visit_until_convergence
    ~order:`topological
    ~fixpoint_reached:effects_settled
    (new effect_collector)
    File_info.empty

class marker file_info def =
  let eff = File_info.get file_info def in
  object(self)
    val mutable depends = restore_depends eff
    val mutable requires = eff.Effect.requires
    method add_stmt s =
      requires <- Requires.with_stmt s requires
    method add_body f =
      requires <- Requires.with_body f requires
    method result =
      let depends, local_deps, result_dep = store_depends depends in
      File_info.with_effect
        file_info
        def
        Effect.(
          with_depends depends %>
          with_local_deps local_deps %>
          with_requires requires %>
          with_result_dep result_dep)

    inherit frama_c_inplace
    method! vstmt =
      let handle_call ~s lvo fundec params =
        let mark () = self#add_body fundec; self#add_stmt s in
        let eff = File_info.get file_info fundec in
        let lvo = opt_map vertices_of_lval lvo in
        let writes =
          Writes_map.filter
            (fun w _ ->
               match w with
               | Writes.Region r -> Vertex_set.mem (Vertex.Region r) depends
               | Writes.Result
                 when has_some lvo -> Vertex_set.exists (fun v -> Vertex_set.mem v depends) @@ the lvo
               | Writes.Result -> false)
            eff.Effect.writes
        in
        if eff.Effect.is_target then mark ();
        if writes <> Writes_map.empty && eff <> Effect.empty then
          let depends', result_dep =
            Writes_map.fold
              (function
                | Writes.Region r -> fun _ ->  Reads.with_global r
                | Writes.Result -> fun _ -> id)
              writes
              Reads.empty |> fun d ->
            d, if Writes_map.mem Writes.Result writes then true else false
          in
          (* !!! *)
          eff.Effect.depends <- Reads.union depends' eff.Effect.depends;
          eff.Effect.result_dep <- result_dep || eff.Effect.result_dep;
          depends <-
            Vertex_set.union
              depends @@
              project_reads ~fundec ~params @@
                Writes_map.fold
                  (fun _ -> Reads.union)
                  writes
                  Reads.empty;
          mark ()
      in
      let handle_assignment ~s ~lv ~vs =
        if Vertex_set.exists (fun v -> Vertex_set.mem v depends) @@ vertices_of_lval lv then begin
          depends <- Vertex_set.union depends vs;
          self#add_stmt s
        end;
        SkipChildren
      in
      let handle_stmt_list ~s stmts =
        if List.exists (fun s -> Stmt.Set.mem s requires.Requires.stmts) stmts then
          self#add_stmt s
      in
      fun s ->
        match s.skind with
        | Instr (Set (lv, e, _)) ->
          handle_assignment ~s ~lv ~vs:(vertices_of_expr e)
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _)) when Options.Target_functions.mem vi.vname ->
          self#add_stmt s;
          begin try
            self#add_body (Kernel_function.get_definition @@ Globals.Functions.find_by_name vi.vname)
          with
          | Kernel_function.No_Definition -> ()
          end;
          SkipChildren
        | Instr (Call (lvo, { enode = Lval (Var vi, NoOffset) }, _, loc)) when Options.Alloc_functions.mem vi.vname ->
          begin match lvo with
          | Some lv ->
            let lv = Mem (new_exp ~loc @@ Lval lv), NoOffset in
            handle_assignment ~s ~lv ~vs:Vertex_set.empty
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
          opt_fold
            (fun e _ ->
               if Vertex_set.mem Vertex.Result depends then
                 depends <- Vertex_set.union depends (vertices_of_expr e))
            eo
            ();
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
    ~fixpoint_reached:effects_settled
    (new marker)

class sweeper file_info =
  let required_bodies =
    Fundec.Map.fold (fun _ e -> Fundec.Set.union e.Effect.requires.Requires.bodies) file_info Fundec.Set.empty
  in
  object
    val mutable required_stmts = Stmt.Set.empty

    inherit frama_c_inplace
    method! vfunc f =
      required_stmts <- (File_info.get file_info f).Effect.requires.Requires.stmts;
      DoChildren
    method! vstmt_aux s =
      if not (Stmt.Set.mem s required_stmts) then
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
      | GFun (f, _) when not (Fundec.Set.mem f required_bodies) ->
        (* ChangeTo [] *)
        DoChildren
      | _ -> DoChildren
  end

let sweep file_info = visitFramacFile (new sweeper file_info) @@ Ast.get ()

let slice () =
  collect_effects () |>
  mark |>
  sweep
