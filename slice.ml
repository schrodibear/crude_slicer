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
    | Type_approximation t -> Typ.hash (t :> typ) + 3
end

module H_region = Hashtbl.Make (Region)

module Formal_var = Make_var (struct let is_ok vi = vi.vformal end)

module H_formal_var = Hashtbl.Make (Formal_var)

module Reads = struct
  type t =
    {
      global : unit H_region.t;
      poly   : unit H_formal_var.t
    }

  let create () = { global = H_region.create 16; poly = H_formal_var.create 16 }
  let import ~from r =
    H_region.(iter (replace r.global) from.global);
    H_formal_var.(iter (replace r.poly) from.poly)
  let add_global g r = H_region.replace r.global g ()
  let add_poly p r = H_formal_var.replace r.poly p ()
  let subseteq r1 r2 =
    try
      H_region.(iter (const' @@ find r2.global) r1.global);
      H_formal_var.(iter (const' @@ find r2.poly) r2.poly);
      true
    with
    | Not_found -> false
  let copy r = { global = H_region.copy r.global; poly = H_formal_var.copy r.poly }
end

module H_fundec = Fundec.Hashtbl
module H_stmt = Stmt.Hashtbl

module Requires = struct
  type t =
    {
      bodies : unit H_fundec.t;
      stmts  : unit H_stmt.t
    }

  let create () = { bodies = H_fundec.create 16; stmts = H_stmt.create 64 }
  let import ~from r =
    H_fundec.(iter (replace r.bodies) from.bodies);
    H_stmt.(iter (replace r.stmts) from.stmts)
  let add_body f r = H_fundec.replace r.bodies f ()
  let add_stmt s r = H_stmt.replace r.stmts s ()
  let subseteq r1 r2 =
    try
      H_fundec.(iter (const' @@ find r2.bodies) r1.bodies);
      H_stmt.(iter (const' @@ find r2.stmts) r2.stmts);
      true
    with
    | Not_found -> false
  let copy r = { bodies = H_fundec.copy r.bodies; stmts = H_stmt.copy r.stmts }
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

module H_write = Hashtbl.Make (Writes)

module Local_var = Make_var (struct let is_ok vi = not vi.vglob && not vi.vformal end)

module H_local_var = Hashtbl.Make (Local_var)

module Effect = struct
  type t =
    {
              writes     : Reads.t H_write.t;
      mutable is_target  : bool;
              depends    : Reads.t;
              local_deps : unit H_local_var.t;
      mutable result_dep : bool;
              requires   : Requires.t
    }

  let create () =
    {
      writes = H_write.create 16;
      is_target = false;
      depends = Reads.create ();
      local_deps = H_local_var.create 16;
      result_dep = false;
      requires = Requires.create ()
    }

  let get_write e w =
    try H_write.find e.writes w with Not_found -> let r = Reads.create () in H_write.replace e.writes w r; r
  let add_writes w e =
    H_write.iter (fun w from -> Reads.import ~from (get_write e w)) w
  let add_global_read w r e = Reads.add_global r (get_write e w)
  let add_poly_read w p e = Reads.add_poly p (get_write e w)
  let add_global_dep d e = Reads.add_global d e.depends
  let add_poly_dep d e = Reads.add_poly d e.depends
  let add_depends d e = Reads.import ~from:d e.depends
  let add_local_dep d e = H_local_var.replace e.local_deps d ()
  let add_local_deps d e = H_local_var.(iter (replace e.local_deps) d)
  let add_result_dep e = e.result_dep <- true
  let add_requires d e = Requires.import ~from:d e.requires
  let set_is_target e = e.is_target <- true

  let add_body_req f e = Requires.add_body f e.requires
  let add_stmt_req s e = Requires.add_stmt s e.requires
  let subseteq e1 e2 =
    try
      (H_write.(iter (fun w r -> if not (Reads.subseteq r (find e2.writes w)) then raise Not_found) e1.writes); true)
      &&
      (not e1.is_target || e2.is_target) &&
      Reads.subseteq e1.depends e2.depends &&
      (H_local_var.(iter (const' @@ find e2.local_deps) e2.local_deps); true) &&
      (not e1.result_dep || e2.result_dep) &&
      Requires.subseteq e1.requires e2.requires
    with
    | Not_found -> false
  let copy e =
    {
      writes =
        (let writes = H_write.copy e.writes in
         H_write.filter_map_inplace (fun _ r -> Some (Reads.copy r)) writes;
         writes);
      is_target = e.is_target;
      depends = Reads.copy e.depends;
      local_deps = H_local_var.copy e.local_deps;
      result_dep = e.result_dep;
      requires = Requires.copy e.requires
    }
end

module File_info = struct
  type t = Effect.t H_fundec.t

  let create () = H_fundec.create 256
  let get fi f = try H_fundec.find fi f with Not_found -> let r = Effect.create () in H_fundec.replace fi f r; r
end

module Cg = Callgraph.Cg

module Components = Graph.Components.Make (Cg.G)

let condensate () =
  Console.debug " ...condensating... ";
  let cg = Cg.get () in
  Console.debug " ...sccs... ";
  let r = Components.scc_list cg in
  Console.debug " ...finished sccs... ";
  r

let rec until_convergence ~fixpoint_reached scc f fi =
  let old = File_info.create () in
  List.iter (fun d -> H_fundec.replace old d @@ Effect.copy @@ File_info.get fi d) scc;
  f fi scc;
  if fixpoint_reached scc ~old ~fresh:fi then ()
  else until_convergence ~fixpoint_reached scc f fi

class type ['a] frama_c_collector = object inherit frama_c_inplace method reflect : 'a end

let visit_until_convergence ~order ~fixpoint_reached (v : _ -> _ -> _ #frama_c_collector) fi =
  let sccs = condensate () in
  let iter =
    match order with
    | `topological -> List.iter
    | `reversed ->
      fun f l -> List.(iter f (rev l))
  in
  iter
    (fun scc ->
       let scc = List.(Kernel_function.(scc |> filter is_definition |> map get_definition)) in
       until_convergence
         ~fixpoint_reached
         scc
         (fun fi ->
            List.iter
              (fun d ->
                 Console.debug "Analysing function %s..." d.svar.vname;
                 let v = v fi d in
                 ignore @@ visitFramacFunction (v :> frama_c_visitor) d;
                 v#reflect))
         fi)
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
  H_region.iter (fun r -> replace acc (Vertex.Region r)) eff.Effect.depends.Reads.global;
  H_formal_var.iter (fun v -> replace acc (Vertex.Parameter v)) eff.Effect.depends.Reads.poly;
  H_local_var.iter (fun v -> replace acc (Vertex.Local v)) eff.Effect.local_deps;
  if eff.Effect.result_dep then replace acc (Vertex.Result) ();
  acc

let project_reads ~fundec ~params =
  let params = List.(combine fundec.sformals @@ map (swap add_vertices_of_expr) params) in
  fun from acc ->
    H_formal_var.iter
      (fun fv () -> (List.assoc (fv :> varinfo) params) acc) from.Reads.poly;
    H_region.iter (fun r -> H_vertex.replace acc (Vertex.Region r)) from.Reads.global

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
    Console.debug " ...adding tr. closure... ";
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
    Console.debug " ...propagating to the graph... ";
    H.iter (fun k v -> H.iter (fun k' v' -> if Bitset.mem sets.(v) v' then Deps.add_edge g k k') h) h;
    Console.debug " ...finished tr. closure... "

class effect_collector file_info def =
  let eff = File_info.get file_info def in
  object
    (* Since we visit *until convergence* we need to restore previously saved deps (from write effects) *)
    val writes =
      let g = Deps.create ~size:(H_write.length eff.Effect.writes) () in
      H_write.iter
        (fun x from ->
           let x = Vertex.of_writes x in
           H_region.iter
             (fun r () -> Deps.add_edge g x (Vertex.Region r))
             from.Reads.global;
           H_formal_var.iter
             (fun v () -> Deps.add_edge g x (Vertex.Parameter v))
             from.Reads.poly)
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
        let eff = File_info.get file_info fundec in
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

let effects_settled fs ~old ~fresh =
  List.for_all (fun f -> Effect.subseteq (File_info.get fresh f) (File_info.get old f)) fs

let collect_effects =
  visit_until_convergence
    ~order:`topological
    ~fixpoint_reached:effects_settled
    (new effect_collector)

class marker file_info def =
  let eff = File_info.get file_info def in
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
        let eff = File_info.get file_info fundec in
        (* first project writes *)
        let writes = H_write.create 16 in
        H_write.iter
          (fun w reads ->
             match w with
             | Writes.Region r ->
               let v = Vertex.Region r in
               if H_vertex.mem depends v then
                 H_write.replace writes w reads
             | Writes.Result when has_some lvo ->
               let h = H_vertex.create 4 in
               opt_iter (add_vertices_of_lval h) lvo;
               if has_nonempty_intersection ~bigger:depends ~smaller:h then
                 H_write.replace writes w reads
             | Writes.Result -> ())
          eff.Effect.writes;
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
          let reads = Reads.create () in
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
    ~fixpoint_reached:effects_settled
    (new marker)

class sweeper file_info =
  let required_bodies =
    let result = H_fundec.create 256 in
    H_fundec.(iter (fun _ e -> iter (replace result) e.Effect.requires.Requires.bodies) file_info);
    List.iter
      (fun kf ->
         try H_fundec.replace result (Kernel_function.get_definition kf) ()
         with Kernel_function.No_Definition -> ())
      (get_addressed_kfs ());
    result
  in
  object
    val mutable required_stmts = H_stmt.create 1

    inherit frama_c_inplace
    method! vfunc f =
      required_stmts <- (File_info.get file_info f).Effect.requires.Requires.stmts;
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
      | GFun (f, _) when not (H_fundec.mem required_bodies f) ->
        ChangeTo []
      | _ -> DoChildren
  end

let sweep file_info = visitFramacFile (new sweeper file_info) @@ Ast.get ()

let slice () =
  let fi = File_info.create () in
  collect_effects fi;
  mark fi;
  sweep fi
