(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "-4-9-42-44-45-48"]

open Extlib

open Cil_types
open Cil_datatype
open Cil
open Cil_printer
open Format
open Visitor

open Info
open Region
open! Common

module Make (Analysis : Analysis) = struct

  module I = Analysis.I

  let w_var vi =
    match isArithmeticOrPointerType vi.vtype, vi.vglob, vi.vformal with
    | true, true,  false -> `Global_var (Global_var.of_varinfo_exn vi)
    | true, false, true  -> `Poly_var   (Formal_var.of_varinfo_exn vi)
    | true, false, false -> `Local_var  (Local_var.of_varinfo_exn vi)
    | false, _,    _     -> Console.fatal
                              "Slice.w_var: broken invariant: trying to write to composite variable without region: %a"
                              pp_varinfo vi
    | true, glob,  frml  -> Console.fatal
                              "Slice.w_var: broken invariant: inconsistent varinfo: %a: .vglob=%B, .vformal=%B"
                              pp_varinfo vi  glob frml

  let unless_comp ty f = if not (isStructOrUnionType @@ Ty.normalize ty) then Some (f ()) else None

  let deref ~loc lv = Mem (new_exp ~loc @@ Lval lv), NoOffset

  let is_var_sating p e =
    match (stripCasts e).enode with
    | Lval (Var v, NoOffset) when p v -> true
    | _                               -> false

  let dummy_flag = Flag.create "slicing_dummy"

  module Make_local
      (C : sig val f : kernel_function option end)
      (F : I.E.Reads)
      (A : I.E.Assigns with type S.t = F.t and type S.some = F.some) = struct

    let f = opt_map Kernel_function.get_name C.f

    module R = struct
      include Representant
      include Analysis
      let poly,         local,         of_var,    of_lval,    of_expr,    relevant_region,    arg_regions =
          poly (the f), local (the f), of_var ?f, of_lval ?f, of_expr ?f, relevant_region ?f, arg_regions ?f
    end
    module U = R.U

    let w_mem ?fi u =
      match (U.repr u).R.kind, f with
      | `Global,    _                              -> `Global_mem (I.M.Global_mem.mk ?fi u)
      | `Local f,   Some f' when String.equal f f' -> `Local_mem  (I.M.Local_mem.mk ?fi u)
      | `Poly f,    Some f' when String.equal f f' -> `Poly_mem   (I.M.Poly_mem.mk ?fi u)
      | (`Local _
        | `Poly _), None                           -> Console.fatal "Slice.w_mem: broken invariant: writing to global \
                                                                     region outside any function: %a"
                                                        R.pp (U.repr u)
      | (`Local f
        | `Poly f), Some f'                        -> Console.fatal "Slice.w_mem: broken invariant: writing to local \
                                                                     region %a of function %s from frunction %s"
                                                        R.pp (U.repr u) f f'
      | `Dummy,     _                              -> Console.fatal "Slice.w_mem: broken invariant: dummy region \
                                                                     encountered"
    let w_lval =
      let deref_mem u = unless_comp (U.repr u).R.typ @@ fun () -> w_mem u in
      fun (h, off as lv) ->
        let no_offset () =
          match R.of_lval lv with
          | `Location (u, _) -> deref_mem u
          | `Value _ | `None ->
            match h with
            | Var vi         -> unless_comp vi.vtype @@ fun () -> w_var vi
            | Mem _          -> Console.fatal "Slice.w_lval: broken invariant: \
                                               Memory accessing lvalue without a location region: %a"
                                  pp_lval lv
        in
        match lastOffset off with
        | Field (fi, NoOffset) -> unless_comp fi.ftype R.(fun () -> w_mem ~fi @@ location @@ of_lval lv)
        | Field _              -> assert false
        | Index (_, NoOffset)  -> deref_mem R.(location @@ of_lval lv)
        | Index _              -> assert false
        | NoOffset             -> no_offset ()

    let unwrap (I.E.Some { reads = (module F'); assigns = (module A'); eff }) : (A.t, F.t) I.E.t =
      match F'.W, A'.W with
      | F.W, A.W -> eff
      | _        -> Console.fatal "Slice.unpack: broken invariant: got effect of a different function"

    let r_mem ?fi u = F.of_writes @@ w_mem ?fi u

    let r_var vi = F.of_writes @@ w_var vi

    let initial_deps assigns =
      let open List in
      iter
        (fun (n, rs) ->
           if n >= 1 then
             iter
               (fun r ->
                  let u = U.of_repr r in
                  if R.relevant_region u then
                    R.dot_voids
                      (fun u' ->
                         R.containers_of_void
                           (fun ty u'' ->
                              if snd @@ Ty.deref ty = n then begin
                                A.add_some (w_mem u)   (r_mem u'') assigns;
                                A.add_some (w_mem u'') (r_mem u)   assigns
                              end)
                           u')
                      u)
               rs)
        (R.all_void_xs ());
      may
        (fun kf ->
           let rv, args = Kernel_function.(get_vi kf, get_formals kf) in
           iter
             (fun vi ->
                match R.of_var vi with
                | `Location (u, _)
                  when not (isStructOrUnionType vi.vtype)
                    && vi.vaddrof                         -> A.add
                                                               (w_mem u) F.K.Poly_var (Formal_var.of_varinfo_exn vi)
                                                               assigns
                | `Location _ | `Value _ | `None          -> ())
             args;
           let (ret_ext_regions, param_regions), (ret_int_regions, arg_regions) =
             R.param_regions kf, R.arg_regions kf (Some (var rv)) (map evar args)
           in
           let add_all au pu =
             match unrollType (U.repr au).R.typ with
             | TComp (ci, _, _) when ci.cstruct -> iter
                                                     (fun fi ->
                                                        if not fi.faddrof && isArithmeticOrPointerType fi.ftype then
                                                          A.add_some (w_mem ~fi au) (r_mem ~fi pu) assigns)
                                                     ci.cfields
             | _                                -> ()
           in
           iter2 add_all arg_regions     param_regions;
           iter2 add_all ret_ext_regions ret_int_regions)

    let add_from_lval lv acc = may F.(fun w -> add_some (of_writes w) acc) @@ w_lval lv

    class rval_visitor f = object(self)
      inherit frama_c_inplace

      method! vexpr =
        let do_expr = ignore % visitFramacExpr (self :> frama_c_visitor) in
        let do_off = ignore % visitFramacOffset (self :> frama_c_visitor) in
        fun e ->
          match e.enode with
          | AddrOf  (Mem e, off)
          | StartOf (Mem e, off) -> do_expr e; do_off off; SkipChildren
          | Const _
          | SizeOf _
          | SizeOfStr _
          | SizeOfE _
          | AlignOf _
          | AlignOfE _
          | AddrOf _
          | StartOf _            -> SkipChildren
          | Lval _
          | UnOp _
          | BinOp _
          | CastE  _
          | Info _               -> DoChildren

      method! vlval lv =
        f lv;
        DoChildren
    end

    let visit_rval f = ignore % visitFramacExpr (new rval_visitor f)

    let add_from_rval e acc = visit_rval (fun lv -> add_from_lval lv acc) e

    let add_from_lval lv acc =
      let o = new rval_visitor (fun lv -> add_from_lval lv acc) in
      match lv with
      | Mem e, off -> ignore @@ visitFramacExpr o e; ignore @@ visitFramacOffset o off
      | Var _, off -> ignore @@ visitFramacOffset o off

    let assign_all e from assigns =
      visit_rval (fun lv -> may (fun w -> A.import_values w from assigns) @@ w_lval lv) e

    let prj_poly_var s params =
      let args =
        match s.skind with
        | Instr (Call (_, _, args, _)) -> args
        | _                            -> Console.fatal "Slice.project_reads: need the proper function call site: %a"
                                            pp_stmt s
      in
      let open List in
      let args = take (length params) args in
      let add_from_arg = combine params @@ map add_from_rval args in
      fun acc fv -> assoc (fv : Formal_var.t :> varinfo) add_from_arg acc

    let prj_poly_mem s =
      let map = R.map s in
      fun acc m -> F.add_some (I.M.Poly_mem.prj ~find:(fun u -> R.H_call.find u map) ~mk:r_mem m) acc

    let prj_reads (type t) (module F' : I.E.Reads with type t = t) s params =
      let prj_poly_var = prj_poly_var s params in
      let prj_poly_mem = prj_poly_mem s in
      fun ~from acc ->
        F'.iter_global_vars (fun v -> F.add_global_var v acc) from;
        F'.iter_poly_vars   (prj_poly_var acc) from;
        F'.iter_global_mems (fun mem -> F.add_global_mem mem acc) from;
        F'.iter_poly_mems   (prj_poly_mem acc) from

    let prj_write ?lv s =
      function
      | `Global_var _
      | `Global_mem _ as w -> Some w
      | `Poly_mem m        -> I.M.Poly_mem.prj
                                ~find:(fun u -> R.H_call.find u @@ R.map s)
                                ~mk:(fun ?fi u -> Some (w_mem ?fi u))
                                m
      | `Result            -> opt_bind w_lval lv
      | `Poly_var _
      | `Local_var _
      | `Local_mem _       -> None

    (* Incomplete, but suitable for fix-point iteration approach *)
    let add_transitive_closure =
      let module Vertex = struct
        type t = I.W.t * F.t
        let compare (a, _) (b, _) = I.W.compare a b
        let equal (a, _) (b, _) = I.W.equal a b
        let hash (x, _) = I.W.hash x
      end in
      let module Deps = Graph.Imperative.Digraph.Concrete (Vertex) in
      let module Sccs = Graph.Components.Make (Deps) in
      let open Deps in
      fun assigns ->
        let g = create () in
        A.iter (fun w r -> add_vertex g (w, r)) assigns;
        iter_vertex
          (fun (w_from, _ as v_from) ->
             match w_from  with
             | `Result                 -> ()
             | #I.W.readable as w_from ->
               iter_vertex
                 (fun (_, r_to as v_to) ->
                    if not (Vertex.equal v_from v_to) &&
                       F.(mem_some (of_writes w_from) r_to) then
                      add_edge g v_from v_to)
                 g)
          g;
        let open List in
        let sccs = rev @@ map rev @@ Sccs.scc_list g in
        let rec round =
          function
          | []                                 -> assert false
          | [_]                                -> ()
          | (_, from) :: ((_, r_c) :: _ as tl) -> F.import ~from r_c; round tl
        in
        iter
          (fun scc ->
             round @@ scc @ [hd scc];
             iter (fun (_, from as v) -> iter_succ (fun (_, r) -> F.import ~from r) g v) scc)
          sccs

    let close_depends =
      let reads = F.create dummy_flag in
      fun assigns depends ->
        F.clear reads;
        F.import ~from:depends reads;
        let import_reads w = F.import ~from:(A.find w assigns) depends in
        F.iter_global_mems (fun m -> import_reads @@ `Global_mem m) reads;
        F.iter_poly_mems   (fun m -> import_reads @@ `Poly_mem m)   reads;
        F.iter_local_mems  (fun m -> import_reads @@ `Local_mem m)  reads;
        F.iter_global_vars (fun v -> import_reads @@ `Global_var v) reads;
        F.iter_poly_vars   (fun v -> import_reads @@ `Poly_var v)   reads;
        F.iter_local_vars  (fun v -> import_reads @@ `Local_var v)  reads

    module Collect (M : sig val from : stmt -> F.t val info : I.t val eff : (A.t, F.t) I.E.t end) = struct
      open M
      let assigns = I.E.assigns eff
      let depends = I.E.depends eff

      let add_transitive_closure () = add_transitive_closure assigns
      let close_depends () = close_depends assigns depends

      let comp_assign lv e from =
        let r_lv, r_e =
          match e.enode with
          | Lval lv' -> R.(location @@ of_lval lv, location @@ of_lval lv')
          | _        -> Console.fatal "Slicing.comp_assign: RHS is not an lval: %a" pp_exp e
        in
        let ci =
          match unrollType @@ typeOf e with
          | TComp (ci, _, _)  -> ci
          | ty                -> Console.fatal "Slicing.comp_assign: RHS is not a composite: %a %a" pp_exp e pp_typ ty
        in
        List.iter
          (fun (path, fi) ->
             let w = w_mem ?fi @@ R.take path r_lv in
             A.add_some w (r_mem ?fi @@ R.take path r_e) assigns;
             A.import_values w from assigns)
          (Ci.all_offsets ci)

      let gassign lv ?e from =
        add_from_lval lv from;
        may (fun e -> add_from_rval e from) e;
        let e = opt_conv (dummy_exp @@ Lval lv) e in
        match w_lval lv with
        | Some w -> A.import_values w from assigns
        | None   -> comp_assign lv e from

      let assign s lv e = gassign lv ~e (from s)
      let return s eo =
        let from = from s in
        may
          (fun e ->
             add_from_rval e from;
             match e.enode, unrollType @@ typeOf e with
             | Lval lv, TComp _ -> comp_assign lv e from
             | _,       TComp _ -> Console.fatal "Slicing.return: composite expression that is not an lvalue: %a" pp_exp e
             | _                -> A.import_values `Result from assigns)
          eo
      let reach_target s = F.import ~from:(from s) depends

      let call s ?lv kf =
        let from = from s in
        let I.E.Some { reads; assigns = (module A'); eff = eff' } =
          I.get info R.flag @@ Kernel_function.get_definition kf
        in
        let prj_reads = prj_reads reads s (Kernel_function.get_formals kf) in
        let prj_write = prj_write ?lv s in
        if I.E.is_target eff' then begin
          F.import ~from depends;
          prj_reads ~from:(I.E.depends eff') depends
        end;
        A'.iter
          (fun w' from' ->
             may
               (fun w ->
                  let reads = A.find w assigns in
                  F.import ~from reads;
                  prj_reads ~from:from' reads)
               (prj_write w'))
          (I.E.assigns eff');
        may
          (fun lv ->
             add_from_lval lv from;
             gassign lv from)
          lv

      let alloc s lv e =
        let from = from s in
        let lv = deref ~loc:(Stmt.loc s) lv in
        add_from_rval e from;
        gassign lv from
      let stub s ?lv es =
        let from = from s in
        may
          (fun lv ->
             List.iter (fun e -> add_from_rval e from) es;
             gassign lv from)
          lv
      let goto s = F.import ~from:(from s) @@ A.find (w_var @@ I.H_stmt.find info.I.goto_vars s) assigns
      let assume s e =
        let from = from s in
        add_from_rval e from;
        assign_all e from assigns
    end

    let collector info =
      let eff = unwrap @@ I.get info R.flag (Kernel_function.get_definition @@ the C.f) in
      let under = Stack.create () in
      let from =
        let from = F.create dummy_flag in
        fun s ->
          F.clear from;
          List.iter
            (fun vi -> F.add_local_var (Local_var.of_varinfo_exn vi) from)
            (I.H_stmt_conds.find info.I.stmt_vars s);
          Stack.iter (fun from' -> F.import ~from:from' from) under;
          from
      in
      let module Collect = Collect (struct let from, info, eff = from, info, eff end) in
      let open Collect in
      object
        method start = ()
        method finish =
          add_transitive_closure ();
          close_depends ()

        inherit frama_c_inplace

        method! vstmt =
          let is_tracking_var v = isVoidPtrType v.vtype && I.E.is_tracking_var (Void_ptr_var.of_varinfo_exn v) eff in
          let start_tracking s lv v arg =
            assign s lv arg;
            I.E.add_tracking_var (Void_ptr_var.of_varinfo_exn v) eff
          in
          let do_children_under e =
            let r = F.create dummy_flag in
            add_from_rval e r;
            Stack.push r under;
            DoChildrenPost (fun s -> ignore @@ Stack.pop under; s)
          in
          fun s ->
            match s.skind with
            | Instr (Set (lv, e, _))
              when is_var_sating is_tracking_var e                       -> alloc s lv e;                 SkipChildren
            | Instr (Set (lv, e, _))                                     -> assign s lv e;                SkipChildren
            | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _))
              when Options.Target_functions.mem vi.vname                 -> reach_target s;               SkipChildren
            | Instr (Call (lvo,
                           { enode = Lval (Var vi, NoOffset) },
                           arg :: _,
                           _))
              when Options.Alloc_functions.mem vi.vname                  ->
              begin match lvo with
              | Some (Var v, NoOffset as lv) when isVoidPtrType v.vtype  -> start_tracking s lv v arg;    SkipChildren
              | Some lv                                                  -> alloc s lv arg;               SkipChildren
              | None                                                     ->                               SkipChildren
              end;
            | Instr (Call (_,
                           { enode = Lval (Var vi, NoOffset) }, [e], _))
              when Options.Assume_functions.mem vi.vname                 -> assume s e;                   SkipChildren
            | Instr (Call (lv,
                           { enode = Lval (Var vi, NoOffset) },
                           _, _))
              when Kf.mem vi                                             -> call
                                                                              s
                                                                              ?lv
                                                                              (Globals.Functions.get vi); SkipChildren
            | Instr (Call (lv,
                           { enode = Lval (Var _, NoOffset) },
                           args, _))                                     -> stub s ?lv args;              SkipChildren
            | Instr (Call (lv, _, args, _))                              -> List.iter
                                                                              (fun kf ->
                                                                                 call
                                                                                   s
                                                                                   ?lv
                                                                                   kf)
                                                                              (Analyze.filter_matching_kfs
                                                                                 lv args);                SkipChildren
            | Instr (Asm _ | Skip _ | Code_annot _)                      ->                               SkipChildren
            | Return (e, _)                                              -> return s e;                   SkipChildren
            | Goto _ | AsmGoto _ | Break _ | Continue _                  -> goto s;                       SkipChildren
            | If (e, _, _, _) | Switch (e, _, _, _)                      -> do_children_under e
            | Loop _  | Block _ | UnspecifiedSequence _                  ->                               DoChildren
            | Throw _ | TryCatch _ | TryFinally _ | TryExcept _          -> failwith
                                                                              "Unsupported features: exceptions \
                                                                               and their handling"
      end

    module Mark
        (M : sig val decide : [< I.W.t] list -> [ `Needed | `Not_yet ] val info : I.t val eff : (A.t, F.t) I.E.t end) =
    struct
      open M
      let assigns = I.E.assigns eff
      let depends = I.E.depends eff

      let close_depends () = close_depends assigns depends

      let comp_assign lv =
        let r_lv = R.(location @@ of_lval lv) in
        let ci =
          match unrollType @@ typeOfLval lv with
          | TComp (ci, _, _)  -> ci
          | ty                -> Console.fatal "Slicing.comp_assign: LHS is not a composite: %a : %a"
                                   pp_lval lv pp_typ ty
        in
        List.map (fun (path, fi) -> w_mem ?fi @@ R.take path r_lv) (Ci.all_offsets ci)

      let gassign lv = decide @@ match w_lval lv with Some w -> [w] | None -> comp_assign lv
      let assign = gassign
      let return eo =
        decide @@
        may_map
          (fun e ->
             match e.enode, unrollType @@ typeOf e with
             | Lval lv, TComp _ -> comp_assign lv
             | _,       TComp _ -> Console.fatal "Slicing.return: composite expression that is not an lvalue: %a"
                                     pp_exp e
             | _                -> [`Result])
          ~dft:[]
          eo
      let call s ?lv kf =
        let I.E.Some { reads = (module F');
                       assigns = (module A');
                       eff = eff' } =
          I.get info R.flag @@ Kernel_function.get_definition kf
        in
        let prj_write = prj_write ?lv s in
        let deps' = I.E.depends eff' in
        let may_push_and_cons f =
          opt_fold @@ List.cons % tap (fun w -> if F.(mem_some (of_writes w) depends) then f ())
        in
        decide @@
        A'.fold
          (fun w' _ ->
             match w', lv with
             | `Result,              Some lv -> may_push_and_cons
                                                  (fun () -> I.E.add_result_dep eff')
                                                  (w_lval lv)
             | `Result,              None    -> id
             | (#I.W.readable as w'), _      -> may_push_and_cons
                                                  F'.(fun () -> add_some (of_writes w') deps')
                                                  (prj_write w'))
          (I.E.assigns eff')
          []
      let alloc ~loc = gassign % deref ~loc
      let stub = may_map gassign ~dft:`Not_yet
      let goto s = decide @@ [`Local_var (Local_var.of_varinfo_exn @@ I.H_stmt.find info.I.goto_vars s)]
      let assume e =
        let r = ref [] in
        visit_rval (fun lv -> may (fun w -> r := w :: !r) @@ w_lval lv) e;
        decide !r
    end

    let marker info =
      let eff = unwrap @@ I.get info R.flag (Kernel_function.get_definition @@ the C.f) in
      let depends = I.E.depends eff in
      let has_result_dep = I.E.has_result_dep eff in
      let reads = F.create dummy_flag in
      let decide : 'a. ([< I.W.t ] as 'a) list -> _ =
        let decide needed = if needed then `Needed else `Not_yet in
        let single w = decide F.(mem_some (of_writes w) depends) in
        let intersects l =
          F.clear reads;
          List.iter
            (function
              | `Result            -> ()
              | #I.W.readable as w -> F.(add_some (of_writes w) reads))
            l;
          F.intersects reads depends
        in
        let rec mem_result : 'a. ([< I.W.t] as 'a) list -> _ =
          function
          | []            -> false
          | `Result :: _  -> true
          | _       :: xs -> mem_result xs
        in
        function
        | []                                -> `Not_yet
        | [`Result] when has_result_dep     -> `Needed
        | [`Result]                         -> `Not_yet
        | [#I.W.readable as w]              -> single w
        | l                                 -> decide (has_result_dep && mem_result l || intersects l)
      in
      let module Mark = Mark (struct let decide, info, eff = decide, info, eff end) in
      let open Mark in
      object
        method start = close_depends ()
        method finish = ()

        inherit frama_c_inplace
        method! vstmt =
          let is_tracking_var v = isVoidPtrType v.vtype && I.E.is_tracking_var (Void_ptr_var.of_varinfo_exn v) eff in
          fun s ->
            let mark vi =
              I.E.add_stmt_req s eff;
              may
                (fun vi ->
                   try
                     I.E.add_body_req (Kernel_function.get_definition @@ Globals.Functions.get vi) eff
                   with
                   | Kernel_function.No_Definition -> ())
                vi
            in
            let stmt ?vi verdict =
              begin match verdict with
              | `Not_yet -> ()
              | `Needed  -> mark vi
              end;
              SkipChildren
            in
            let at_least_one f l =
              begin match List.find_map f l with
              | Some _ as vi -> mark vi
              | None         -> ()
              end;
              SkipChildren
            in
            let stmts stmts = if List.exists (fun s -> I.E.has_stmt_req s eff) stmts then I.E.add_stmt_req s eff in
            let block b = stmts b.bstmts in
            match s.skind with
            | Instr (Set (lv, e, loc))
              when is_var_sating is_tracking_var e                        -> stmt @@ alloc ~loc lv
            | Instr (Set (lv, _, _))                                      -> stmt @@ assign lv
            | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _))
              when Options.Target_functions.mem vi.vname                  -> mark (Some vi); SkipChildren
            | Instr (Call (lv,
                           { enode = Lval (Var vi, NoOffset) }, _, loc))
              when Options.Alloc_functions.mem vi.vname                   ->
              begin match lv with
              | Some (Var v, NoOffset) when isVoidPtrType v.vtype         -> SkipChildren
              | Some lv                                                   -> stmt ~vi @@ alloc ~loc lv
              | None                                                      -> SkipChildren
              end;
            | Instr (Call (_,
                           { enode = Lval (Var vi, NoOffset) }, [e], _))
              when Options.Assume_functions.mem vi.vname                  -> stmt ~vi @@ assume e
            | Instr (Call (lv,
                           { enode = Lval (Var vi, NoOffset) }, _, _))
              when Kf.mem vi                                              -> stmt ~vi
                                                                               (call
                                                                                  s
                                                                                  ?lv
                                                                                  (Globals.Functions.get vi))
            | Instr (Call (lv,
                           { enode = Lval (Var _, NoOffset) }, _, _))     -> stmt @@ stub lv
            | Instr (Call (lv, _, args, _))                               -> at_least_one
                                                                               (fun kf ->
                                                                                  match call s ?lv kf with
                                                                                  | `Needed ->
                                                                                    Some (Kernel_function.get_vi kf)
                                                                                  | `Not_yet -> None)
                                                                               (Analyze.filter_matching_kfs lv args)
            | Instr (Asm _ | Skip _ | Code_annot _)                       -> SkipChildren
            | Return (e, _)                                               -> stmt @@ return e
            | Goto _ | AsmGoto _ | Break _ | Continue _                   -> stmt @@ goto s
            | If (_, b1, b2, _)                                           -> DoChildrenPost
                                                                               (fun s -> block b1; block b2; s)
            | Switch (_, b, _, _) | Loop (_, b, _, _, _) | Block  b       -> DoChildrenPost (fun s -> block b; s)
            | UnspecifiedSequence ss                                      -> DoChildrenPost
                                                                              (fun s ->
                                                                                 stmts @@
                                                                                 List.map (fun (s, _, _, _, _) -> s) ss;
                                                                                 s)
            | Throw _ | TryCatch _ | TryFinally _ | TryExcept _           -> failwith
                                                                               "Unsupported features: exceptions \
                                                                                and their handling"
      end
  end

  module Fixpoint = Fixpoint.Make (I)

  module H = I.H_fundec

  type visitor = unit Fixpoint.frama_c_collector H.t

  type visitors =
    {
      collectors : visitor;
      markers    : visitor
    }

  let prepare info =
    let module H = I.H_fundec in
    let collectors, markers = H.create 512, H.create 512 in
    Globals.Functions.iter_on_fundecs
      (fun d ->
         let I.E.Some { reads = (module F); assigns = (module A); _ } = I.get info Representant.flag d in
         let module L = Make_local (struct let f = Some (Globals.Functions.get d.svar) end) (F) (A) in
         H.replace collectors d @@ L.collector info;
         H.replace markers d @@ L.marker info);
    { collectors; markers }

end

(*

let collect_effects break_continue_cache =
  visit_until_convergence
    ~order:`topological
    (new effect_collector break_continue_cache)

let mark =
  visit_until_convergence
    ~order:`reversed
    (new marker)

class sweeper file_info =
  let dummy_flag = Flag.create "sweeper_dummy" in
  let required_bodies, main_eff =
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
    if Kernel_function.is_definition main then begin
      let d = Kernel_function.get_definition main in
      Fundec.Hashtbl.add result d ();
      result, Some (File_info.get file_info flag d)
    end else
      result, None
  in
  object
    val mutable eff = Effect.create dummy_flag

    inherit frama_c_inplace
    method! vfunc f =
      let name = f.svar.vname in
      if Options.(Alloc_functions.mem name || Assume_functions.mem name || Target_functions.mem name) then
        SkipChildren
      else begin
        eff <- File_info.get file_info flag f;
        DoChildren
      end
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
      | GVar (vi, ({ init = Some _ } as init), _)
        when
          not vi.vaddrof &&
          isArithmeticOrPointerType vi.vtype &&
          may_map
            ~dft:false
            (fun main_eff ->
               not Reads.(mem Global (Region.Variable (Global_var.of_varinfo_exn vi)) @@ Effect.depends main_eff))
            main_eff ->
        init.init <- None;
        SkipChildren
      | GVar (vi, ({ init = Some (CompoundInit _ as init') } as init), _) when has_some main_eff ->
        let rec filter_init =
          let deps = Effect.depends (the main_eff) in
          fun region ->
            function
            | SingleInit _ as i ->
              let relevant =
                let check_type t =
                  Reads.(mem Global @@ Region.Type_approximation (Primitive_type.of_typ_exn t)) deps
                in
                match region with
                | `Type t -> check_type t
                | `Field fi when fi.fcomp.cstruct ->
                  Reads.(mem Global (Region.Field (Struct_field.of_fieldinfo_exn fi)) deps)
                | `Field fi -> check_type fi.ftype
              in
              if relevant then Some i else None
            | CompoundInit (ty, inits) ->
              let inits =
                List.(
                  flatten @@
                  map
                  (fun (off, i) ->
                     let region =
                       match lastOffset off with
                       | Field ({ fcomp = { cstruct = true; _ }; faddrof = false; _ } as fi, NoOffset) -> `Field fi
                       | _ -> `Type (unrollType @@ typeOffset ty off)
                     in
                     may_map ~dft:[] (fun i -> [off, i]) @@ filter_init region i)
                  inits)
              in
              if inits <> [] then Some (CompoundInit (ty, inits)) else None
        in
        init.init <- filter_init (`Type (unrollType vi.vtype)) init';
        SkipChildren
      | _ -> DoChildren
  end

let sweep file_info = visitFramacFile (new sweeper file_info) @@ Ast.get ()

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
  collect_effects (collect_break_continue sccs) fi sccs;
  mark fi sccs;
  sweep fi
*)
