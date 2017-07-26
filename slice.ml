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
open Visitor

open Info
open Region
open! Common

module Make (Analysis : Analysis) = struct

  module I = Analysis.I

  let w_var vi =
    match isArithmeticOrPointerType vi.vtype, vi.vglob, vi.vformal with
    | true, true,  false -> `Global_var (Global_var.of_varinfo vi)
    | true, false, true  -> `Poly_var   (Formal_var.of_varinfo vi)
    | true, false, false -> `Local_var  (Local_var.of_varinfo vi)
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
      (C : sig val f : kernel_function end)
      (F : I.E.Reads)
      (A : I.E.Assigns with type S.t = F.t and type S.some = F.some) = struct

    let f = Kernel_function.get_name C.f

    module R = struct
      include Representant
      include Analysis
      let poly,   local,   of_var,    of_lval,    of_expr,    relevant_region,    arg_regions =
          poly f, local f, of_var ~f, of_lval ~f, of_expr ~f, relevant_region ~f, arg_regions ~f
    end
    module U = R.U

    let w_mem ?fi u =
      match (U.repr u).R.kind with
      | `Global                          -> `Global_mem (I.M.Global_mem.mk ?fi u)
      | `Local f' when String.equal f f' -> `Local_mem  (I.M.Local_mem.mk ?fi u)
      | `Poly f'  when String.equal f f' -> `Poly_mem   (I.M.Poly_mem.mk ?fi u)
      | `Local f'
      | `Poly f'                         -> Console.fatal "Slice.w_mem: broken invariant: writing to local \
                                                           region %a of function %s from function %s"
                                              R.pp (U.repr u) f' f
      | `Dummy                           -> Console.fatal "Slice.w_mem: broken invariant: dummy region \
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
        | Field (fi, NoOffset)
          when fi.faddrof
             || not fi.fcomp.cstruct -> unless_comp fi.ftype R.(fun () -> w_mem @@ location @@ of_lval lv)
        | Field (fi, NoOffset)       -> unless_comp fi.ftype R.(fun () -> w_mem ~fi @@ location @@ of_lval lv)
        | Field _                    -> assert false
        | Index (_, NoOffset)        -> deref_mem R.(location @@ of_lval lv)
        | Index _                    -> assert false
        | NoOffset                   -> no_offset ()

    let unwrap (I.E.Some { reads = (module F'); assigns = (module A'); eff }) : (A.t, F.t) I.E.t =
      match F'.W, A'.W with
      | F.W, A.W -> eff
      | _        -> Console.fatal "Slice.unpack: broken invariant: got effect of a different function"

    let r_mem ?fi u = F.of_write @@ w_mem ?fi u

    let r_var vi = F.of_write @@ w_var vi

    let extract info = unwrap @@ I.get info R.flag (Kernel_function.get_definition C.f)

    let init_deps info () =
      let assigns = I.E.assigns @@ extract info in
      let open List in
      let rv, args = Kernel_function.(R.retvar @@ get_vi C.f, get_formals C.f) in
      iter
        (fun vi ->
           match R.of_var vi with
           | `Location (u, _)
             when not (isStructOrUnionType vi.vtype)
               && vi.vaddrof                         -> A.add
                                                          (w_mem u) F.K.Poly_var (Formal_var.of_varinfo vi)
                                                          assigns
           | `Location _ | `Value _ | `None          -> ())
        args;
      let param_regions, arg_regions =
        (R.param_regions C.f, R.arg_regions dummyStmt C.f (Some (var rv)) (map evar args)) |>
        if isStructOrUnionType @@ Ty.rtyp_if_fun rv.vtype
        then
          function
          | re :: prs, ri :: ars -> ri :: prs, re :: ars
          | [], _ | _, []        -> Console.fatal "Slice.init_deps: broken invariant: no composite return region"
        else
          id
      in
      let arg_tys =
        Ty.rtyp_if_fun rv.vtype :: map (fun vi -> vi.vtype) args |>
        filter (fun ty -> isStructOrUnionType ty || isPointerType ty || isArrayType ty)
      in
      let add_all (ty, (au, pu)) =
        match unrollType ty with
        | TComp (ci, _, _) when ci.cstruct -> iter
                                                (fun fi ->
                                                   if not fi.faddrof && isArithmeticOrPointerType fi.ftype then
                                                     A.add_some (w_mem ~fi au) (r_mem ~fi pu) assigns)
                                                ci.cfields
        | _                                -> ()
      in
      iter add_all @@ combine arg_tys @@ combine arg_regions param_regions

    let complement assigns depends =
      let open List in
      iter
        (fun (n, rs) ->
           if n = 0 then
             iter
               (fun r ->
                  let u = U.of_repr r in
                  if R.relevant_region u then
                    R.containers_of_void
                      (fun ty' u' ->
                         let r' = U.repr u' in
                         R.containers_of_void
                           (fun ty'' u'' ->
                              let r'' = U.repr u'' in
                              if not (R.equal r' r'')
                                 && List.for_all isArithmeticOrPointerType [R.typ r'; R.typ r'']
                                 && Ty.(snd @@ deref ty' = snd @@ deref ty'') then begin
                                if A.mem (w_mem u') assigns || A.mem (w_mem u'') assigns then begin
                                  A.add_some (w_mem u')  (r_mem u'') assigns;
                                  A.add_some (w_mem u'') (r_mem u')  assigns
                                end;
                                if F.mem_some (r_mem u') depends || F.mem_some (r_mem u'') depends then begin
                                  F.add_some (r_mem u') depends;
                                  F.add_some (r_mem u'') depends;
                                end
                              end)
                           u)
                      u)
               rs)
        (R.all_void_xs ())

    let add_from_lval lv acc = may F.(fun w -> add_some (of_write w) acc) @@ w_lval lv

    class rval_visitor f = object(self)
      inherit frama_c_inplace

      method! vexpr =
        let do_expr = ignore % visitFramacExpr (self :> frama_c_visitor) in
        let do_off = ignore % visitFramacOffset (self :> frama_c_visitor) in
        fun e ->
          match R.match_container_of1 e.enode, R.match_container_of2 e.enode with
          | Some (e, _), _
          | _,           Some (e, _) -> do_expr e;             SkipChildren
          | None,        None        ->
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
              | StartOf _            ->                        SkipChildren
              | Lval _
              | UnOp _
              | BinOp _
              | CastE  _
              | Info _               ->                        DoChildren

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
                       F.(mem_some (of_write w_from) r_to) then
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
      fun assigns depends result_dep ->
        F.clear reads;
        F.import ~from:depends reads;
        let import_reads w = if A.mem w assigns then F.import ~from:(A.find w assigns) depends in
        F.iter_global_mems (fun m -> import_reads @@ `Global_mem m) reads;
        F.iter_poly_mems   (fun m -> import_reads @@ `Poly_mem m)   reads;
        F.iter_local_mems  (fun m -> import_reads @@ `Local_mem m)  reads;
        F.iter_global_vars (fun v -> import_reads @@ `Global_var v) reads;
        F.iter_poly_vars   (fun v -> import_reads @@ `Poly_var v)   reads;
        F.iter_local_vars  (fun v -> import_reads @@ `Local_var v)  reads;
        if result_dep then import_reads `Result

    let is_tracking_var eff v = isVoidPtrType v.vtype && I.E.is_tracking_var (Void_ptr_var.of_varinfo v) eff

    module Collect (M : sig val from : stmt -> F.t val info : I.t val eff : (A.t, F.t) I.E.t end) = struct
      open M
      let assigns = I.E.assigns eff
      let depends = I.E.depends eff
      let set_is_target () = I.E.set_is_target eff

      let add_transitive_closure () = add_transitive_closure assigns
      let complement () = complement assigns depends
      let close_depends () = close_depends assigns depends (I.E.has_result_dep eff)

      let is_tracking_var = is_tracking_var eff

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
          (Ci.offsets ci)

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
             match unrollType @@ typeOf e with
             | TComp _ -> comp_assign (var @@ R.retvar @@ Kernel_function.get_vi C.f) e from
             | _       -> A.import_values `Result from assigns)
          eo
      let reach_target s =
        F.import ~from:(from s) depends;
        set_is_target ()

      let call s ?lv kf =
        let from = from s in
        let I.E.Some { reads; assigns = (module A'); eff = eff' } =
          I.get info R.flag @@ Kernel_function.get_definition kf
        in
        let prj_reads = prj_reads reads s (Kernel_function.get_formals kf) in
        let prj_write = prj_write ?lv s in
        if I.E.is_target eff' then begin
          F.import ~from depends;
          prj_reads ~from:(I.E.depends eff') depends;
          set_is_target ()
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
      let goto s = F.import ~from:(from s) @@ A.find (w_var @@ H_stmt.find info.I.goto_vars s) assigns
      let assume s e =
        let from = from s in
        add_from_rval e from;
        assign_all e from assigns
    end

    let collector info =
      let eff = extract info in
      let under = Stack.create () in
      let from =
        let from = F.create dummy_flag in
        fun s ->
          F.clear from;
          List.iter
            (fun vi -> F.add_local_var (Local_var.of_varinfo vi) from)
            (H_stmt_conds.find_all info.I.stmt_vars s);
          Stack.iter (fun from' -> F.import ~from:from' from) under;
          from
      in
      let module Collect = Collect (struct let from, info, eff = from, info, eff end) in
      let open Collect in
      object
        method start = ()
        method finish =
          add_transitive_closure ();
          close_depends ();
          complement ()

        inherit frama_c_inplace

        method! vstmt =
          let start_tracking s lv v arg =
            assign s lv arg;
            I.E.add_tracking_var (Void_ptr_var.of_varinfo v) eff
          in
          let do_children_under e =
            let r = F.create dummy_flag in
            add_from_rval e r;
            Stack.push r under;
            DoChildrenPost (fun s -> ignore @@ Stack.pop under; s)
          in
          fun s ->
            match s.skind with
            | Instr (Set ((Var v, NoOffset as lv), e, _))
              when isVoidPtrType v.vtype
                && is_var_sating is_tracking_var e                       -> start_tracking s lv v e;      SkipChildren
            | Instr (Set (lv, e, _))
              when is_var_sating is_tracking_var e
                && not (isVoidPtrType @@ typeOfLval lv)                  -> alloc s lv e;                 SkipChildren
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
              when Kf.mem_definition vi                                  -> call
                                                                              s
                                                                              ?lv
                                                                              (Globals.Functions.get vi); SkipChildren
            | Instr (Call (lv,
                           { enode = Lval (Var _, NoOffset) },
                           args, _))                                     -> stub s ?lv args;              SkipChildren
            | Instr (Call (lv, e, args, _))                              ->
              let kfs = Analyze.callee_approx e in
              begin match kfs with
              | []                                                       -> stub s ?lv args;              SkipChildren
              | kfs                                                      -> List.iter (call s ?lv) kfs;   SkipChildren
              end
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

      let complement () = complement assigns depends
      let close_depends () = close_depends assigns depends (I.E.has_result_dep eff)

      let is_tracking_var = is_tracking_var eff

      let comp_assign lv =
        let r_lv = R.(location @@ of_lval lv) in
        let ci =
          match unrollType @@ typeOfLval lv with
          | TComp (ci, _, _)  -> ci
          | ty                -> Console.fatal "Slicing.comp_assign: LHS is not a composite: %a : %a"
                                   pp_lval lv pp_typ ty
        in
        List.map (fun (path, fi) -> w_mem ?fi @@ R.take path r_lv) (Ci.offsets ci)

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
          opt_fold @@ List.cons % tap (fun w -> if F.(mem_some (of_write w) depends) then f ())
        in
        let writes =
          A'.fold
            (fun w' _ ->
               match w', lv with
               | `Result,              Some lv -> may_push_and_cons
                                                    (fun () -> I.E.add_result_dep eff')
                                                    (w_lval lv)
               | `Result,              None    -> id
               | (#I.W.readable as w'), _      -> may_push_and_cons
                                                    F'.(fun () -> add_some (of_write w') deps')
                                                    (prj_write w'))
            (I.E.assigns eff')
            []
        in
        if I.E.is_target eff' then `Needed else decide writes

      let alloc ~loc = gassign % deref ~loc
      let stub = may_map gassign ~dft:`Not_yet
      let goto s = decide @@ [`Local_var (Local_var.of_varinfo @@ H_stmt.find info.I.goto_vars s)]
      let assume e =
        let r = ref [] in
        visit_rval (fun lv -> may (fun w -> r := w :: !r) @@ w_lval lv) e;
        decide !r
    end

    let marker info =
      let eff = extract info in
      let depends = I.E.depends eff in
      let has_result_dep () = I.E.has_result_dep eff in
      let reads = F.create dummy_flag in
      let decide =
        let decide needed = if needed then `Needed else `Not_yet in
        let single w = decide F.(mem_some (of_write w) depends) in
        let intersects l =
          F.clear reads;
          List.iter
            (function
              | `Result            -> ()
              | #I.W.readable as w -> F.(add_some (of_write w) reads))
            l;
          F.intersects reads depends
        in
        let rec mem_result =
          function
          | []            -> false
          | `Result :: _  -> true
          | #I.W.t  :: xs -> mem_result xs
        in
        function
        | []                               -> `Not_yet
        | [`Result] when has_result_dep () -> `Needed
        | [`Result]                        -> `Not_yet
        | [#I.W.readable as w]             -> single w
        | (l : [< I.W.t] list)             -> decide (has_result_dep () && mem_result l || intersects l)
      in
      let module Mark = Mark (struct let decide, info, eff = decide, info, eff end) in
      let open Mark in
      object
        method start =
          close_depends ();
          complement ()
        method finish = ()

        inherit frama_c_inplace
        method! vstmt s =
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
          let try_all f l =
            List.(iter (mark % some) @@ concat_map f l);
            SkipChildren
          in
          let stmts stmts = if List.exists (fun s -> I.E.has_stmt_req s eff) stmts then I.E.add_stmt_req s eff in
          let block b = stmts b.bstmts in
          match s.skind with
          | Instr (Set (lv, e, loc))
            when is_var_sating is_tracking_var e
              && not (isVoidPtrType @@ typeOfLval lv)                   -> stmt @@ alloc ~loc lv
          | Instr (Set (lv, _, _))                                      -> stmt @@ assign lv
          | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _))
            when Options.Target_functions.mem vi.vname                  -> mark (Some vi); SkipChildren
          | Instr (Call (lv,
                         { enode = Lval (Var vi, NoOffset) }, _, loc))
            when Options.Alloc_functions.mem vi.vname                   ->
            begin match lv with
            | Some (Var v, NoOffset as lv) when isVoidPtrType v.vtype   -> stmt ~vi @@ assign lv
            | Some lv                                                   -> stmt ~vi @@ alloc ~loc lv
            | None                                                      -> SkipChildren
            end;
          | Instr (Call (_,
                         { enode = Lval (Var vi, NoOffset) }, [e], _))
            when Options.Assume_functions.mem vi.vname                  -> stmt ~vi @@ assume e
          | Instr (Call (lv,
                         { enode = Lval (Var vi, NoOffset) }, _, _))
            when Kf.mem_definition vi                                   -> stmt ~vi
                                                                             (call
                                                                                s
                                                                                ?lv
                                                                                (Globals.Functions.get vi))
          | Instr (Call (lv,
                         { enode = Lval (Var _, NoOffset) }, _, _))     -> stmt @@ stub lv
          | Instr (Call (lv, e, _, _))                                  ->
            let kfs = Analyze.callee_approx e in
            begin match kfs with
            | []                                                       -> stmt @@ stub lv
            | kfs                                                      -> try_all
                                                                            (fun kf ->
                                                                               match call s ?lv kf with
                                                                               | `Needed  -> [Kernel_function.get_vi kf]
                                                                               | `Not_yet -> [])
                                                                             kfs
            end
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

    let filter_init info =
      let eff = extract info in
      let depends = I.E.depends eff in
      fun v init ->
        let rec filter lv =
          function
          | SingleInit _ as i   -> opt_bind
                                     (fun w -> if F.(mem_some (of_write w) depends) then Some i else None)
                                     (w_lval lv)
          | CompoundInit (ty, l) -> List.filter
                                      (fun (off, init) -> has_some @@ filter (addOffsetLval off lv) init)
                                      l |> fun l ->
                                    if l <> [] then Some (CompoundInit (ty, l)) else None
        in
        opt_bind (filter @@ var v) init.init
  end

  module Make (M : sig val info : I.t end) = struct
    open M

    module Fixpoint = Fixpoint.Make (I)

    module H = H_fundec

    let collectors, markers, initializers, filters = H.create 512, H.create 512, H.create 512, H.create 512

    let () =
      Globals.Functions.iter_on_fundecs
        (fun d ->
           let I.E.Some { reads = (module F); assigns = (module A); _ } = I.get info Representant.flag d in
           let module L = Make_local (struct let f = Globals.Functions.get d.svar end) (F) (A) in
           H.replace collectors d @@ L.collector info;
           H.replace markers d @@ L.marker info;
           H.replace initializers d @@ L.init_deps info;
           H.replace filters d @@ L.filter_init info)

    let collect = Fixpoint.visit_until_convergence ~order:`topological (const @@ H.find collectors) info
    let mark =    Fixpoint.visit_until_convergence ~order:`reversed    (const @@ H.find markers) info

    let init () =
      Console.debug "Started init (init_deps for every function)...";
      Globals.Functions.iter_on_fundecs (fun d -> H.find initializers d ())

    let is_named = function Label _ -> true | _ -> false

    let collect_labels s =
      let rec loop acc s =
        let open List in
        fold_right Label.Set.add (filter is_named s.labels) acc |>
        fold_left' loop @@
        match s.skind with
        | If (_, b1, b2, _)        ->  b1.bstmts @ b2.bstmts
        | Switch (_, b, _, _)
        | Loop (_, b, _, _, _)
        | Block b                  ->  b.bstmts
        | UnspecifiedSequence l    ->  map (fun (s, _, _, _, _) -> s) l
        | _                        ->  []
      in
      Label.Set.(elements @@ loop (of_list s.labels) s)

    let shrink_block b =
      let rec loop acc ss =
        match ss, acc with
        | [],                                               acc -> List.rev acc
        | { skind = Instr (Skip _); labels = []; _ } :: ss, acc -> loop acc ss

        | s :: ss,
          ({ skind = Instr (Skip _); _ } as s') :: acc          ->(s.labels <- s'.labels @ s.labels;
                                                                   loop (s :: acc) ss)
        | s :: ss,                                          acc -> loop (s :: acc) ss
      in
      b.bstmts <- loop [] b.bstmts

    class sweeper () =
      let required_bodies, main_filter =
        let open Kernel_function in
        let result = H.create 256 in
        H.(iter
             (fun _ -> I.E.iter_body_reqs @@ fun f -> replace result f ())
             info.I.effects);
        List.iter
          (fun kf ->
             try                H.replace result (get_definition kf) ()
             with
             | No_Definition -> ())
          (Analyze.get_addressed_kfs ());
        match get_definition @@ Globals.Functions.find_by_name @@ Kernel.MainFunction.get () with
        | d                  -> H.add result d (); result, Some (H.find filters d)
        | exception
            (Not_found
            | No_Definition) ->                    result, None
      in
      object
        val mutable eff = I.E.create dummy_flag

        inherit frama_c_inplace

        method! vfunc f =
          let name = f.svar.vname in
          if Options.(Alloc_functions.mem name || Assume_functions.mem name || Target_functions.mem name)
          then                                  SkipChildren
          else (eff <- I.get info dummy_flag f; DoChildren)

        method! vstmt_aux s =
          if not (I.E.has_stmt_req' s eff)
          then if Options.Use_ghosts.is_set ()
            then (s.ghost <- true; DoChildren)
            else                   ChangeTo { s with skind = Instr (Skip (Stmt.loc s)); labels = collect_labels s }
          else                     DoChildren

        method! vblock _ = DoChildrenPost (tap shrink_block)

        method! vglob_aux g =
          match g, main_filter with
          | GFun (f, _), _ when not (H.mem required_bodies f) ->                                   ChangeTo []
          | GVar (vi, init, _), Some main_filter              -> init.init <- main_filter vi init; SkipChildren
          | _                                                 ->                                   DoChildren
      end

    module H_lab = Label.Hashtbl

    class cfg_fixupper () =
      let h_labs = H_lab.create 1024 in
      let update sr = sr := H_lab.find h_labs List.(hd @@ filter is_named !sr.labels) in
      let vis = object
        inherit frama_c_inplace
        method! vstmt s =
          begin match s.skind with
          | Goto (sr, _)                    -> update sr
          | AsmGoto (_, _, _, _, _, srs, _) -> List.iter update srs
          | _                               -> ()
          end;
          DoChildren
      end in
      object
        inherit frama_c_inplace

        method! vfunc _ =
          H_lab.clear h_labs;
          DoChildrenPost (tap @@ ignore % visitFramacFunction vis)

        method! vstmt s =
          List.iter (fun l -> H_lab.replace h_labs l s) s.labels;
          DoChildren
      end

    let sweep () =
      let file = Ast.get () in
      visitFramacFile (new sweeper ()) file;
      visitFramacFile (new cfg_fixupper ()) file;
      Cfg.clearFileCFG ~clear_id:false file;
      Cfg.computeFileCFG file;
      Rmtmps.removeUnusedTemps
        ~isRoot:(function GFun (f, _) when f.svar.vname = Kernel.MainFunction.get () -> true | _ -> false)
        file
  end
end

let slice () =
  Console.debug "Started slicing...";
  let offs_of_key = Info.H_field.create 2048 in
  Analyze.cache_offsets ~offs_of_key;
  let module Region_analysis = Region.Analysis (struct let offs_of_key = offs_of_key end) () in
  let { Region_analysis.I.goto_vars; stmt_vars; _ } as info = Region_analysis.I.create () in
  Analyze.fill_goto_tables ~goto_vars ~stmt_vars;
  let module Transform = Transform.Make (Region_analysis) in
  Transform.rewrite ();
  Region_analysis.compute_regions ();
  let module Slice = Make (Region_analysis) in
  let module Slice = Slice.Make (struct let info = info end) in
  Slice.init ();
  let sccs = Analyze.condensate () in
  Console.debug "Will now collect assigns and deps...";
  Slice.collect sccs;
  Console.debug "Will now mark...";
  Slice.mark sccs;
  Console.debug "Will now sweep...";
  Slice.sweep ()
