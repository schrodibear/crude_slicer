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

  module R = struct
    include Representant
    include Analysis
  end
  module U = R.U
  module I = R.I

  let w_mem ?f ?fi u =
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

  let w_lval =
    let deref_mem u = unless_comp (U.repr u).R.typ @@ fun () -> w_mem u in
    fun ?f (h, off as lv) ->
      let no_offset () =
        match R.of_lval ?f lv with
        | `Location (u, _) -> deref_mem u
        | `Value _ | `None ->
          match h with
          | Var vi         -> unless_comp vi.vtype @@ fun () -> w_var vi
          | Mem _          -> Console.fatal "Slice.w_lval: broken invariant: \
                                             Memory accessing lvalue without a location region: %a"
                                pp_lval lv
      in
      match lastOffset off with
      | Field (fi, NoOffset) -> unless_comp fi.ftype R.(fun () -> w_mem ~fi @@ location @@ of_lval ?f lv)
      | Field _              -> assert false
      | Index (_, NoOffset)  -> deref_mem R.(location @@ of_lval ?f lv)
      | Index _              -> assert false
      | NoOffset             -> no_offset ()

  let dummy_flag = Flag.create "slicing_dummy"

  module Make_local
      (F : I.E.Reads) (A : I.E.Assigns with type set = F.t) (C : sig val f : kernel_function option end) = struct

    let f = opt_map Kernel_function.get_name C.f

    let r_mem ?fi u = F.of_writes @@ w_mem ?f ?fi u

    let r_var vi = F.of_writes @@ w_var vi

    let initial_deps assigns =
      let open List in
      let relevant_region = R.relevant_region ?f in
      iter
        (fun (n, rs) ->
           if n >= 1 then
             iter
               (fun r ->
                  let u = U.of_repr r in
                  let F.Some (k1, r1) = r_mem u in
                  let w1 = w_mem ?f u in
                  if relevant_region u then
                    R.dot_voids
                      (fun u ->
                         R.containers_of_void
                           (fun ty u ->
                              if snd @@ Ty.deref ty = n then
                                let F.Some (k2, r2) = r_mem u in
                                let w2 = w_mem ?f u in
                                A.add w1 k2 r2 assigns;
                                A.add w2 k1 r1 assigns)
                           u)
                      u)
               rs)
        (R.all_void_xs ());
      may
        (fun kf ->
           let rv, args = Kernel_function.(get_vi kf, get_formals kf) in
           iter
             (fun vi ->
                match R.of_var ?f vi with
                | `Location (u, _)
                  when not (isStructOrUnionType vi.vtype)
                    && vi.vaddrof                         -> A.add
                                                               (w_mem u) I.E.K.Poly_var (Formal_var.of_varinfo_exn vi)
                                                               assigns
                | `Location _ | `Value _ | `None          -> ())
             args;
           let (ret_ext_regions, param_regions), (ret_int_regions, arg_regions) =
             R.param_regions kf, R.arg_regions ?f kf (Some (var rv)) (map evar args)
           in
           let add_all au pu =
             match unrollType (U.repr au).R.typ with
             | TComp (ci, _, _) when ci.cstruct -> iter
                                                     (fun fi ->
                                                        if not fi.faddrof && isArithmeticOrPointerType fi.ftype then
                                                          let F.Some (k, r) = r_mem ~fi pu in
                                                          A.add (w_mem ~fi au) k r assigns)
                                                     ci.cfields
             | _                                -> ()
           in
           iter2 add_all arg_regions     param_regions;
           iter2 add_all ret_ext_regions ret_int_regions)

    let add_from_lval lv acc = may F.(fun w -> let Some (k, r) = of_writes w in add k r acc) @@ w_lval ?f lv

    class rval_collector = object(self)
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
    end

    class rval_reads_collector acc = object
      inherit frama_c_inplace
      inherit! rval_collector

      method! vlval lv =
        add_from_lval lv acc;
        DoChildren
    end

    let add_from_rval e acc = ignore @@ visitFramacExpr (new rval_reads_collector acc) e

    let add_from_lval lv acc =
      let o = new rval_reads_collector acc in
      match lv with
      | Mem e, off -> ignore @@ visitFramacExpr o e; ignore @@ visitFramacOffset o off
      | Var _, off -> ignore @@ visitFramacOffset o off

    class rval_assigner assigns from = object
      inherit frama_c_inplace
      inherit! rval_collector

      method! vlval lv =
        may (fun w -> A.import_values w from assigns) (w_lval ?f lv);
        DoChildren
    end

    let assign_all e from assigns = ignore @@ visitFramacExpr (new rval_assigner assigns from) e

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
      fun acc m ->
        let F.Some (k, r) = I.M.Poly_mem.prj ~find:(fun u -> R.H_call.find u map) ~mk:r_mem m in
        F.add k r acc

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
                                ~mk:(fun ?fi u -> Some (w_mem ?f ?fi u))
                                m
      | `Result            -> opt_bind (w_lval ?f) lv
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
               let F.Some (k, r) = F.of_writes w_from in
               iter_vertex
                 (fun (_, r_to as v_to) ->
                    if not (Vertex.equal v_from v_to) && F.mem k r r_to then add_edge g v_from v_to)
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

    let comp_assign lv e reads assigns =
        let r_lv, r_e =
          match e.enode with
          | Lval lv' -> R.(location @@ of_lval ?f lv, location @@ of_lval lv')
          | _        -> Console.fatal "Slicing.comp_assign: RHS is not an lval: %a" pp_exp e
        in
        let ci =
          match unrollType @@ typeOf e with
          | TComp (ci, _, _)  -> ci
          | ty                -> Console.fatal "Slicing.comp_assign: RHS is not a composite: %a %a" pp_exp e pp_typ ty
        in
        List.iter
          (fun (path, fi) ->
             let F.Some (k, r) = r_mem ?fi (R.take path r_e) in
             let w = w_mem ?fi @@ R.take path r_lv in
             A.add w k r assigns;
             A.import_values w reads assigns)
          (Ci.all_offsets ci)

    (* Working around the value restriction... *)
    module M = struct
      let reads = F.create dummy_flag

      module M = struct
        let under cont info under s =
          F.clear reads;
          List.iter
            (fun vi -> F.add_local_var (Local_var.of_varinfo_exn vi) reads)
            (I.H_stmt_conds.find info.I.stmt_vars s);
          Stack.iter (fun from -> F.import ~from reads) under;
          cont reads
      end
    end

    include M.M

    let under' info under' s cont = under cont info under' s

    let gassign reads lv ?e assigns =
      add_from_lval lv reads;
      may (fun e -> add_from_rval e reads) e;
      let e = opt_conv (dummy_exp @@ Lval lv) e in
      match w_lval ?f lv with
      | Some w -> A.import_values w reads assigns
      | None   -> comp_assign lv e reads assigns

    let assign = under gassign

    let return = under @@ fun reads ?e assigns ->
      may
        (fun e ->
           add_from_rval e reads;
           match e.enode, unrollType @@ typeOf e with
           | Lval lv, TComp _ -> comp_assign lv e reads assigns
           | _,       TComp _ -> Console.fatal "Slicing.return: composite expression that is not an lvalue: %a" pp_exp e
           | _                -> A.import_values `Result reads assigns)
        e

    let reach_target = under (fun from -> F.import ~from)

    let call info under s = under' info under s @@ fun from ?lv kf depends assigns ->
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
        (fun w from' ->
           may
             (fun w ->
                let reads = A.find w assigns in
                F.import ~from reads;
                prj_reads ~from:from' reads)
             (prj_write w))
        (I.E.assigns eff');
      may
        (fun lv ->
           add_from_lval lv from;
           gassign from lv assigns)
        lv

    let deref ~loc lv = Mem (new_exp ~loc @@ Lval lv), NoOffset

    let alloc = under @@ fun reads ~loc lv ?e assigns ->
      let lv = deref ~loc lv in
      may (fun e -> add_from_rval e reads) e;
      gassign reads lv assigns

    let stub = under @@ fun reads ?lv es assigns ->
      may
        (fun lv ->
           List.iter (fun e -> add_from_rval e reads) es;
           gassign reads lv assigns)
        lv

    let goto info under s = under' info under s @@ fun from assigns ->
      F.import ~from @@ A.find (w_var @@ I.H_stmt.find info.I.goto_vars s) assigns

    let assume = under @@ fun under e assigns ->
      add_from_rval e under;
      assign_all e under assigns

    let is_var_sating p e =
      match (stripCasts e).enode with
      | Lval (Var v, NoOffset) when p v -> true
      | _                               -> false

    class effect_collector info eff =
      let under = Stack.create () in
      let assign       = assign       info under in
      let return       = return       info under in
      let reach_target = reach_target info under in
      let call         = call         info under in
      let alloc        = alloc        info under in
      let stub         = stub         info under in
      let goto         = goto         info under in
      let assume       = assume       info under in
      let assigns = I.E.assigns eff in
      let depends = I.E.depends eff in
      object
        method start = ()
        method finish =
          add_transitive_closure assigns;
          close_depends assigns depends

        inherit frama_c_inplace

        method! vstmt =
          let is_tracking_var v = isVoidPtrType v.vtype && I.E.is_tracking_var (Void_ptr_var.of_varinfo_exn v) eff in
          let start_tracking s lv v arg =
            assign s lv ~e:arg assigns;
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
            | Instr (Set (lv, e, loc))
              when is_var_sating is_tracking_var e                       -> alloc s ~loc lv ~e assigns; SkipChildren
            | Instr (Set (lv, e, _))                                     -> assign s lv ~e assigns;     SkipChildren
            | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _))
              when Options.Target_functions.mem vi.vname                 -> reach_target s depends;     SkipChildren
            | Instr (Call (lvo,
                           { enode = Lval (Var vi, NoOffset) },
                           arg :: _,
                           loc))
              when Options.Alloc_functions.mem vi.vname                  ->
              begin match lvo with
              | Some (Var v, NoOffset as lv) when isVoidPtrType v.vtype  -> start_tracking s lv v arg;  SkipChildren
              | Some lv                                                  -> alloc
                                                                              s ~loc lv ~e:arg assigns; SkipChildren
              | None                                                     ->                             SkipChildren
              end;
            | Instr (Call (_,
                           { enode = Lval (Var vi, NoOffset) }, [e], _))
              when Options.Assume_functions.mem vi.vname                 -> assume s e assigns;         SkipChildren
            | Instr (Call (lv,
                           { enode = Lval (Var vi, NoOffset) },
                           _, _))
              when Kf.mem vi                                             -> call
                                                                              s
                                                                              ?lv
                                                                              (Globals.Functions.get vi)
                                                                              depends
                                                                              assigns;                  SkipChildren
            | Instr (Call (lv,
                           { enode = Lval (Var _, NoOffset) },
                           args, _))                                     -> stub s ?lv args assigns;    SkipChildren
            | Instr (Call (lv, _, args, _))                              -> List.iter
                                                                              (fun kf ->
                                                                                 call
                                                                                   s
                                                                                   ?lv
                                                                                   kf
                                                                                   depends
                                                                                   assigns)
                                                                              (Analyze.filter_matching_kfs
                                                                                 lv args);              SkipChildren
            | Instr (Asm _ | Skip _ | Code_annot _)                      ->                             SkipChildren
            | Return (e, _)                                              -> return s ?e assigns;        SkipChildren
            | Goto _ | AsmGoto _ | Break _ | Continue _                  -> goto s assigns;             SkipChildren
            | If (e, _, _, _) | Switch (e, _, _, _)                      -> do_children_under e
            | Loop _  | Block _ | UnspecifiedSequence _                  -> DoChildren
            | Throw _ | TryCatch _ | TryFinally _ | TryExcept _          -> failwith
                                                                              "Unsupported features: exceptions \
                                                                               and their handling"
      end

    let comp_assign lv mods =
        let r_lv = R.(location @@ of_lval ?f lv) in
        let ci =
          match unrollType @@ typeOfLval lv with
          | TComp (ci, _, _)  -> ci
          | ty                -> Console.fatal "Slicing.comp_assign: LHS is not a composite: %a : %a"
                                   pp_lval lv pp_typ ty
        in
        List.iter
          (fun (path, fi) ->
             let F.Some (k, r) = r_mem ?fi (R.take path r_lv) in
             F.add k r mods)
          (Ci.all_offsets ci)

    include
      (struct
        type 'a reads = F.t
        type verdict = Needed | Not_yet
        type 'b cont = { f : 'a. ('a reads -> verdict) -> 'a reads -> bool ref -> 'b }
        let mods = F.create dummy_flag
        let mod_res = ref false
        let need cont deps result_dep =
          F.clear mods;
          mod_res := false;
          cont.f (fun _ -> if result_dep && !mod_res || F.intersects mods deps then Needed else Not_yet) mods mod_res
      end :
       sig
         type 'a reads = private F.t
         type verdict = private Needed | Not_yet
         type 'b cont = { f : 'a. ('a reads -> verdict) -> 'a reads -> bool ref -> 'b }
         val need : 'b cont -> F.t -> bool -> 'b
       end)

    let gassign decide mods _ lv =
      let cmods = (mods : _ reads :> F.t) in
      begin match w_lval ?f lv with
      | Some w -> F.(let Some (k, r) = of_writes w in add k r cmods)
      | None   -> comp_assign lv cmods
      end;
      decide mods

    let assign = need { f = gassign }

    let return = need { f = fun decide mods mod_res e ->
      let cmods = (mods : _ reads :> F.t) in
      may
        (fun e ->
           match e.enode, unrollType @@ typeOf e with
           | Lval lv, TComp _ -> comp_assign lv cmods
           | _,       TComp _ -> Console.fatal "Slicing.return: composite expression that is not an lvalue: %a" pp_exp e
           | _                -> mod_res := true)
        e;
      decide mods }

    let need' deps cont = need cont deps

    let call info deps = need' deps { f = fun decide mods _ s ?lv kf ->
      let cmods = (mods : _ reads :> F.t) in
      let I.E.Some { reads = (module F');
                     assigns = (module A');
                     eff = eff' } =
        I.get info R.flag @@ Kernel_function.get_definition kf
      in
      let prj_write = prj_write ?lv s in
      let deps' = I.E.depends eff' in
      A'.iter
        (fun w' _ ->
           let result lv =
             may
               (fun w ->
                  let F.Some (k, r) = F.of_writes w in
                  F.add k r cmods;
                  if F.mem k r deps then I.E.add_result_dep eff')
               (w_lval ?f lv)
           in
           match w', lv with
           | `Result,                                Some lv -> result lv
           | `Result,                                None    -> ()
           | (`Local_var _   | `Local_mem _
             | `Poly_var _   | `Poly_mem _
             | `Global_var _ | `Global_mem _ as w'), _       ->
             may
               (fun w ->
                  let F.Some (k, r) = F.of_writes w in
                  F.add k r cmods;
                  if F.mem k r deps then
                    let F'.Some (k', r') = F'.of_writes w' in
                    F'.add k' r' deps')
               (prj_write w'))
        (I.E.assigns eff');
      decide mods }

    let alloc = need { f = fun decide mods mod_res ~loc lv ->
      let lv = deref ~loc lv in
      gassign decide mods mod_res lv }

    let stub = need { f = fun decide mods mod_res lv ->
      may_map (fun lv -> gassign decide mods mod_res lv) ~dft:(decide mods) lv }

    let goto info = need { f = fun decide mods _ s ->
      F.add F.K.Local_var (Local_var.of_varinfo_exn @@ I.H_stmt.find info.I.goto_vars s) (mods : _ reads :> F.t);
      decide mods }

    let assume = need { f = fun decide mods _ e ->
      add_from_rval e (mods : _ reads :> F.t);
      decide mods }

    class marker info eff =
      let deps = I.E.depends eff in
      let result_dep = I.E.has_result_dep eff in
      let assign       = assign    deps result_dep in
      let return       = return    deps result_dep in
      let call         = call info deps result_dep in
      let alloc        = alloc     deps result_dep in
      let stub         = stub      deps result_dep in
      let goto         = goto info deps result_dep in
      let assume       = assume    deps result_dep in
      let assigns = I.E.assigns eff in
      object(self)
        method start = close_depends assigns deps
        method finish = ()

        method add_stmt s = I.E.add_stmt_req s eff
        method add_body f = I.E.add_body_req f eff

        inherit frama_c_inplace
        method! vstmt =
          let is_tracking_var v = isVoidPtrType v.vtype && I.E.is_tracking_var (Void_ptr_var.of_varinfo_exn v) eff in
          fun s ->
            let mark vi =
              self#add_stmt s;
              may
                (fun vi ->
                   try
                     self#add_body (Kernel_function.get_definition @@ Globals.Functions.get vi)
                   with
                   | Kernel_function.No_Definition -> ())
                vi
            in
            let stmt ?vi verdict =
              begin match verdict with
              | Not_yet -> ()
              | Needed  -> mark vi
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
            let stmts stmts =
              if List.exists (fun s -> I.E.has_stmt_req s eff) stmts then
                self#add_stmt s
            in
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
                                                                                  | Needed ->
                                                                                    Some (Kernel_function.get_vi kf)
                                                                                  | Not_yet -> None)
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
            | Throw _ | TryCatch _ | TryFinally _ | TryExcept _          -> failwith
                                                                              "Unsupported features: exceptions \
                                                                               and their handling"
      end
  end
end

(*

let collect_effects break_continue_cache =
  visit_until_convergence
    ~order:`topological
    (new effect_collector break_continue_cache)

class marker file_info def =
  let eff = File_info.get file_info flag def in
  let dummy_flag = Flag.create "marker_dummy" in
  object(self)
    method add_stmt s = Effect.add_stmt_req s eff
    method add_body f = Effect.add_body_req f eff

    method finish =
      let deps = Effect.depends eff in
      let import_reads w = Reads.import ~from:(Effect.reads w eff) deps in
      Reads.iter_global (fun r -> import_reads @@ Writes.Global r) deps;
      Reads.iter_poly (fun v -> import_reads @@ Writes.Poly v) deps;
      Reads.iter_local (fun v -> import_reads @@ Writes.Local v) deps

    inherit frama_c_inplace
    method! vstmt =
      let handle_call ~s lvo fundec params =
        let mark () = self#add_body fundec; self#add_stmt s in
        let eff' = File_info.get file_info flag fundec in
        (* first project writes *)
        let writes = Effect.shallow_copy_writes dummy_flag eff' in
        H_write.filter_map_inplace
          ~check:false
          (fun w reads ->
             match w with
             | Writes.Global r ->
               if Reads.mem Reads.Global r (Effect.depends eff) then Some reads else None
             | Writes.Result when has_some lvo ->
               let r = Reads.create dummy_flag in
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
          let reads = Reads.create dummy_flag in
          H_write.iter (fun _ from -> Reads.import ~from reads) writes;
          project_reads ~fundec ~params ~from:reads (Effect.depends eff);
          may
            (fun lv ->
               let r = Reads.create dummy_flag in
               add_from_lval lv r;
               if Reads.intersects (Effect.depends eff) r then add_rval_from_lval lv (Effect.depends eff))
            lvo;
          mark ()
        end
      in
      let handle_assignment =
        let r = Reads.create dummy_flag in
        fun ~s ~lv ~from ->
          Reads.clear r;
          lv r;
        if Reads.intersects (Effect.depends eff) r then begin
          from (Effect.depends eff);
          self#add_stmt s
        end;
        SkipChildren
      in
      let handle_stmt_list ~s stmts =
        if List.exists (fun s -> Effect.has_stmt_req s eff) stmts then
          self#add_stmt s
      in
      let handle_goto_block ~s =
        let check =
          let checker = object
            inherit frama_c_inplace
            method! vstmt s =
              match s.skind with
              | Break _ | Continue _ -> SkipChildren
              | _ when Effect.has_stmt_req s eff -> raise Exit
              | _ -> DoChildren
          end in
          fun b ->
          try ignore @@ visitFramacBlock checker b; false with Exit -> true
        in
        let mark =
          let marker = object
            inherit frama_c_inplace
            method! vstmt s =
              match s.skind with
              | Break _ | Continue _ ->
                self#add_stmt s;
                SkipChildren
              | If (_, block1, block2, _) ->
                DoChildrenPost (fun s -> handle_stmt_list ~s @@ block1.bstmts @ block2.bstmts; s)
              | Switch (_, block, _, _) ->
                DoChildrenPost (fun s -> handle_stmt_list ~s block.bstmts; s)
              | Loop (_, block, _, _, _)
              | Block block ->
                DoChildrenPost (fun s -> handle_stmt_list ~s block.bstmts; s)
              | UnspecifiedSequence l ->
                DoChildrenPost (fun s -> handle_stmt_list ~s @@ List.map (fun (s, _ ,_ ,_, _) -> s) l; s)
              | _ -> DoChildren
          end in
          ignore % visitFramacBlock marker
        in
        fun b -> if check b then begin mark b; self#add_stmt s end
      in
      let alloc_to ~s ~loc ~lv ~from =
        let lv = Mem (new_exp ~loc @@ Lval lv), NoOffset in
        handle_assignment ~s ~lv:(add_from_lval lv) ~from:(fun r -> from r; add_rval_from_lval lv r)
      in
      let is_tracking_var v = isVoidPtrType v.vtype && Effect.is_tracking_var (Void_ptr_var.of_varinfo_exn v) eff in
      fun s ->
        match s.skind with
        | Instr (Set (lv, e, loc)) when is_var_sating is_tracking_var e ->
          alloc_to ~s ~loc ~lv ~from:(add_from_rval e)
        | Instr (Set (lv, e, _)) ->
          handle_assignment ~s ~lv:(add_from_lval lv) ~from:(add_from_rval_and_lval lv e)
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
          | Some (Var v, NoOffset as lv)
            when isVoidPtrType v.vtype && Effect.is_tracking_var (Void_ptr_var.of_varinfo_exn v) eff ->
            handle_assignment ~s ~lv:(add_from_lval lv) ~from:ignore
          | Some lv -> alloc_to ~s ~loc ~lv ~from:ignore
          | None -> SkipChildren
          end
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, [e], _)) when Options.Assume_functions.mem vi.vname ->
          handle_assignment ~s ~lv:(add_from_rval e) ~from:ignore
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
          may (fun e -> if Effect.has_result_dep eff then add_from_rval e (Effect.depends eff)) eo;
          SkipChildren
        | Goto _ ->
          self#add_stmt s;
          SkipChildren
        | Break _ | Continue _ ->
          SkipChildren
        | If (_, block1, block2, _) ->
          DoChildrenPost (fun s -> handle_stmt_list ~s @@ block1.bstmts @ block2.bstmts; s)
        | Switch (_, block, _, _) ->
          DoChildrenPost (fun s -> handle_goto_block ~s block; s)
        | Loop (_, block, _, _, _) ->
          DoChildrenPost (fun s -> handle_goto_block ~s block; s)
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
