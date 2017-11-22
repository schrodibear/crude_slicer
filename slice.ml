(******************************************************************************)
(* Copyright (c) 2014-2017 ISPRAS (http://www.ispras.ru)                      *)
(* Institute for System Programming of the Russian Academy of Sciences        *)
(*                                                                            *)
(* Licensed under the Apache License, Version 2.0 (the "License");            *)
(* you may not use this file except in compliance with the License.           *)
(* You may obtain a copy of the License at                                    *)
(*                                                                            *)
(*     http://www.apache.org/licenses/LICENSE-2.0                             *)
(*                                                                            *)
(* Unless required by applicable law or agreed to in writing, software        *)
(* distributed under the License is distributed on an "AS IS" BASIS,          *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.   *)
(* See the License for the specific language governing permissions and        *)
(* limitations under the License.                                             *)
(******************************************************************************)

[@@@warning "-4-9-42-44-45-48"]

open Extlib

open Cil_types
open Cil_datatype
open Cil
open Cil_printer
open Visitor

open Info
open! Common

module Make (Analysis : Region.Analysis) = struct

  module I = Analysis.I

  let unless_comp ty f =
    let ty = Ty.normalize ty in
    if not (isStructOrUnionType ty || isVoidType ty) then Some (f ()) else None

  let deref =
    let module H = Lval.Hashtbl in
    let h = H.create 64 in
    fun ~loc lv -> H.memo h lv @@ fun lv -> Mem (new_exp ~loc @@ Lval lv), NoOffset

  let rec fold_init f acc lv =
    function
    | SingleInit e            -> f acc lv e
    | CompoundInit (_, inits) -> List.fold_left
                                   (fun acc (off, init) -> fold_init f acc (addOffsetLval off lv) init)
                                   acc
                                   inits

  let is_var_sating p e =
    match (stripCasts e).enode with
    | Lval (Var v, NoOffset) when p v -> true
    | _                               -> false

  let dummy_flag = Flag.create "slicing_dummy"

  let callee_approx = Analysis.callee_approx

  let new_callee_approx = Exp.List_hashtbl.(may_map copy ~dft:(create 16) callee_approx)

  module Make_local
      (C : sig val f : kernel_function end)
      (L : I.E.Local) = struct

    let f = Kernel_function.get_name C.f

    module R = struct
      include Analysis.R
      include Analysis
      let of_var,    of_lval,    of_expr,    relevant_region,    arg_regions =
        of_var ~f, of_lval ~f, of_expr ~f, relevant_region ~f, arg_regions ~f
    end
    module U = Analysis.U

    module F = L.R
    module A = L.A
    module G = I.G
    module W = L.W
    open L.F

    let w_var vi =
      match isArithmeticOrPointerType vi.vtype, vi.vglob, vi.vformal with
      | true, true,  false -> `Global_var (G.Var.of_varinfo vi)
      | true, false, true  -> `Poly_var   (Poly.Var.of_varinfo vi)
      | true, false, false -> `Local_var  (Local.Var.of_varinfo vi)
      | false, _,    _     -> Console.fatal
                                "Slice.w_var: broken invariant: \
                                 trying to write to composite variable without region: %a"
                                pp_varinfo vi
      | true, glob,  frml  -> Console.fatal
                                "Slice.w_var: broken invariant: inconsistent varinfo: %a: .vglob=%B, .vformal=%B"
                                pp_varinfo vi  glob frml

    let w_mem ?fi u =
      match (U.repr u).R.kind with
      | `Global                          -> `Global_mem (G.Mem.mk ?fi u)
      | `Local f' when String.equal f f' -> `Local_mem  (Local.Mem.mk ?fi u)
      | `Poly f'  when String.equal f f' -> `Poly_mem   (Poly.Mem.mk ?fi u)
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

    let unwrap (I.E.Some { local = (module L'); eff }) : (A.t, F.t) I.E.t =
      match L'.R.W, L'.A.W with
      | F.W, A.W -> eff
      | _        -> Console.fatal "Slice.unpack: broken invariant: got effect of a different function"

    let r_mem ?fi u = F.of_write @@ w_mem ?fi u

    let r_var vi = F.of_write @@ w_var vi

    let extract info = unwrap @@ I.get info R.flag (Kernel_function.get_definition C.f)

    let init_deps info () =
      let assigns = I.E.assigns @@ extract info in
      let open List in
      iter
        (fun vi ->
           match R.of_var vi with
           | `Location (u, _)
             when not (isStructOrUnionType vi.vtype)
               && vi.vaddrof                         -> A.add
                                                          (w_mem u) F.Poly_var (Poly.Var.of_varinfo vi)
                                                          assigns
           | `Location _ | `Value _ | `None          -> ())
        (Kernel_function.get_formals C.f);
      iter
        (fun (offs, au, pu) ->
           iter
             (fun (path, fi) -> A.add_some (w_mem ?fi @@ R.take path au) (r_mem ?fi @@ R.take path pu) assigns)
             offs)
        (R.initial_deps C.f)

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
        | Instr
            (Call (_, _, args, _)
            | Local_init (_, ConsInit (_, args, Plain_func), _)) -> args
        | _                                                      -> Console.fatal "Slice.project_reads: need a proper \
                                                                                   function call site: %a"
                                                                      pp_stmt s
      in
      let open List in
      let args = take (length params) args in
      let add_from_arg = combine params @@ map add_from_rval args in
      fun acc fv -> assoc fv add_from_arg acc

    let prj_poly_mem ~prj s kf =
      let map = R.map s kf in
      fun acc m -> F.add_some (prj ~find:(fun u -> R.H_map.find u map) ~mk:r_mem m) acc

    let prj_reads (type a r) (module L' : I.E.Local with type A.t = a and type R.t = r) s kf =
      let prj_poly_var = prj_poly_var s (Kernel_function.get_formals kf) in
      let prj_poly_mem = prj_poly_mem s kf in
      fun ~from acc ->
        L'.R.iter_global_vars (fun v -> F.add_global_var v acc) from;
        L'.R.iter_poly_vars   ((prj_poly_var :> F.t -> L'.F.Poly.Var.t -> unit) acc) from;
        L'.R.iter_global_mems (fun mem -> F.add_global_mem mem acc) from;
        L'.R.iter_poly_mems   (prj_poly_mem ~prj:L'.F.Poly.Mem.prj acc) from

    let prj_write ~prj ?lv s kf =
      function
      | `Global_var _
      | `Global_mem _ as w -> Some w
      | `Poly_mem m        -> prj ~find:(fun u -> R.H_map.find u @@ R.map s kf) ~mk:(fun ?fi u -> Some (w_mem ?fi u)) m
      | `Result            -> opt_bind w_lval lv
      | `Poly_var _
      | `Local_var _
      | `Local_mem _       -> None

    (* Incomplete, but suitable for fix-point iteration approach *)
    let add_transitive_closure =
      let module Vertex = struct
        type t = W.t * F.t
        let compare (a, _) (b, _) = W.compare a b
        let equal (a, _) (b, _) = W.equal a b
        let hash (x, _) = W.hash x
      end in
      let module Deps = Graph.Imperative.Digraph.Concrete (Vertex) in
      let module Sccs = Graph.Components.Make (Deps) in
      let open Deps in
      fun assigns ->
        let g = create () in
        A.iter (fun w r -> add_vertex g (w, r)) assigns;
        iter_vertex
          (fun (w_from, _ as v_from) ->
             match w_from with
             | `Result               -> ()
             | #W.readable as w_from ->
               iter_vertex
                 (fun (_, r_to as v_to) ->
                    if not (Vertex.equal v_from v_to) &&
                       F.(mem_some (of_write w_from) r_to) then
                      add_edge g v_from v_to)
                 g)
          g;
        let open List in
        let sccs = rev @@ Sccs.scc_list g in
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
        F.iter import_reads reads;
        if result_dep then import_reads `Result

    module type Actions = sig
      val start : unit -> unit
      val finish : unit -> unit
      val is_tracking_var : varinfo -> bool
      val start_tracking : stmt -> lval -> varinfo -> exp -> unit
      val assign : stmt -> lval -> exp -> unit
      val init : stmt -> lval -> init -> unit
      val return : stmt -> exp option -> unit
      val call : stmt -> ?lv:lval -> ?e:exp -> kernel_function -> unit
      val stub : stmt -> ?lv:lval -> ?e:exp -> exp list -> unit
      val alloc : stmt -> lval -> exp -> unit
      val goto : stmt -> unit
      val reach_target : stmt -> unit
      val assume : stmt -> exp -> unit
      val unreach : stmt -> unit
      val if_ : stmt -> exp -> block -> block -> stmt visitAction
      val switch : stmt -> exp -> block -> stmt visitAction
      val block : stmt -> block -> stmt visitAction
      val unordered : stmt -> (stmt * lval list * lval list * lval list * stmt ref list) list -> stmt visitAction
    end

    let visitor (module M : Actions) =
      let open M in
      let dcall s ?lv f args =
        match Globals.Functions.get f with
        | kf when Kernel_function.is_definition kf -> call s ?lv kf
        | _                                        -> stub s ?lv args
        | exception Not_found                      -> stub s ?lv args
      in
      let alloc' s ?lv f arg args =
        let call () = dcall s ?lv f (arg :: args) in
        begin match lv with
        | Some (Var v, NoOffset as lv) when isVoidPtrType v.vtype ->(start_tracking s lv v arg;
                                                                     call ())
        | Some lv when not (isVoidPtrType @@ typeOfLval lv)       ->(alloc s lv arg;
                                                                     call ())
        | Some _                                                  -> call ()
        (* ^^^ Unsound! Struct fields should be supported as tracking fields!
            Or full support for reinterpretation should be implemented.    *)
        | None                                                    -> ()
        end;
      in
      let icall s ?lv e args =
        let kfs = Analyze.callee_approx ?callee_approx e in
        Exp.(List_hashtbl.replace new_callee_approx (underef_mem e) []);
        match kfs with
        | []  -> stub s ?lv args
        | kfs -> List.iter
                   (fun kf ->
                      if Kernel_function.is_definition kf
                      then call s ?lv ~e kf
                      else stub s ?lv ~e args)
                   kfs
      in
      object
        method start = start ()
        method finish = finish ()

        inherit frama_c_inplace

        method! vstmt s =
          match s.skind with
          | Instr (Set ((Var v, NoOffset as lv), e, _))
            when isVoidPtrType v.vtype
              && is_var_sating is_tracking_var e                       -> start_tracking s lv v e;      SkipChildren
          | Instr (Set (lv, e, _))
            when is_var_sating is_tracking_var e
              && not (isVoidPtrType @@ typeOfLval lv)                  -> alloc s lv e;                 SkipChildren
          | Instr (Set (lv, e, _))                                     -> assign s lv e;                SkipChildren
          | Instr (Local_init (vi, AssignInit i, _))                   -> init s (var vi) i;            SkipChildren
          | Instr (Call
                     (_,
                      { enode = Lval (Var f, NoOffset); _ },
                      _, _))
            when Options.Target_functions.mem f.vname                  -> reach_target s;               SkipChildren
          | Instr (Call
                     (lv,
                      { enode = Lval (Var f, NoOffset) },
                      (arg :: args), _))
            when Options.Alloc_functions.mem f.vname                   -> alloc' s ?lv f arg args;      SkipChildren
          | Instr (Local_init
                     (vi, ConsInit (f, arg :: args, Plain_func), _))
            when Options.Alloc_functions.mem f.vname                   -> alloc'
                                                                            s
                                                                            ~lv:(var vi)
                                                                            f
                                                                            arg
                                                                            args;                       SkipChildren

          | Instr (Call (_,
                         { enode = Lval (Var f, NoOffset) }, [e], _))
            when Options.Assume_functions.mem f.vname                  -> assume s e;                   SkipChildren
          | Instr (Call (_,
                         { enode = Lval (Var f, NoOffset) }, [], _))
            when Options.Path_assume_functions.mem f.vname             -> unreach s;                    SkipChildren
          | Instr (Call (lv,
                         { enode = Lval (Var f, NoOffset) },
                         args, _))                                     -> dcall s ?lv f args;           SkipChildren
          | Instr (Local_init (vi, ConsInit (f, args, Plain_func), _)) -> dcall s ~lv:(var vi) f args;  SkipChildren
          | Instr (Call (lv, e, args, _))                              -> icall s ?lv e args;           SkipChildren
          | Instr (Local_init (_, ConsInit (_, _, Constructor), _) )   -> Console.fatal
                                                                            "collector: C++ constructors \
                                                                             are unsupported"
          | Instr (Asm _ | Skip _ | Code_annot _)                      ->                               SkipChildren
          | Return (e, _)                                              -> return s e;                   SkipChildren
          | Goto _ | AsmGoto _ | Break _ | Continue _                  -> goto s;                       SkipChildren
          | If (e, b1, b2, _)                                          -> if_ s e b1 b2
          | Switch (e, b, _, _)                                        -> switch s e b
          | Loop (_, b, _, _, _) | Block b                             -> block s b
          | UnspecifiedSequence ss                                     -> unordered s ss
          | Throw _ | TryCatch _ | TryFinally _ | TryExcept _          -> Console.fatal
                                                                            "Unsupported features: exceptions \
                                                                             and their handling"
      end

    module type Info = sig val info : I.t end

    module type From = sig
      val info : I.t
      val from : stmt -> F.t
      val do_children_under : exp -> stmt visitAction
    end

    module From (M : Info) : From = struct
      include M
      let under = Stack.create ()
      let from =
        let from = F.create dummy_flag in
        fun s ->
          F.clear from;
          List.iter
            (fun vi -> F.add_local_var (Local.Var.of_varinfo vi) from)
            (H_stmt_conds.find_all M.info.stmt_vars s);
          Stack.iter (fun from' -> F.import ~from:from' from) under;
          from

      let do_children_under e =
        let r = F.create dummy_flag in
        add_from_rval e r;
        Stack.push r under;
        DoChildrenPost (fun s -> ignore @@ Stack.pop under; s)
    end

    module Eff (M : Info ) = struct
      let eff = extract M.info
      open I.E
      let assigns = assigns eff
      let depends = depends eff
      let has_result_dep () = has_result_dep eff
      let has_stmt_req s = has_stmt_req s eff
      let add_stmt_req s = add_stmt_req s eff
      let has_body_req f = has_body_req f eff
      let add_body_req f = add_body_req f eff
      let set_is_target () = set_is_target eff
      let is_tracking_var v = isVoidPtrType v.vtype && is_tracking_var (Void_ptr_var.of_varinfo v) eff
      let add_tracking_var v = add_tracking_var v eff
    end

    module Collect (M : From) : Actions = struct
      open M
      include Eff (M)

      let start () = ()
      let finish =
        let add_transitive_closure () = add_transitive_closure assigns in
        let close_depends () = close_depends assigns depends (has_result_dep ()) in
        let complement () = complement assigns depends in
        fun () ->
          add_transitive_closure ();
          close_depends ();
          complement ()

      let comp_assign lv e from =
        let r_lv, r_e =
          match e.enode with
          | Lval lv' -> R.(location @@ of_lval lv, location @@ of_lval lv')
          | _        -> Console.fatal "Slicing.comp_assign: RHS is not an lval: %a" pp_exp e
        in
        let ci =
          match Ty.unbracket @@ unrollType @@ typeOf e with
          | TComp (ci, _, _) -> ci
          | ty               -> Console.fatal "Slicing.comp_assign: RHS is not a composite: %a %a" pp_exp e pp_typ ty
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
      let init s = fold_init (const @@ assign s) ()
      let return s eo =
        let from = from s in
        may
          (fun e ->
             add_from_rval e from;
             match unrollType @@ typeOf e with
             | TComp _ -> comp_assign (var @@ R.retvar @@ Kernel_function.get_vi C.f) e from
             | _       -> A.import_values `Result from assigns)
          eo

      let start_tracking s lv v arg =
        assign s lv arg;
        add_tracking_var @@ Void_ptr_var.of_varinfo v

      let call s ?lv ?e kf =
        let from = from s in
        may (fun e -> add_from_rval e from) e;
        let I.E.Some { local = (module L') as local; eff = eff' } =
          I.get info R.flag @@ Kernel_function.get_definition kf
        in
        let prj_reads = prj_reads local s kf in
        let prj_write = prj_write ?lv s kf in
        if I.E.is_target eff' then begin
          F.import ~from depends;
          prj_reads ~from:(I.E.depends eff') depends;
          set_is_target ()
        end;
        L'.A.iter
          (fun w' from' ->
             may
               (fun w ->
                  let reads = A.find w assigns in
                  F.import ~from reads;
                  prj_reads ~from:from' reads)
               (prj_write ~prj:L'.F.Poly.Mem.prj w'))
          (I.E.assigns eff');
        may
          (fun lv ->
             add_from_lval lv from;
             gassign lv from)
          lv
      let stub s ?lv ?e es =
        let from = from s in
        may (fun e -> add_from_rval e from) e;
        may
          (fun lv ->
             List.iter (fun e -> add_from_rval e from) es;
             gassign lv from)
          lv
      let alloc s lv e =
        let from = from s in
        let lv' = deref ~loc:(Stmt.loc s) lv in
        add_from_rval e from;
        gassign lv from;
        gassign lv' from

      let goto s = F.import ~from:(from s) @@ A.find (w_var @@ H_stmt.find info.goto_vars s) assigns
      let reach_target s =
        F.import ~from:(from s) depends;
        set_is_target ()
      let import_trans ~from =
        let from' = F.copy dummy_flag from in
        F.iter (fun r -> F.import ~from:(A.find r assigns) from') from;
        F.iter (fun w -> A.import_values w from' assigns) from'
      let assume s e =
        let from = from s in
        add_from_rval e from;
        assign_all e from assigns;
        import_trans ~from
      let unreach s =
        let from = from s in
        import_trans ~from

      let if_ _ e _ _ = do_children_under e
      let switch _ e _ = do_children_under e
      let block _ _ = DoChildren
      let unordered = block
    end

    let collector info = visitor (module Collect (From (struct let info = info end)))

    module type Decide = sig
      val info : I.t
      val mark : ?kf:kernel_function -> stmt -> unit
      val decide : stmt -> ?kf:kernel_function -> [< W.t] list -> unit
      val surround : stmt -> stmt list -> unit
    end

    module Decide (M : sig val info : I.t end) : Decide = struct
      include M
      include Eff (M)

      let mark =
        let add_body_req kf = Kernel_function.(try add_body_req @@ get_definition kf with No_Definition -> ()) in
        fun ?kf s ->
          add_stmt_req s;
          match s.skind with
          | Instr (Call (_, { enode = Lval (Var vi, NoOffset); _ }, _, _))
          | Instr (Local_init (_, ConsInit (vi, _, Plain_func), _))        -> add_body_req (Globals.Functions.get vi)
          | Instr (Call (_, e, _, _))
            when has_some kf                                               ->(let e = Exp.underef_mem e in
                                                                              Exp.List_hashtbl.(
                                                                                replace
                                                                                  new_callee_approx
                                                                                  e
                                                                                  (the kf ::
                                                                                   find_all new_callee_approx e)))
          | _                                                              -> ()

      let decide s ?kf =
        let intersects =
          let reads = F.create dummy_flag in
          fun l ->
            F.clear reads;
            List.iter
              (function
              | `Result          -> ()
              | #W.readable as w -> F.(add_some (of_write w) reads))
              l;
            F.intersects reads depends
        in
        let rec mem_result =
          function
          | []           -> false
          | `Result :: _ -> true
          | #W.t  :: xs  -> mem_result xs
        in
        function
        | []                                     -> ()
        | [`Result]
          when has_result_dep ()                 -> mark ?kf s
        | [`Result]                              -> ()
        | [#W.readable as w]
          when F.(mem_some (of_write w) depends) -> mark ?kf s
        | [#W.readable]                          -> ()
        | (l : [< W.t] list)
          when has_result_dep () && mem_result l
            || intersects l                      -> mark ?kf s
        | _                                      -> ()

      let surround s stmts = if List.exists has_stmt_req stmts then add_stmt_req s
    end

    module Mark (M : Decide) : Actions = struct
      open M
      include Eff (M)

      let start () =
        let close_depends () = close_depends assigns depends (has_result_dep ()) in
        let complement () = complement assigns depends in
        close_depends ();
        complement ()
      let finish () = ()

      let comp_assign lv =
        let r_lv = R.(location @@ of_lval lv) in
        let ci =
          match Ty.unbracket @@ unrollType @@ typeOfLval lv with
          | TComp (ci, _, _)  -> ci
          | ty                -> Console.fatal "Slicing.comp_assign: LHS is not a composite: %a : %a"
                                   pp_lval lv pp_typ ty
        in
        List.map (fun (path, fi) -> w_mem ?fi @@ R.take path r_lv) (Ci.offsets ci)
      let gassign lv = match w_lval lv with Some w -> [w] | None -> comp_assign lv
      let assign s = const' @@ decide s % gassign
      let init s = decide s %% fold_init (const @@ const' gassign) []
      let return s eo =
        decide s @@
        may_map
          (fun e ->
             match e.enode, unrollType @@ typeOf e with
             | Lval lv, TComp _ -> comp_assign lv
             | _,       TComp _ -> Console.fatal "Slicing.return: composite expression that is not an lvalue: %a"
                                     pp_exp e
             | _                -> [`Result])
          ~dft:[]
          eo

      let start_tracking = ignore4

      let call s ?lv ?e:_ kf =
        let I.E.Some { local = (module L');
                       eff = eff' } =
          I.get info R.flag @@ Kernel_function.get_definition kf
        in
        let prj_write = prj_write ?lv s kf in
        let deps' = I.E.depends eff' in
        let may_push_and_cons f =
          opt_fold @@ List.cons % tap (fun w -> if F.(mem_some (of_write w) depends) then f ())
        in
        let writes =
          L'.A.fold
            (fun w' _ ->
               match w', lv with
               | `Result,                Some lv -> may_push_and_cons
                                                      (fun () -> I.E.add_result_dep eff')
                                                      (w_lval lv)
               | `Result,                None    -> id
               | (#L'.W.readable as w'), _       -> may_push_and_cons
                                                      L'.R.(fun () -> add_some (of_write w') deps')
                                                      (prj_write ~prj:L'.F.Poly.Mem.prj w'))
            (I.E.assigns eff')
            []
        in
        if I.E.is_target eff' then mark ~kf s else decide s ~kf writes
      let stub s ?lv ?e:_ _ = may (decide s % gassign) lv
      let alloc s lv _ = decide s @@ gassign lv @ gassign (deref ~loc:(Stmt.loc s) lv)

      let goto s = decide s [`Local_var (Local.Var.of_varinfo @@ H_stmt.find info.goto_vars s)]
      let reach_target s = mark s
      let assume s e =
        let r = ref [] in
        visit_rval (fun lv -> may (fun w -> r := w :: !r) @@ w_lval lv) e;
        decide s !r
      let unreach s = mark s

      let block s b = surround s b.bstmts
      let if_ s _ b1 b2 = DoChildrenPost (fun s' -> block s b1; block s b2; s')
      let block s b = DoChildrenPost (fun s' -> block s b; s')
      let switch s _ = block s
      let unordered s ss = DoChildrenPost (fun s' -> surround s @@ List.map (fun (s, _, _, _, _) -> s) ss; s')
    end

    let marker info = visitor (module Mark (Decide (struct let info = info end)))

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
        opt_bind (filter @@ var v) init
  end

  module Make (M : sig val info : I.t end) = struct
    open M

    module Fixpoint = Fixpoint.Make (I)

    module H = H_fundec

    let collectors, markers, initializers, filters = H.create 512, H.create 512, H.create 512, H.create 512

    let () =
      Globals.Functions.iter_on_fundecs
        (fun d ->
           let I.E.Some { local = (module L); _ } = I.get info Analysis.R.flag d in
           let module L = Make_local (struct let f = Globals.Functions.get d.svar end) (L) in
           H.replace collectors d @@ L.collector info;
           H.replace markers d @@ L.marker info;
           H.replace initializers d @@ L.init_deps info;
           H.replace filters d @@ L.filter_init info)

    let collect = Fixpoint.visit_until_convergence ~order:`topological (const @@ H.find collectors) info
    let mark =    Fixpoint.visit_until_convergence ~order:`reversed    (const @@ H.find markers) info

    let init sccs =
      Console.debug "Started init (init_deps for every function)...";
      Kernel_function.(
        List.iter
          (fun kf ->
             match get_definition kf with
             | d                       -> H.find initializers d ()
             | exception No_Definition -> ())
          (List.flatten sccs))

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

    module H_int = Datatype.Int.Hashtbl

    class sweeper () =
      let required_bodies, main_def, main_filter =
        let open Kernel_function in
        let result = H.create 256 in
        H.(iter
             (fun _ -> I.E.iter_body_reqs @@ fun f -> replace result f ())
             info.effects);
        List.iter
          (fun kf ->
             try                H.replace result (get_definition kf) ()
             with
             | No_Definition -> ())
          (Analyze.get_addressed_kfs ());
        match get_definition @@ Globals.Functions.find_by_name @@ Kernel.MainFunction.get () with
        | d                  -> H.add result d (); result, Some d, Some (H.find filters d)
        | exception
            (Not_found
            | No_Definition) ->                    result, None, None
      in
      let () = may (fun approx -> Exp.List_hashtbl.(clear approx; iter (add approx) new_callee_approx)) callee_approx in
      let irrelevant_lines = H_int.create 2048 in
      let del_stmt, del_var =
        let del_loc ?no (start, stop) =
          for i = start.Lexing.pos_lnum to stop.Lexing.pos_lnum do
            H_int.replace irrelevant_lines i no
          done
        in
        (fun s ->
           match s.skind with
           | Goto (_, loc)
             when H_stmt.mem info.goto_next s -> del_loc
                                                   ~no:(fst @@
                                                        Stmt.loc @@
                                                        H_stmt.find info.goto_next s).Lexing.pos_lnum
                                                   loc
           | Instr (Local_init (vi, _, loc))  ->(vi.vdefined <- false;
                                                 del_loc loc)
           | _                                -> del_loc (Stmt.loc s)),
        del_loc ?no:None
      in
      object(self)
        val mutable eff = I.E.create dummy_flag (emptyFunction "")

        method iter_irrelevant_lines f = H_int.iter f irrelevant_lines

        inherit frama_c_inplace

        method! vfunc f =
          let name = f.svar.vname in
          if Options.(Alloc_functions.mem name
                      || Assume_functions.mem name
                      || Path_assume_functions.mem name
                      || Target_functions.mem name)
          then                                  SkipChildren
          else (eff <- I.get info dummy_flag f; DoChildren)

        method! vstmt_aux s =
          let skip () = { s with skind = Instr (Skip (Stmt.loc s)); labels = collect_labels s } in
          if not (I.E.has_stmt_req' s eff)
          && not (opt_equal Fundec.equal main_def self#current_func && match s.skind with Return _ -> true | _ -> false)
          then begin
            del_stmt s;
            if Options.Use_ghosts.is_set ()
            then (s.ghost <- true;                          DoChildren)
            else                                            ChangeTo (skip ())
          end else
            match s.skind with
            | Instr (Local_init (vi, AssignInit init, loc)) ->
              begin match (H.find filters (the self#current_func)) vi (Some init) with
              | Some init                                -> ChangeTo
                                                              { s with
                                                                skind = Instr (Local_init (vi, AssignInit init, loc)) }
              | None                                     ->(del_stmt s;
                                                            ChangeTo (skip ()))
              end
            | _                                          -> DoChildren

        method! vblock _ = DoChildrenPost (tap shrink_block)

        method! vglob_aux g =
          match g, main_filter with
          | GFun (f, _),          _
            when not (H.mem required_bodies f)     ->                                        ChangeTo []
          | GVar (vi, init, loc), Some main_filter ->(init.init <- main_filter vi init.init;
                                                      if init.init = None then
                                                        del_var loc;                         SkipChildren)
          | _                                      ->                                        DoChildren
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

    let sweep ?after_sweeping_funcs () =
      let file = Ast.get () in
      let sweeper = new sweeper () in
      visitFramacFile (sweeper :> frama_c_visitor) file;
      let oslice = Options.Oslice.get () in
      if oslice <> "" then
        Command.pp_to_file
          oslice
          Pretty_utils.(Format.(fun fmt ->
            pp_iter2
              ~sep:"\n"
              ~between:","
              (const' sweeper#iter_irrelevant_lines)
              pp_print_int
              (pp_opt ~pre:"" pp_print_int)
              fmt ()));
      visitFramacFile (new cfg_fixupper ()) file;
      Cfg.clearFileCFG ~clear_id:false file;
      Cfg.computeFileCFG file;
      may (fun callee_approx -> Function_pointers.rewrite ~callee_approx) callee_approx;
      Rmtmps.removeUnusedTemps
        ~isRoot:(
          function
          | GFun (f, _) when f.svar.vname = Kernel.MainFunction.get () -> true
          | GCompTag _ | GVar _ | GVarDecl _                           -> true
          | _                                                          -> false)
        file;
      may ((|>) ()) after_sweeping_funcs;
      Rmtmps.removeUnusedTemps
        ~isRoot:(function
        | GFun (f, _) when f.svar.vname = Kernel.MainFunction.get ()
                        || hasAttribute Kf.stub_attr f.svar.vattr    -> true
        | _                                                          -> false)
        file

    let clear () =
      Analysis.clear ();
      I.clear info
  end
end

let slice () =
  Console.debug "Started slicing...";
  let offs_of_key = Info.H_field.create 2048 in
  Analyze.cache_offsets ~offs_of_key;
  Console.debug "Stage 1...";
  let large_file = Globals.Functions.fold (const ((+) 1)) 0 > Options.Widening_threshold.get () in
  let module Region_analysis1 =
    Region.Analysis
      (struct
        let offs_of_key   = offs_of_key
        let callee_approx = None
        let region_length, region_depth, region_count = 1, 1, 2
        let mode = `Global
        let widen = false
        let assert_stratification = Options.Assert_stratification.get ()
        let recognize_container_of2 = Options.Recognize_wrecked_container_of.get ()
      end)
      ()
  in
  let module Transform = Transform.Make (Region_analysis1) in
  Transform.rewrite ();
  Region_analysis1.compute_regions ();
  let module Function_pointer_analysis = Function_pointers.Make (Region_analysis1) in
  let callee_approx = Function_pointer_analysis.approx () in
  Console.debug "Stage 2...";
  Region_analysis1.clear ();
  Gc.full_major ();
  let module Region_analysis2 =
    Region.Analysis
      (struct
        let offs_of_key   = offs_of_key
        let callee_approx = Some callee_approx
        let        region_length,        region_depth,        region_count =
          Options.(Region_length.get (), Region_depth.get (), Region_count.get ())
        let mode = `Poly_rec
        let widen = large_file
        let assert_stratification = Options.Assert_stratification.get ()
        let recognize_container_of2 = Options.Recognize_wrecked_container_of.get ()
      end)
      ()
  in
  let info = Region_analysis2.I.create () in
  Analyze.fill_goto_tables info;
  Region_analysis2.compute_regions ();
  let module Slice = Make (Region_analysis2) in
  let module Info = struct let info = info end in
  let module Slice = Slice.Make (Info) in
  let sccs = Analyze.condensate ~callee_approx () in
  Slice.init sccs;
  Console.debug "Will now collect assigns and deps...";
  Slice.collect sccs;
  Console.debug "Will now mark...";
  Slice.mark sccs;
  Console.debug "Will now sweep and generate summaries...";
  let module Summaries = Summaries.Make (Region_analysis2) (Info) in
  Slice.sweep ~after_sweeping_funcs:(fun () -> if Options.Summaries.get () then Summaries.generate sccs) ();
  let stat = Gc.stat () in
  Console.debug  "Current # of live words: %d" stat.Gc.live_words;
  Console.debug "Will now clean...";
  Slice.clear ();
  Gc.full_major ();
  let stat = Gc.stat () in
  Console.debug  "Current # of live words: %d" stat.Gc.live_words
