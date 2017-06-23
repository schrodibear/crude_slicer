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

    class rval_reads_collector acc = object(self)
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
        add_from_lval lv acc;
        DoChildren
    end

    let add_from_rval e acc = ignore @@ visitFramacExpr (new rval_reads_collector acc) e

    let add_from_lval lv acc =
      let o = new rval_reads_collector acc in
      match lv with
      | Mem e, off -> ignore @@ visitFramacExpr o e; ignore @@ visitFramacOffset o off
      | Var _, off -> ignore @@ visitFramacOffset o off

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

    let return = under @@ fun reads e assigns ->
      add_from_rval e reads;
      match e.enode, unrollType @@ typeOf e with
      | Lval lv, TComp _ -> comp_assign lv e reads assigns
      | _,       TComp _ -> Console.fatal "Slicing.return: composite expression that is not an lvalue: %a" pp_exp e
      | _                -> A.import_values `Result reads assigns

    let reach_target = under (fun from -> F.import ~from)

    let call info under s = under' info under s @@ fun from ?lv kf args depends assigns ->
      let I.E.Some { reads; assigns = (module A'); eff = eff' } =
        I.get info R.flag @@ Kernel_function.get_definition kf
      in
      let prj_reads = prj_reads reads s args in
      let prj_write = prj_write ?lv s in
      if I.E.is_target eff' then begin
        F.import ~from depends;
        prj_reads ~from:(I.E.depends eff') depends
      end;
      A'.iter
        (fun w from' ->
           may
             (fun w -> let reads = A.find w assigns in
               F.import ~from reads;
               prj_reads ~from:from' reads)
             (prj_write w))
        (I.E.assigns eff');
      may
        (fun lv ->
           add_from_lval lv from;
           gassign from lv assigns)
        lv

    let alloc = under @@ fun reads lv ?e assigns ->
      may (fun e -> add_from_rval e reads) e;
      gassign reads lv assigns

    let goto info under s = under' info under s @@ fun from assigns ->
      F.import ~from @@ A.find (w_var @@ I.H_stmt.find info.I.goto_vars s) assigns

    let is_var_sating p e =
      match (stripCasts e).enode with
      | Lval (Var v, NoOffset) when p v -> true
      | _                               -> false

    class effect_collector info eff = object
      method finish = add_transitive_closure (I.E.assigns eff)

      val curr_reads = Stack.create ()

      inherit frama_c_inplace

      method! vstmt =
      let handle_call lvo fundec params =
        let eff' = File_info.get file_info flag fundec in
        if Effect.is_target eff' then begin
          add_depends ~reach_target:true;
          project_reads ~fundec ~params ~from:(Effect.depends eff') (Effect.depends eff)
        end;
        let lv = may_map add_from_lval lvo ~dft:ignore in
        let project_reads = project_reads ~fundec ~params in
        Effect.iter_writes
          (fun w from ->
             match w with
             | Writes.Global _ | Writes.Result ->
               let lv = may_map (fun (Reads.Some (k, x)) r -> Reads.add k x r) ~dft:lv (Reads.of_writes w) in
               let struct_assign = w = Writes.Result && may_map ~dft:false (isStructOrUnionType % typeOfLval) lvo in
               add_edges ~struct_assign ~lv ~from:(project_reads ~from) ()
             | _ -> ())
          eff';
        may (fun lv' -> add_edges ~lv ~from:(add_rval_from_lval lv') ()) lvo
      in
      let handle_all_reads =
        let from = Reads.create dummy_flag in
        fun () ->
          Reads.clear from;
          collect_reads from;
          add_depends ~reach_target:false;
          Effect.iter_writes (fun _ r -> Reads.import ~from r) eff;
          Reads.import ~from all_reads
      in
      let continue_under f =
        let r = Reads.create dummy_flag in
        f r;
        Stack.push r curr_reads;
        DoChildrenPost (fun s -> ignore @@ Stack.pop curr_reads; s)
      in
      let alloc_to ~loc ~lv ~from =
        let lv = Mem (new_exp ~loc @@ Lval lv), NoOffset in
        add_edges ~lv:(add_from_lval lv) ~from:(fun r -> from r; add_rval_from_lval lv r) ()
      in
      let is_tracking_var v = isVoidPtrType v.vtype && Effect.is_tracking_var (Void_ptr_var.of_varinfo_exn v) eff in
      fun s ->
        match s.skind with
        | Instr (Set (lv, e, loc)) when is_var_sating is_tracking_var e ->
          alloc_to ~loc ~lv ~from:(add_from_rval e);
          SkipChildren
        | Instr (Set (lv, e, _)) ->
          add_edges
            ~struct_assign:(isStructOrUnionType @@ typeOfLval lv)
            ~lv:(add_from_lval lv)
            ~from:(add_from_rval_and_lval lv e)
            ();
          SkipChildren
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _)) when Options.Target_functions.mem vi.vname ->
          add_depends ~reach_target:true;
          SkipChildren
        | Instr (Call (lvo, { enode = Lval (Var vi, NoOffset) }, _, loc)) when Options.Alloc_functions.mem vi.vname ->
          begin match lvo with
          | Some (Var v, NoOffset as lv) when isVoidPtrType v.vtype ->
            add_edges ~lv:(add_from_lval lv) ~from:ignore ();
            Effect.add_tracking_var (Void_ptr_var.of_varinfo_exn v) eff
          | Some lv -> alloc_to ~loc ~lv ~from:ignore
          | None -> ()
          end;
          SkipChildren
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, [e], _)) when Options.Assume_functions.mem vi.vname ->
          add_edges ~lv:(add_from_rval e) ~from:ignore ();
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
            ~from:(may_map add_from_rval eo ~dft:ignore)
            ();
          SkipChildren
        | Goto _ ->
          handle_all_reads ();
          SkipChildren
        | Break _ | Continue _ ->
          SkipChildren
        | If (e, _, _, _)  ->
          continue_under (add_from_rval e)
        | Switch (e, _, _, _) ->
          continue_under
            (fun r ->
               add_from_rval e r;
               List.iter (fun e -> add_from_rval e r) (H_stmt_conds.find_or_empty break_continue_cache s))
        | Loop _ ->
          continue_under
            (fun r -> List.iter (fun e -> add_from_rval e r) (H_stmt_conds.find_or_empty break_continue_cache s))
        | Block _ | UnspecifiedSequence _ -> DoChildren
        | Throw _ | TryCatch _ | TryFinally _ | TryExcept _  ->
          failwith "Unsupported features: exceptions and their handling"
  end

    
  end
end

(*

class effect_collector break_continue_cache file_info def =
  let eff = File_info.get file_info flag def in
  let dummy_flag = Flag.create "effect_collector_dummy" in
  object
    method finish = add_transitive_closure eff

    val all_reads = Reads.create dummy_flag
    val curr_reads = Stack.create ()

    inherit frama_c_inplace

    method! vstmt =
      let collect_reads acc =
        Reads.import ~from:all_reads acc;
        Stack.iter (fun from -> Reads.import ~from acc) curr_reads
      in
      let add_edges =
        let r_lv = Reads.create dummy_flag and r_from = Reads.create dummy_flag in
        fun ?(struct_assign=false) ?lv ~from () ->
          Reads.clear r_lv;
          Reads.clear r_from;
          from r_from;
          collect_reads r_from;
          match lv with
          | Some lv ->
            lv r_lv;
            let handle r_from =
              Reads.iter_global (fun r -> Effect.add_reads (Writes.Global r) r_from eff) r_lv;
              Reads.iter_poly (fun v -> Effect.add_reads (Writes.Poly v) r_from eff) r_lv;
              Reads.iter_local (fun v -> Effect.add_reads (Writes.Local v) r_from eff) r_lv
            in
            if not struct_assign then handle r_from
            else if not (Reads.is_empty r_lv) then
              let r = Reads.copy dummy_flag r_from in
              Reads.sub ~from:r r_lv;
              handle r
          | None -> Effect.add_reads Writes.Result r_from eff
      in
      let add_depends ~reach_target =
        if reach_target then Effect.set_is_target eff;
        if Effect.is_target eff then collect_reads (Effect.depends eff)
      in
      let handle_call lvo fundec params =
        let eff' = File_info.get file_info flag fundec in
        if Effect.is_target eff' then begin
          add_depends ~reach_target:true;
          project_reads ~fundec ~params ~from:(Effect.depends eff') (Effect.depends eff)
        end;
        let lv = may_map add_from_lval lvo ~dft:ignore in
        let project_reads = project_reads ~fundec ~params in
        Effect.iter_writes
          (fun w from ->
             match w with
             | Writes.Global _ | Writes.Result ->
               let lv = may_map (fun (Reads.Some (k, x)) r -> Reads.add k x r) ~dft:lv (Reads.of_writes w) in
               let struct_assign = w = Writes.Result && may_map ~dft:false (isStructOrUnionType % typeOfLval) lvo in
               add_edges ~struct_assign ~lv ~from:(project_reads ~from) ()
             | _ -> ())
          eff';
        may (fun lv' -> add_edges ~lv ~from:(add_rval_from_lval lv') ()) lvo
      in
      let handle_all_reads =
        let from = Reads.create dummy_flag in
        fun () ->
          Reads.clear from;
          collect_reads from;
          add_depends ~reach_target:false;
          Effect.iter_writes (fun _ r -> Reads.import ~from r) eff;
          Reads.import ~from all_reads
      in
      let continue_under f =
        let r = Reads.create dummy_flag in
        f r;
        Stack.push r curr_reads;
        DoChildrenPost (fun s -> ignore @@ Stack.pop curr_reads; s)
      in
      let alloc_to ~loc ~lv ~from =
        let lv = Mem (new_exp ~loc @@ Lval lv), NoOffset in
        add_edges ~lv:(add_from_lval lv) ~from:(fun r -> from r; add_rval_from_lval lv r) ()
      in
      let is_tracking_var v = isVoidPtrType v.vtype && Effect.is_tracking_var (Void_ptr_var.of_varinfo_exn v) eff in
      fun s ->
        match s.skind with
        | Instr (Set (lv, e, loc)) when is_var_sating is_tracking_var e ->
          alloc_to ~loc ~lv ~from:(add_from_rval e);
          SkipChildren
        | Instr (Set (lv, e, _)) ->
          add_edges
            ~struct_assign:(isStructOrUnionType @@ typeOfLval lv)
            ~lv:(add_from_lval lv)
            ~from:(add_from_rval_and_lval lv e)
            ();
          SkipChildren
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, _, _)) when Options.Target_functions.mem vi.vname ->
          add_depends ~reach_target:true;
          SkipChildren
        | Instr (Call (lvo, { enode = Lval (Var vi, NoOffset) }, _, loc)) when Options.Alloc_functions.mem vi.vname ->
          begin match lvo with
          | Some (Var v, NoOffset as lv) when isVoidPtrType v.vtype ->
            add_edges ~lv:(add_from_lval lv) ~from:ignore ();
            Effect.add_tracking_var (Void_ptr_var.of_varinfo_exn v) eff
          | Some lv -> alloc_to ~loc ~lv ~from:ignore
          | None -> ()
          end;
          SkipChildren
        | Instr (Call (_, { enode = Lval (Var vi, NoOffset) }, [e], _)) when Options.Assume_functions.mem vi.vname ->
          add_edges ~lv:(add_from_rval e) ~from:ignore ();
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
            ~from:(may_map add_from_rval eo ~dft:ignore)
            ();
          SkipChildren
        | Goto _ ->
          handle_all_reads ();
          SkipChildren
        | Break _ | Continue _ ->
          SkipChildren
        | If (e, _, _, _)  ->
          continue_under (add_from_rval e)
        | Switch (e, _, _, _) ->
          continue_under
            (fun r ->
               add_from_rval e r;
               List.iter (fun e -> add_from_rval e r) (H_stmt_conds.find_or_empty break_continue_cache s))
        | Loop _ ->
          continue_under
            (fun r -> List.iter (fun e -> add_from_rval e r) (H_stmt_conds.find_or_empty break_continue_cache s))
        | Block _ | UnspecifiedSequence _ -> DoChildren
        | Throw _ | TryCatch _ | TryFinally _ | TryExcept _  ->
          failwith "Unsupported features: exceptions and their handling"
  end

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
