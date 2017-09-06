(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Cil_types
open Cil
open Visitor
open Cil_datatype

open Extlib
open! Common

[@@@warning "-48-4-44"]

module Make (R : Region.Analysis) = struct
  module R = struct
    include R.R
    include R
  end
  module U = R.U

  class f_opt_visitor funcs = object
    inherit frama_c_inplace

    val mutable f = None

    method! vfunc fd =
      if Varinfo.Set.mem fd.svar funcs
      then begin
        f <- Some fd.svar.vname;
        DoChildren
      end else
        SkipChildren
  end

  let approx =
    let module H = struct
      include Hashtbl.Make
          (struct
            type t = R.t
            let hash, equal = R.(hash, equal)
          end)
      module H = Kernel_function.Hashtbl
      let add h u kf =
        let r = U.repr u in
        H.replace (try find h r with Not_found -> let h' = H.create 4 in add h r h'; h') kf ()
      let iter h f u = try H.iter f @@ find h (U.repr u) with Not_found -> ()
      let import h ~from u = iter h (const' @@ add h u) from
      let find_all h u = try H.fold (const' List.cons) (find h @@ U.repr u) [] with Not_found -> []
    end in
    let module H_e = Exp.List_hashtbl in
    let module Fixpoint =
      Fixpoint.Make
        (struct
          module E = struct
            type some = unit
            let pp _ = ignore
          end

          type t = unit

          let get _ _ _ = ()
          let flag = R.flag
        end)
    in
    let approx = H.create 128 in
    let propagator dir () _ = object
      inherit frama_c_inplace

      method start = ()
      method finish = ()
      method! vstmt s =
        match s.skind with
        | Instr (Call _)           ->
          begin match R.map s with
          | map                    -> R.H_map.iter
                                        (fun u' u ->
                                           let from, u =
                                             match dir with
                                             | `Forward  -> u,  u'
                                             | `Backward -> u', u
                                           in
                                           H.import approx ~from u)
                                        map;                        SkipChildren
          | exception Not_found    ->                               SkipChildren
          end
        | _                        ->                               DoChildren
    end in
    fun () ->
      Console.debug "Started function pointer approximation...";
      let file = Ast.get () in
      let sccs = Analyze.condensate () in
      let funcs = List.flatten sccs |> List.map Kernel_function.get_vi |> Varinfo.Set.of_list in
      visitFramacFile
        (object
          inherit f_opt_visitor funcs
          inherit! Analyze.direct_call_skipping_visitor


          method! vvrbl vi =
            begin match Globals.Functions.get vi with
            | kf                  -> H.add approx R.(location @@ of_var ?f vi) kf
            | exception Not_found -> ()
            end;
            SkipChildren
        end)
        file;
      Fixpoint.visit_until_convergence ~order:`topological (propagator `Backward) () sccs;
      Fixpoint.visit_until_convergence ~order:`reversed    (propagator `Forward)  () sccs;
      let r = H_e.create 2048 in
      visitFramacFile
        (object
          inherit f_opt_visitor funcs

          method! vstmt s =
            match s.skind with
            | Instr (Call (_, e, _, _))    ->
              let e = Exp.underef_mem e in
              begin match R.of_expr e with
              | `Value u                   -> H_e.add r e @@ H.find_all approx u
              | `None                      -> ()
              end;                                                               SkipChildren
            | _                            ->                                    DoChildren

        end)
        file;
      H.clear approx;
      r
end

let ensure_nondet_int_function_present () =
  try
    ignore @@ Globals.Functions.find_by_name @@ Options.Nondet_int_function.get ()
  with
  | Not_found ->
    let file = Ast.get () in
    file.globals <-
      GFunDecl (empty_funspec (),
                makeGlobalVar (Options.Nondet_int_function.get ()) (TFun (intType, Some [], false, [])),
                Location.unknown)
      :: file.globals

let rewrite ~callee_approx =
  let approx ckf s lvo e args loc =
    let open Kernel_function in
    let mkStmt = mkStmt ~valid_sid:true in
    let call kf = Instr (Call (lvo, evar (get_vi kf), args, loc)) in
    let stub () =
      let nondet = makeTempVar (get_definition ckf) ~name:"nondet_stub" (TInt (IInt, [])) in
      let init_nondet vi =
        let verifier_nondet = get_vi @@ Globals.Functions.find_by_name @@ Options.Nondet_int_function.get () in
        mkStmt @@ Instr (Call (Some (var vi), evar verifier_nondet, [], loc))
      in
      may_map
        (fun lv ->
           let ty = typeOfLval lv in
           if isIntegralOrPointerType ty
           && need_cast ty ulongLongType
           && need_cast ty longLongType
           then
             Block
               (mkBlock @@
                [init_nondet nondet;
                 mkStmt @@
                 Instr (Set
                          (lv,
                           mkCast ~force:false ~overflow:Check ~e:(evar nondet) ~newt:(typeOfLval lv),
                           loc))])
           else
             s.skind)
        ~dft:(Instr (Skip loc))
        lvo
    in
    let e = Exp.underef_mem e in
    s.skind <-
      List.fold_right
        (fun kf acc ->
           If (mkBinOp ~loc Eq e (mkAddrOf ~loc @@ var @@ get_vi kf),
               mkBlock [mkStmt @@ call kf],
               mkBlock [mkStmt @@ acc],
               loc))
        Exp.(List_hashtbl.find_all callee_approx e)
        (stub ())
  in
  ensure_nondet_int_function_present ();
  visitFramacFile
    (object(self)
      inherit frama_c_inplace

      method! vstmt s =
        match s.skind with
        | Instr
            (Call
               (_,
                { enode = Lval (Var vi, NoOffset); _ },
                _,
                _))
          when Kf.mem vi                                 ->                                                SkipChildren
        | Instr (Call (lvo, e, args, loc))               -> approx (the self#current_kf) s lvo e args loc; SkipChildren
        | _                                              ->                                                DoChildren
    end)
    (Ast.get ())
