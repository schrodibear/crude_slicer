(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

[@@@warning "-48-44-4"]

open Cil
open Cil_types
open Visitor

open Extlib
open! Common
open Region
open Analyze

let container_of =
  let mkCast = mkCast ~overflow:Check ~force:true in
  fun ~loc offs e ->
    let newt =
      TPtr
        ((match List.hd offs with
           | `Field fi             -> TComp (fi.fcomp, empty_size_cache (), [])
           | `Container_of_void ty -> Ty.normalize ty),
         [])
    in
    mkCast ~newt ~e:(new_exp ~loc @@ BinOp (MinusPI,
                                            mkCast ~newt:charPtrType ~e,
                                            mkCast
                                              ~newt:theMachine.typeOfSizeOf
                                              ~e:(mkAddrOf ~loc (Mem (mkCast ~newt ~e:(zero ~loc)), to_offset offs)),
                                            charPtrType))

let dot ~loc offs e = mkAddrOf ~loc (Mem e, to_offset offs)

let rec mark =
  function
  | []                         -> ()
  | `Field fi :: os            -> fi.faddrof <- true; mark os
  | `Container_of_void _ :: os -> mark os

module Make (Analysis : Analysis) = struct
  open Analysis

  let builtin_expect = Str.regexp @@ Options.Builtin_expect_regexp.get ()

  class rewriter = object(self)
    inherit frama_c_inplace

    method! vexpr e =
      let loc = e.eloc in
      let visit = visitFramacExpr (self :> frama_c_visitor) in
      let cast ty e =
        let ty' = typeOf e in
        if not (Ty.compatible ty ty') then
          match
            Ci.(match_deep_first_subfield_of ty ty',
                match_deep_first_subfield_of ty' ty)
          with
          | Some offs, _
          | _,         Some offs                               -> mark offs
          | _                                                  -> ()
      in
      match match_container_of2 e.enode, match_dot e.enode with
      | Some (e, offs), _                       -> let e = visit e in mark offs; ChangeTo (container_of ~loc offs e)
      | _,              Some (e, offs)          -> let e = visit e in mark offs; ChangeTo (dot ~loc offs e)
      | _                                       ->
        match e.enode with
        | CastE (ty, _, e)                      -> cast ty e; DoChildren
        | BinOp
            ((Eq | Ne as op),
             { enode = CastE (ty, _, e1); _ },
             { enode = CastE (ty', _, e2); _ },
             _)
          when
            not (need_cast
                   ty
                   theMachine.ptrdiffType) &&
            not (need_cast ty ty')              -> ChangeDoChildrenPost (mkBinOp ~loc op e1 e2, id)
        | _                                     -> DoChildren

    method! vinst =
      function
      | Call (Some lv, { enode = Lval (Var { vname; _ }, NoOffset); _ }, [e; _], loc)
        when Str.string_match builtin_expect vname 0                                  -> ChangeTo [Set (lv, e, loc)]
      | _                                                                             -> DoChildren
  end

  let unique_param_names =
    let name n = "arg" ^ string_of_int n in
    let rec next vis n =
      let n = n + 1 in
      let name = name n in
      if List.exists (fun vi -> String.equal vi.vname name) vis
      then next vis n
      else n
    in
    fun () ->
      Globals.Functions.iter
        (fun kf ->
           let vis = Kernel_function.get_formals kf in
           ignore @@
           List.fold_left
             (fun acc vi ->
                if vi.vname = "" then
                  vi.vname <- name acc;
                next vis acc)
             (next vis 0)
             vis)

  let rewrite () =
    Console.debug "Started rewriting AST...";
    unique_param_names ();
    visitFramacFile (new rewriter) @@ Ast.get ()
end
