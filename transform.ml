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

[@@@warning "-48-44-4"]

open Cil
open Cil_types
open Visitor

open Extlib
open! Common
open Region

let dot ~loc offs e =
  mkCast
    ~force:false
    ~overflow:Check
    ~e:(mkAddrOf ~loc (Mem e, Offset.of_offs offs))
    ~newt:(TPtr (ucharType, []))

let rec mark =
  function
  | []                         -> ()
  | `Field fi :: os            -> fi.faddrof <- true; mark os
  | `Container_of_void _ :: os -> mark os

module Make (Analysis : Analysis) = struct
  open Analysis

  let builtin_expect = Str.regexp @@ Options.Builtin_expect_regexp.get ()

  let mark_lval =
    let rec mark_offset =
      function
      | NoOffset        -> ()
      | Field (fi, off) -> fi.faddrof <- true; mark_offset off
      | Index (_, off)  -> mark_offset off
    in
    function
    | Var vi, off -> vi.vaddrof <- true; mark_offset off
    | Mem _,  off -> mark_offset off

  let cast_init vi =
    let rec loop ty =
      function
      | SingleInit e
        when need_cast ty (typeOf e) -> SingleInit (mkCast ~force:false ~overflow:Check ~e ~newt:ty)
      | SingleInit _ as i            -> i
      | CompoundInit (_, is)         -> CompoundInit (ty, List.map (fun (off, i) -> off, loop (typeOffset ty off) i) is)
    in
    loop vi.vtype

  class rewriter = object(self)
    inherit frama_c_inplace

    method! vexpr e =
      let loc = e.eloc in
      let visit = visitFramacExpr (self :> frama_c_visitor) in
      let cast ty e =
        let ty' = let ty' = typeOf e in if isIntegralType ty' then ty else ty' in
        let ty, ty' = map_pair Ty.deref_once (ty, ty') in
        if not (Ty.compatible ty ty') then
          match
            Ci.(match_deep_first_subfield_of ty ty',
                match_deep_first_subfield_of ty' ty)
          with
          | Some offs, _
          | _,         Some offs                               -> mark offs
          | _                                                  -> ()
      in
      let container_of = Exp.container_of ~loc in
      match match_container_of2 e.enode, match_dot e.enode with
      | Some (e, offs), _                         -> let e = visit e in mark offs; ChangeTo (container_of offs e)
      | _,              Some (e, offs)            -> let e = visit e in mark offs; ChangeTo (dot ~loc offs e)
      | _                                         ->
        match e.enode with
        | AddrOf lv | StartOf lv                  -> mark_lval lv; DoChildren
        | CastE (ty, _, e)                        -> cast ty e;    DoChildren
        | BinOp
            ((Eq | Ne as op),
             { enode = CastE (ty, _, e1); _ },
             { enode = CastE (ty', _, e2); _ },
             _)
          when
            not
              (need_cast ty theMachine.upointType
               || need_cast ty ty')               -> ChangeToPost
                                                       (mkBinOp ~loc op
                                                          (mkCast ~force:false ~overflow:Check ~e:e1 ~newt:(typeOf e2))
                                                          e2,
                                                        id)
        | _                                       -> DoChildren

    method! vstmt s =
      match s.skind with
      | Instr (Call (Some lv,
                     { enode =
                         Lval (Var { vname; _ }, NoOffset); _ },
                     [e; _], loc))
        when Str.string_match builtin_expect vname 0             -> s.skind <- Instr (Set (lv, e, loc));    DoChildren
      | Instr (Local_init (vi, AssignInit init, loc))            ->(s.skind <-
                                                                      Instr
                                                                        (Local_init
                                                                           (vi,
                                                                            AssignInit (cast_init vi init),
                                                                            loc));                          DoChildren)
      | _                                                        ->                                         DoChildren

    method! vglob_aux =
      function
      | GFun (f, _)
        when Options.Required_bodies.mem f.svar.vname      -> DoChildren
      | GFun (d, loc)
        when Options.(Alloc_functions.mem  d.svar.vname ||
                      Assume_functions.mem d.svar.vname ||
                      Target_functions.mem d.svar.vname)   ->(let kf = Globals.Functions.get d.svar in
                                                              kf.fundec <-
                                                                Declaration
                                                                  (d.sspec, d.svar, Some d.sformals, d.svar.vdecl);
                                                              ChangeTo [GFunDecl (d.sspec, d.svar, loc)])
      | _                                                  -> DoChildren

  end

  let unique_param_names =
    let name old n = old ^ if n = 0 then "" else string_of_int n in
    let exists_glob_name n =
      try ignore @@ Globals.Vars.find_from_astinfo n VGlobal; true
      with Not_found ->
      try ignore @@ Globals.Functions.find_by_name n;         true
      with Not_found ->                                       false
    in
    let rec next vis old n =
      let n = n + 1 in
      let name = name old n in
      if List.exists (fun vi -> String.equal vi.vname name) vis || exists_glob_name name
      then next vis old n
      else n
    in
    fun () ->
      Globals.Functions.iter
        (fun kf ->
           let vis = Kernel_function.get_formals kf in
           ignore @@
           List.fold_left
             (fun acc vi ->
                let old = if vi.vname = "" then "arg" else vi.vname in
                let acc = next vis old acc in
                if vi.vname = "" || exists_glob_name vi.vname then
                  vi.vname <- name old acc;
                acc)
             ~-1
             vis)

  let rewrite () =
    Console.debug "Started rewriting AST...";
    unique_param_names ();
    visitFramacFile (new rewriter) @@ Ast.get ()
end
