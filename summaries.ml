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

[@@@warning "-48"]

open Extlib

open Cil_types
open Cil_datatype
open Cil
open Visitor

open! Common

let ensure_havoc_function_present () = Kf.ensure_proto voidType (Options.Havoc_function.get ()) [voidPtrType] true
let ensure_choice_function_present () = Kf.ensure_proto ulongLongType (Options.Choice_function.get ()) [intType] true

module Make (R : Region.Analysis) (M : sig val info : R.I.t end) = struct
  module I = R.I
  module R = struct
    include R.R
    include R
  end
  module U = R.U
  open M

  let generate =
    let open List in
    let module H_d = Fundec.Hashtbl in
    let module S_d = Fundec.Set in
    let module M_v = Varinfo.Map in
    let mkStmt = mkStmt ~valid_sid:true in
    let loc = Location.unknown in
    let fresh_stub_name oldname =
      let doesn't_exist name =
        try ignore @@ Globals.Functions.find_by_name name; false
        with Not_found ->                                  true
      in
      let name = oldname ^ Options.Stub_postfix.get () in
      if doesn't_exist name
      then
        name
      else
        let rec find n =
          let name = name ^ string_of_int n in
          if doesn't_exist name
          then name
          else find (n + 1)
        in
        find 0
    in
    let stmts_of_writes d d' =
      let retvar =
        let rety = getReturnType d.svar.vtype in
        makeTempVar d' ~insert:(not @@ isVoidType rety) ~name:"result" rety
      in
      let retexp = if isStructOrUnionType retvar.vtype then mkAddrOf ~loc (var retvar) else evar retvar in
      let params = fold_right2 M_v.add d.sformals d'.sformals M_v.empty in
      let mk_w : I.writable -> _ =
        let mk_mem (r, fo) =
          let eo =
            opt_map
              (visitFramacExpr @@
               object
                 inherit frama_c_inplace
                 method! vexpr e =
                   if R.Exp.is_ret e
                   then ChangeTo retexp
                   else DoChildren
                 method! vvrbl vi = try ChangeTo (M_v.find vi params) with Not_found -> SkipChildren
               end)
              (R.exp' r :> exp option)
          in
          match eo, fo with
          | None,      _       -> `Skip
          | Some addr, None    -> `Exp (new_exp ~loc @@ Lval (mkMem ~addr ~off:NoOffset))
          | Some addr, Some fi -> `Exp (new_exp ~loc @@ Lval (mkMem ~addr ~off:(Field (fi, NoOffset))))
        in
        let mk_var vi = `Var (var @@ try M_v.find vi params with Not_found -> vi) in
        function
        | `Global_mem m -> mk_mem m
        | `Global_var v -> mk_var v
        | `Local_mem  _ -> `Skip
        | `Local_var  _ -> `Skip
        | `Poly_mem   m -> mk_mem m
        | `Poly_var   v -> mk_var v
        | `Result       -> `Var (var retvar)
      in
      let limit =
        let max = Options.Deps_limit.get () in
        let z = mkCast ~force:true ~overflow:Check ~e:(zero ~loc) ~newt:voidPtrType in
        fun es -> let l = List.length es in if 0 < l && l <= max then es else [z]
      in
      let havoc_lval =
        let havoc = Kernel_function.get_vi @@ Globals.Functions.find_by_name @@ Options.Choice_function.get () in
        fun lv es ->
          let tmp = makeTempVar d' ~insert:true ~name:"tmp" ulongLongType in
          [mkStmt @@ Instr (Call (Some (var tmp), evar havoc, limit es, loc));
           mkStmt @@ Instr (Set (lv, mkCast ~force:false ~overflow:Check ~e:(evar tmp) ~newt:(typeOfLval lv), loc))]
      in
      let havoc_region =
        let havoc = Kernel_function.get_vi @@ Globals.Functions.find_by_name @@ Options.Havoc_function.get () in
        fun e es -> [mkStmt @@ Instr (Call (None, evar havoc, e :: limit es, loc))]
      in
      let I.E.Some { local = (module L); eff } = I.get info R.flag d in
      flatten @@
      rev @@
      (if not (isVoidType retvar.vtype) then [[mkStmt @@ Return (Some (evar retvar), loc)]] else []) @
      L.A.fold
        (fun w froms ->
           let froms () =
             rev @@
             L.R.fold
               (fun r ->
                  match mk_w (r : L.W.readable :> I.writable) with
                  | `Var lv -> cons @@ new_exp ~loc (Lval lv)
                  | `Exp e  -> cons e
                  | `Skip   -> id)
               froms
               []
           in
           if
             match w with
             | `Result            -> I.E.has_result_dep eff
             | #L.W.readable as w -> L.R.(mem_some (of_write w) @@ I.E.depends eff)
           then
             match mk_w (w :> I.writable) with
             | `Var lv -> cons @@ havoc_lval   lv (froms ())
             | `Exp e  -> cons @@ havoc_region e  (froms ())
             | `Skip   -> id
           else
             id)
        (I.E.assigns eff)
        []
    in
    let h_ins = H_d.create 256 in
    fun sccs ->
      ensure_havoc_function_present ();
      ensure_choice_function_present ();
      let ds = sccs |> flatten |> Kernel_function.(filter_map is_definition get_definition) |> S_d.of_list in
      let file = Ast.get () in
      visitFramacFile
        (object
          inherit frama_c_inplace
          method! vfunc d =
            let name = d.svar.vname in
            let I.E.Some { eff; _ } = I.get info R.flag d in
            if S_d.mem d ds
            && not
                 (I.E.is_target eff
                  || Options.(Alloc_functions.mem name || Assume_functions.mem name || Path_assume_functions.mem name))
            then
              H_d.add h_ins d d;
            SkipChildren
        end)
        file;
      H_d.filter_map_inplace
        (fun _ d ->
           some @@
           let d' = emptyFunctionFromVI @@ copyVarinfo d.svar @@ fresh_stub_name d.svar.vname in
           d'.sformals <- getFormalsDecl d'.svar;
           d'.svar.vattr <- Attr (Kf.stub_attr, [AStr d.svar.vname]) :: d'.svar.vattr;
           d'.sbody.bstmts <- stmts_of_writes d d';
           d')
        h_ins;
      ignore @@
      visitFramacFile
        (object
          inherit frama_c_inplace
          method! vglob_aux =
            function
              [@warning "-4"]
            | GFun (d, _) as g when H_d.mem h_ins d -> ChangeTo [g; GFun (H_d.find h_ins d, loc)]
            | _                                     -> SkipChildren
        end)
        file;
      H_d.clear h_ins
end
