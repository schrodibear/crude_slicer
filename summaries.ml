(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

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

  type mem = R.t * fieldinfo option

  let generate =
    let open List in
    let open Kernel_function in
    let open Options in
    let find_by_name = Globals.Functions.find_by_name in
    let module H_v = Varinfo.Hashtbl in
    let module H_d = Fundec.Hashtbl in
    let h_ins = H_d.create 256 in
    let h_params = H_v.create 16 in
    let mkStmt = mkStmt ~valid_sid:true in
    let loc = Location.unknown in
    fun sccs ->
      ensure_havoc_function_present ();
      ensure_choice_function_present ();
      let havoc_lval =
        let havoc = get_vi @@ find_by_name @@ Choice_function.get () in
        fun d lv es ->
          let tmp = makeTempVar d ~insert:true ~name:"tmp" ulongLongType in
          [mkStmt @@ Instr (Call (Some (var tmp), evar havoc, es, loc));
           mkStmt @@ Instr (Set (lv, mkCast ~force:false ~overflow:Check ~e:(evar tmp) ~newt:(typeOfLval lv), loc))]
      in
      let havoc_region =
        let havoc = get_vi @@ find_by_name @@ Havoc_function.get () in
        fun e es -> [mkStmt @@ Instr (Call (None, evar havoc, e :: es, loc))]
      in
      let file = Ast.get () in
      visitFramacFile
        (object
          inherit frama_c_inplace
          method! vfunc d =
            let name = d.svar.vname in
            let I.E.Some { eff; _ } = I.get info R.flag d in
            if not (I.E.is_target eff
                    || Alloc_functions.mem name || Assume_functions.mem name || Path_assume_functions.mem name)
            then
              H_d.add h_ins d d;
            SkipChildren
        end)
        file;
      flatten sccs |>
      filter is_definition |>
      map get_definition |>
      iter
        (fun d ->
           let I.E.Some { reads = (module F); assigns = (module A); eff } = I.get info R.flag d in
           if H_d.mem h_ins d then
             let d' =
               let name =
                 let doesn't_exist name = try ignore @@ find_by_name name; false with Not_found -> true in
                 let name = d.svar.vname ^ "_stub" in
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
               let d' = emptyFunctionFromVI @@ copyVarinfo d.svar name in
               d'.sformals <- getFormalsDecl d'.svar;
               d'.svar.vattr <- Attr (Kf.stub_attr, [AStr d.svar.vname]) :: d'.svar.vattr;
               d'
             in
             iter2 (H_v.add h_params) d.sformals d'.sformals;
             let retvar =
               let rety = getReturnType d'.svar.vtype in
               makeTempVar d' ~insert:(not @@ isVoidType rety) ~name:"result" rety
             in
             let retexp = if isStructOrUnionType retvar.vtype then mkAddrOf ~loc (var retvar) else evar retvar in
             let stmts = Stack.create () in
             let from = Stack.create () in
             A.iter
               (fun w froms ->
                  let mk : I.W.t -> _ =
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
                             method! vvrbl vi = try ChangeTo (H_v.find h_params vi) with Not_found -> SkipChildren
                           end)
                          (R.exp' r)
                      in
                      match eo, fo with
                      | None,      _       -> `Skip
                      | Some addr, None    -> `Exp (new_exp ~loc @@ Lval (mkMem ~addr ~off:NoOffset))
                      | Some addr, Some fi -> `Exp (new_exp ~loc @@ Lval (mkMem ~addr ~off:(Field (fi, NoOffset))))
                    in
                    let mk_var vi = `Var (var @@ try H_v.find h_params vi with Not_found -> vi) in
                    function
                    | `Global_mem m -> mk_mem (m :> mem)
                    | `Global_var v -> mk_var (v :> varinfo)
                    | `Local_mem  _ -> `Skip
                    | `Local_var  _ -> `Skip
                    | `Poly_mem   m -> mk_mem (m :> mem)
                    | `Poly_var   v -> mk_var (v :> varinfo)
                    | `Result       -> `Var (var retvar)
                  in
                  let froms () =
                    let open! Stack in
                    F.iter (fun r -> push (mk r) from) froms;
                    fold
                      (fun acc ->
                         function
                         | `Var lv -> new_exp ~loc (Lval lv) :: acc
                         | `Exp e  -> e                      :: acc
                         | `Skip   ->                           acc)
                      []
                      from |>
                    tap (const @@ clear from)
                  in
                  if
                    match w with
                    | `Result            -> I.E.has_result_dep eff
                    | #I.W.readable as w -> F.(mem_some (of_write w) @@ I.E.depends eff)
                  then
                    iter
                      (fun s -> Stack.push s stmts)
                      (match mk w with
                       | `Var lv -> havoc_lval d' lv (froms ())
                       | `Exp e  -> havoc_region  e  (froms ())
                       | `Skip   -> []))
               (I.E.assigns eff);
             d'.sbody.bstmts <-
               Stack.fold cons' [] stmts @
               if not (isVoidType retvar.vtype) then [mkStmt @@ Return (Some (evar retvar), loc)] else [];
             Stack.clear stmts;
             H_v.clear h_params;
             H_d.replace h_ins d d');
      H_d.filter_map_inplace (fun d d' -> if Fundec.equal d d' then None else Some d') h_ins;
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
