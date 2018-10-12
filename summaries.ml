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
open Info

let ensure_havoc_function_present () = Kf.ensure_proto voidType (Options.Havoc_function.get ()) [voidPtrType] true
let ensure_choice_function_present () = Kf.ensure_proto ulongLongType (Options.Choice_function.get ()) [intType] true
let ensure_uniformity_flag_function_present () =
  Kf.ensure_proto intType (Options.Uniformity_flag_function.get ()) [voidConstPtrType] false
let ensure_evaluation_function_present () =
  Kf.ensure_proto ulongLongType (Options.Evaluation_function.get ()) [voidConstPtrType] false

module Make (R : Region.Analysis) (M : sig val info : R.I.t end) = struct
  module I = R.I
  module R = struct
    include R.R
    include R
  end
  module U = R.U
  open M

  module Make_local (L : I.E.Local) = struct
    module F = L.F
    open F

    type elem =
      | Top
      | Bot
      | Top_or_bot of Local.Var.t
      | Val_or_top of { g : Local.Var.t; v : Local.Var.t }
      | Val_or_bot of { a : Local.Var.t; v : Local.Var.t }
      | Mixed of { a : Local.Var.t; g : Local.Var.t; v : Local.Var.t }
      | Val of Local.Var.t

    let loc = Location.unknown
    let exp = new_exp ~loc
    let stmt = mkStmt ~ghost:false ~valid_sid:true
    let instr = mkStmtOneInstr ~ghost:false ~valid_sid:true
    let set lv e = instr @@ Set (lv, e, loc)
    let call ?lv v es = instr @@ Call (lv, evar v, es, loc)

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

    module M_v = Varinfo.Map
    let f =
      let f = F.f in
      let d = emptyFunctionFromVI @@ copyVarinfo f.svar @@ fresh_stub_name f.svar.vname in
      d.sformals <- getFormalsDecl d.svar;
      d.svar.vattr <- Attr (Kf.stub_attr, [AStr d.svar.vname]) :: f.svar.vattr;
      d
    let retvar =
      let rety = getReturnType f.svar.vtype in
      makeTempVar F.f ~insert:(not @@ isVoidType rety) ~name:"result" rety
    let retexp = if isStructOrUnionType retvar.vtype then mkAddrOf ~loc (var retvar) else evar retvar
    let params = List.fold_right2 M_v.add F.f.sformals f.sformals M_v.empty
    let aux kind =
      Local.Var.of_varinfo @@
      makeTempVar
        f
        ~name:(match kind with `Grd -> "grd" | `Ass -> "ass" | `Val _ -> "val" | `Tmp _ -> "tmp")
        (match kind with `Grd | `Ass -> intType | `Val t | `Tmp t -> t)
    let var' v = var (v : Local.Var.t :> varinfo)
    let evar' v = evar (v : Local.Var.t :> varinfo)

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
      | None,      _       -> None
      | Some addr, None    -> Some (exp @@ Lval (mkMem ~addr ~off:NoOffset))
      | Some addr, Some fi -> Some (exp @@ Lval (mkMem ~addr ~off:(Field (fi, NoOffset))))
    let mk_var vi = var @@ try M_v.find vi params with Not_found -> vi

    let limit =
      let max = Options.Deps_limit.get () in
      let z = mkCast ~force:true ~overflow:Check ~e:(zero ~loc) ~newt:voidPtrType in
      fun es -> let l = List.length es in if 0 < l && l <= max then es else [z]
    let get_vi = Kernel_function.get_vi % Globals.Functions.find_by_name
    let havoc_lval =
      let havoc = get_vi @@ Options.Choice_function.get () in
      fun lv es ->
        let tmp = aux (`Tmp ulongLongType) in
        [call ~lv:(var' tmp) havoc @@ limit es;
         set lv @@ mkCast ~force:false ~overflow:Check ~e:(evar' tmp) ~newt:(typeOfLval lv)]
    let havoc_region =
      let havoc = get_vi @@ Options.Havoc_function.get () in
      fun e es -> [call havoc @@ e :: limit es]

    let guard_mem =
      let uniformity_flag = get_vi @@ Options.Uniformity_flag_function.get () in
      fun lv e -> [call ~lv uniformity_flag [e]]
    let eval_mem =
      let eval = get_vi @@ Options.Evaluation_function.get () in
      fun lv e ->
        let tmp = aux (`Tmp ulongLongType) in
        [call ~lv:(var' tmp) eval [e];
         set lv @@ mkCast ~force:false ~overflow:Check ~e:(evar' tmp) ~newt:(typeOfLval lv)]

    let push, stmts =
      let stmts = Queue.create () in
      List.iter (swap Queue.add @@ stmts), fun () -> Queue.to_seq stmts

    let const i k =
      let v = aux (`Val (TInt (k, []))) in
      push [set (var' v) @@ exp @@ Const (CInt64 (i, k, None))];
      Val v

    let mem m =
      match mk_mem m with
      | Some e ->(let g = aux `Grd in
                  let v = aux (`Val (typeOf e)) in
                  push @@ guard_mem (var' g) e @ eval_mem (var' v) e;
                  Val_or_top { g; v })
      | None   -> Console.fatal "Summaries.Local.mem: unexpected dangling region: should have been eliminated"

    let nondet ty =
      let v = aux (`Val ty) in
      push @@ havoc_lval (var' v) [];
      Val v

    let top = Top

    let bot = Bot

    let unop u e t =
      match u with
      | `Cast i   -> CastE (TInt (i, []), Check, e)
      | `Minus
      | `Bw_neg
      | `Neg as u -> UnOp
                       ((match u with
                        | `Minus  -> Neg Check
                        | `Bw_neg -> BNot
                        | `Neg    -> LNot),
                        e,
                        t)

    let unary u e t =
      let op v =
        let v' = aux (`Val t) in
        push [set (var' v') @@ exp @@ unop u (evar' v) t];
        v'
      in
      match e with
      | Top                 -> Top
      | Bot                 -> Bot
      | Top_or_bot _ as v   -> v
      | Val_or_top { g; v } -> Val_or_top { g; v = op v }
      | Val_or_bot { a; v } -> Val_or_bot { a; v = op v }
      | Mixed { a; g; v }   -> Mixed { a; g; v = op v }
      | Val v               -> Val (op v)

    let (&&?) a1 a2 =
      match a1, a2 with
      | `False,  _
      | _,       `False  -> `False
      | `True,   `True   -> `True
      | `True,   `Var v
      | `Var v,  `True   -> `Var v
      | `Var v1, `Var v2 ->(let g = aux `Grd in
                            push [set (var' g) @@ mkBinOp ~loc BAnd (evar' v1) @@ evar' v2];
                            `Var g)

    let (||?) a1 a2 =
      match a1, a2 with
      | `True,  _
      | _,      `True   -> `True
      | `False,  `False -> `False
      | `False, `Var v
      | `Var v, `False  -> `Var v
      | `Var v1,`Var v2 ->(let g = aux `Grd in
                           push [set (var' g) @@ mkBinOp ~loc BOr (evar' v1) @@ evar' v2];
                           `Var g)

    let ikind t =
      match unrollType t with
      | TInt (i, _) -> i
      | _           -> Console.fatal "Summaries.Local.ikind: unexpected type"
    let get_val ~s ~u t =
      exp @@ Const (CInt64 ((if isSignedInteger t then s else u) @@ bitsSizeOf t, ikind t, None))
    let all_ones = get_val ~s:min_signed_number ~u:max_unsigned_number
    let min_val  = get_val ~s:min_signed_number ~u:(fun _ -> Integer.zero)
    let max_val  = get_val ~s:max_signed_number ~u:max_unsigned_number
    let z = zero ~loc
    let one = one ~loc

    let eq ?g v e =
      let g' = aux `Grd in
      let eq = mkBinOp ~loc Eq (evar' v) e in
      push [set (var' g') @@ may_map (mkBinOp ~loc LAnd eq % evar') ~dft:eq g];
      `Var g'

    let eq1 e =
      function
      | Top
      | Bot
      | Top_or_bot _        -> `False
      | Val_or_top { g; v }
      | Mixed { g; v; _ }   -> eq ~g v e
      | Val_or_bot { v; _ }
      | Val v               -> eq v e

    let eq2 e1 e2 =
      match e1, e2 with
      | (Top
        | Bot
        | Top_or_bot _),                _
      | _,                              (Top
                                        | Bot
                                        | Top_or_bot _)                -> `False
      | (Val_or_top { g = g1; v = v1 }
        | Mixed { g = g1; v = v1; _ }), (Val_or_top { g = g2; v = v2 }
                                        | Mixed { g = g2; v = v2; _ }) -> `Var g1 &&? eq ~g:g2 v1 (evar' v2)
      | (Val_or_top { g; v = v1 }
        | Mixed { g; v = v1; _ }),      (Val_or_bot { v = v2; _ }
                                        | Val v2)
      | (Val_or_bot { v = v1; _ }
        | Val v1),                      (Val_or_top { g; v = v2 }
                                        | Mixed { g; v = v2; _ })      -> eq ~g v1 (evar' v2)
      | (Val_or_bot { v = v1; _ }
        | Val v1),                      (Val_or_bot { v = v2; _ }
                                        | Val v2)                      -> eq v1 (evar' v2)

    let binop b e1 e2 t =
      let p1, p2 = map_pair (isPointerType % typeOf) (e1, e2) in
      BinOp
        ((match b with
         | `Plus when p1        -> PlusPI
         | `Plus                -> PlusA Check
         | `Minus when p1 && p2 -> MinusPP
         | `Minus when p1       -> MinusPI
         | `Minus               -> MinusA Check
         | `Mult                -> Mult Check
         | `Div                 -> Div Check
         | `Mod                 -> Mod Check
         | `Shift_left          -> Shiftlt Check
         | `Shift_right         -> Shiftrt
         | `Lt                  -> Lt
         | `Gt                  -> Gt
         | `Le                  -> Le
         | `Ge                  -> Ge
         | `Eq                  -> Eq
         | `Ne                  -> Ne
         | `Bw_and              -> BAnd
         | `Bw_xor              -> BXor
         | `Bw_or               -> BOr
         | `And                 -> LAnd
         | `Or                  -> LOr),
         e1,
         e2,
         t)

    let split_g_a =
      function
      | Top                 -> `False, `True
      | Bot                 -> `False, `False
      | Top_or_bot a        -> `False, `Var a
      | Val_or_top { g; _ } -> `Var g, `True
      | Val_or_bot { a; _ } -> `True,  `Var a
      | Mixed { g; a; _ }   -> `Var g, `Var a
      | Val _               -> `True,  `True

    let value t =
      function
      | Top
      | Bot
      | Top_or_bot _        ->(let v = aux (`Val t) in
                               push @@ havoc_lval (var' v) [];
                               v)
      | Val_or_top { v; _ }
      | Val_or_bot { v; _ }
      | Mixed { v; _ }
      | Val v               -> v

    let elem ~g ~a v =
      match g, a with
      | `False, `True  -> Top
      | _,      `False -> Bot
      | `False, `Var a -> Top_or_bot a
      | `Var g, `True  -> Val_or_top { g; v = v () }
      | `True,  `Var a -> Val_or_bot { a; v = v () }
      | `Var g, `Var a -> Mixed { g; a; v = v () }
      | `True,  `True  -> Val (v ())

    let binary b e1 e2 t =
      let op v1 v2 =
        let v' = aux (`Val t) in
        push [set (var' v') @@ exp @@ binop b (evar' v1) (evar' v2) t];
        v'
      in
      let (g1, a1), (g2, a2) = map_pair split_g_a (e1, e2) in
      let w =
        if isIntegralType t then
          match b with
          | `Shift_right
            when isSignedInteger t       -> eq1 z e1 ||? eq1 (all_ones t) e1
          | (`Shift_left | `Shift_right) -> eq1 z e1
          | (`Mult| `Bw_and | `And)      -> eq1 z e1 ||? eq1 z e2
          | (`Div | `Mod)                -> eq1 z e1
          | `Lt                          -> eq1 (max_val t) e1 ||? eq1 (min_val t) e2
          | `Gt                          -> eq1 (min_val t) e1 ||? eq1 (max_val t) e2
          | `Ge                          -> eq1 (max_val t) e1 ||? eq1 (min_val t) e2
          | `Le                          -> eq1 (min_val t) e1 ||? eq1 (max_val t) e2
          | `Or                          -> eq1 one e1 ||? eq1 one e2
          | `Bw_or                       -> eq1 (all_ones t) e1 ||? eq1 (all_ones t) e2
          | #Symbolic.Op.binary          -> `False
        else                                `False
      in
      elem ~g:(g1 &&? g2 ||? w) ~a:(a1 &&? a2) (fun () -> op (value t e1) @@ value t e2)

    let ite =
      let op i t e ty =
        let v' = aux (`Val ty) in
        push [stmt @@ If (evar' i, mkBlock [set (var' v') @@ evar' t], mkBlock [set (var' v') @@ evar' e], loc)];
        v'
      in
      fun i t e ty ->
        let (gi, ai), (gt, at), (ge, ae) = split_g_a i, split_g_a t, split_g_a e in
        elem
          ~g:(gi &&? gt &&? ge ||? eq1 one i &&? gt ||? eq1 z i &&? ge ||? eq2 t e)
          ~a:(ai &&? at &&? ae)
          (fun () -> op (value intType i) (value ty t) (value ty e) ty)

    let var v =
      let v = try M_v.find v params with Not_found -> v in
      let v' = aux (`Val v.vtype) in
      push [set (var' v') @@ evar v];
      Val v'

    module H_stack = FCHashtbl.Make (Datatype.List (Stmt))

    type cache =
        C : 'r readables * ('c -> 'r Symbolic.t -> ('r Symbolic.t -> elem lazy_t) -> elem lazy_t) * 'c -> cache

    let get_def s =
      match s.skind with
      | Instr (Call (_, { enode = Lval (Var v, NoOffset); _ }, _, _)) ->(Kernel_function.get_definition @@
                                                                         Globals.Functions.get v)
      | _                                                             -> Console.fatal
                                                                           "Summaries.Local.get_def: not a direct call"

    let rec eval : type s. _ -> _ -> _ -> (module I.E.Local with type S.Symbolic.t = s) -> s -> _ =
      fun cache stack lcache ((module L') as l) v ->
        let C (r1, memo, c) = lcache in
        let Refl = eq_readables r1 L'.S.Symbolic.readable in
        let Refl = L'.S.Symbolic.eq in
        memo
          c
          v
          (fun v ->
             lazy
               (let eval' = eval cache stack lcache l in
                let let_ (type e cr) s (w : (L'.S.Symbolic.Readable.r, cr, e) binding) (e : e) (v : cr Symbolic.t) =
                  let f = get_def s in
                  let I.E.Some { local = (module L''); _ } = I.get info R.flag f in
                  let module S' = L''.S.Symbolic in
                  let stack = s :: stack in
                  match w with
                  | S'.W r ->(let Refl = eq_readables r S'.readable in
                              let Refl = S'.eq in
                              let lcache =
                                H_stack.memo
                                  cache
                                  stack
                                  (fun _ ->
                                     let c = S'.H.create 32 in
                                     let memo f k v =
                                       ignore @@ S'.H.memo c (S'.read @@ f k) (fun _ -> eval' v)
                                     in
                                     L''.F.Poly.Var.M.iter (memo (fun v -> `Poly_var v))   e.poly_vars;
                                     L''.F.Poly.Mem.M.iter (memo (fun m -> `Poly_mem m))   e.poly_mems;
                                     I.G.Var.M.iter        (memo (fun v -> `Global_var v)) e.global_vars;
                                     I.G.Mem.M.iter        (memo (fun m -> `Global_mem m)) e.global_mems;
                                     C (r, S'.H.memo, c))
                              in
                              Lazy.force @@ eval cache stack lcache (module L'') v)
                  | _      -> Console.fatal "Summaries.Local.eval: unexpected reads witness"
                in
                let eval = Lazy.force % eval' in
                begin match v.node with
                | Const (i, k)           -> const i k
                | Read (`Poly_var v)     -> var (v :> varinfo)
                | Read (`Global_var v)   -> var (v :> varinfo)
                | Read (`Poly_mem m)     -> mem (m :> R.t * fieldinfo option)
                | Read (`Global_mem m)   -> mem (m :> R.t * fieldinfo option)
                | Nondet (_, l)          -> nondet (typeOfLval l)
                | Top                    -> top
                | Bot                    -> bot
                | Ite (_, i, t, e, ty)   -> ite (eval i) (eval t) (eval e) ty
                | Unary (u, a, t)        -> unary u (eval a) t
                | Binary (b, a1, a2, ty) -> binary b (eval a1) (eval a2) ty
                | Let (s, w, e, v)       -> let_ s w e v
                end))

    (*let stmts_of_writes d d' =

      let mk_w =

        function
        | `Global_mem m -> mk_mem m
        | `Global_var v -> mk_var v
        | `Local_mem  _ -> `Skip
        | `Local_var  _ -> `Skip
        | `Poly_mem   m -> mk_mem m
        | `Poly_var   v -> mk_var v
        | `Result       -> `Var (var retvar)


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
