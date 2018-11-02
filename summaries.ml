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

[@@@warning "-42-44-45-48"]

open Extlib

open Cil_types
open Cil_datatype
open Cil
open Visitor

open! Common
open Info

let ensure_havoc_function_present () = Kf.ensure_proto voidType (Options.Havoc_function.get ()) [voidPtrType] true
let ensure_choice_function_present () = Kf.ensure_proto ulongLongType (Options.Choice_function.get ()) [intType] true
let ensure_alloc_function_present () =
  Kf.ensure_proto voidPtrType (Options.Alloc_function.get ()) [theMachine.upointType] false
let ensure_memory_function_present () =
  Kf.ensure_proto voidConstPtrType (Options.Memory_function.get ()) [voidConstPtrType] false
let ensure_select_function_present () =
  Kf.ensure_proto ulongLongType (Options.Select_function.get ()) [voidConstPtrType; voidConstPtrType] false
let ensure_update_function_present () =
  Kf.ensure_proto
    voidConstPtrType (Options.Update_function.get ()) [voidConstPtrType; voidConstPtrType; ulongLongType] false
let ensure_const_function_present () =
  Kf.ensure_proto voidConstPtrType (Options.Const_function.get ()) [ulongLongType] false
let ensure_nondet_mem_function_present () =
  Kf.ensure_proto voidConstPtrType (Options.Nondet_mem_function.get ()) [] false
let ensure_assign_function_present () =
  Kf.ensure_proto voidType (Options.Assign_function.get ()) [voidConstPtrType; voidConstPtrType] false
let ensure_assume_function_present () = Kf.ensure_proto voidType (Options.Assume_function.get ()) [intType] false
let ensure_error_function_present () = Kf.ensure_proto voidType (Options.Error_function.get ()) [] false

module Make (R : Region.Analysis) (M : sig val info : R.I.t end) = struct
  module I = R.I
  module R = struct
    include R.R
    include R
  end
  module U = R.U
  open M

  module Make_local (L : I.E.Local) (E : sig val eff : (L.A.t, L.R.t, L.S.t) I.E.t end) = struct
    module F = L.F
    open F

    type value = [`V | `M] * Local.Var.t

    type elem =
      | Top
      | Bot
      | Top_or_bot of Local.Var.t
      | Val_or_top of { g : Local.Var.t; v : value }
      | Val_or_bot of { a : Local.Var.t; v : value }
      | Mixed of { a : Local.Var.t; g : Local.Var.t; v : value }
      | Val of value

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
        ~name:
          (match kind with
          | `Grd         -> "grd"
          | `Ass         -> "ass"
          | `Val (`V, _) -> "var"
          | `Val (`M, _) -> "mem"
          | `Tmp _       -> "tmp")
        (match kind with
        | `Grd | `Ass           -> intType
        | `Val (`V, t) | `Tmp t -> t
        | `Val (`M, t)          -> TPtr (typeAddAttributes [Attr ("const", [])] t, []))
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
    let alloc =
      let alloc = get_vi @@ Options.Alloc_function.get () in
      fun lv sz -> [call ~lv alloc [sz]]
    let havoc_mem =
      let havoc = get_vi @@ Options.Havoc_function.get () in
      fun e es -> [call havoc @@ e :: limit es]
    let get_mem =
      let mem = get_vi @@ Options.Memory_function.get () in
      fun lv e -> [call ~lv mem [e]]
    let select =
      let sel = get_vi @@ Options.Select_function.get () in
      fun lv m a ->
        let tmp = aux (`Tmp ulongLongType) in
        [call ~lv:(var' tmp) sel [m; a];
         set lv @@ mkCast ~force:false ~overflow:Check ~e:(evar' tmp) ~newt:(typeOfLval lv)]
    let update =
      let upd = get_vi @@ Options.Update_function.get () in
      fun lv m a v -> [call ~lv upd [m; a; v]]
    let const_mem =
      let cst = get_vi @@ Options.Const_function.get () in
      fun lv v -> [call ~lv cst [v]]
    let nondet_mem =
      let ndm = get_vi @@ Options.Nondet_mem_function.get () in
      fun lv -> [call ~lv ndm []]
    let assign =
      let ass = get_vi @@ Options.Assign_function.get () in
      fun m1 m2 -> [call ass [m1; m2]]
    let assume =
      let ass = get_vi @@ Options.Assume_function.get () in
      fun a -> [call ass [a]]
    let error =
      let err = get_vi @@ Options.Error_function.get () in
      fun () -> [call err []]

    let push, stmts =
      let stmts = Queue.create () in
      List.iter (swap Queue.add @@ stmts), fun () -> Queue.to_seq stmts

    let conv k (k', v) =
      match k, k' with
      | `V, `V
      | `M, `M -> v
      | `M, `V ->(let m = aux @@ `Val (`M, (v : Local.Var.t :> varinfo).vtype) in
                  push @@ const_mem (var' m) @@ evar' v;
                  m)
      | `V, `M -> Console.fatal "Summaries.Local.conv: malformed symbolic value of incompatible kind"

    let top = Top

    let bot = Bot

    let cst k c =
      let v = aux @@ `Val (`V, typeOf @@ exp @@ Const c) in
      push [set (var' v) @@ exp @@ Const c];
      Val (k, conv k (`V, v))

    let adr k g =
      let v = aux @@ `Val (`V, TPtr ((g : Global_var.t :> varinfo).vtype, [])) in
      push [set (var' v) @@ mkAddrOrStartOf ~loc @@ var (g :> varinfo)];
      Val (k, conv k (`V, v))

    let vrb k v =
      let v = try M_v.find v params with Not_found -> v in
      let v' = aux (`Val (`V, v.vtype)) in
      push [set (var' v') @@ evar v];
      Val (k, conv k (`V, v'))

    let mem m =
      match mk_mem m with
      | Some e ->(let m = aux @@ `Val (`M, typeOf e) in
                  push @@ get_mem (var' m) e;
                  Val (`M, m))
      | None   -> Console.fatal "Summaries.Local.mem: unexpected dangling region: should have been eliminated"

    let ndm ty =
      let m = aux @@ `Val (`M, ty) in
      push @@ nondet_mem @@ var' m;
      Val (`M, m)

    let unop u e t =
      match u with
      | `Cast t   -> CastE (t, Check, e)
      | `Minus
      | `Bw_neg
      | `Neg as u -> UnOp
                       ((match u with
                        | `Minus  -> Neg Check
                        | `Bw_neg -> BNot
                        | `Neg    -> LNot),
                        e,
                        t)

    let una k u e t =
      let op v =
        let v = conv `V v in
        let v' = aux (`Val (`V, t)) in
        push [set (var' v') @@ exp @@ unop u (evar' v) t];
        k, conv k (`V, v')
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
      | `True,   _
      | _,       `True   -> `True
      | `False,  `False  -> `False
      | `False,  `Var v
      | `Var v,  `False  -> `Var v
      | `Var v1, `Var v2 ->(let g = aux `Grd in
                            push [set (var' g) @@ mkBinOp ~loc BOr (evar' v1) @@ evar' v2];
                            `Var g)

    let ikind t =
      match[@warning "-4"] unrollType t with
      | TInt (i, _) -> i
      | _           -> Console.fatal "Summaries.Local.ikind: unexpected type"
    let get_val ~s ~u t =
      exp @@ Const (CInt64 ((if isSignedInteger t then s else u) @@ bitsSizeOf t, ikind t, None))
    let all_ones = get_val ~s:min_signed_number ~u:max_unsigned_number
    let min_val  = get_val ~s:min_signed_number ~u:(fun _ -> Integer.zero)
    let max_val  = get_val ~s:max_signed_number ~u:max_unsigned_number
    let z = zero ~loc
    let one = one ~loc

    let eq ?(n=false) ?g v e =
      let g' = aux `Grd in
      let eq = mkBinOp ~loc (if n then Ne else Eq) (evar' v) e in
      push [set (var' g') @@ may_map (mkBinOp ~loc LAnd eq % evar') ~dft:eq g];
      `Var g'
    let neq = eq ~n:true

    let eq1 ?n e =
      function
      | Top
      | Bot
      | Top_or_bot _        -> `False
      | Val_or_top { g; v }
      | Mixed { g; v; _ }   -> eq ?n ~g (conv `V v) e
      | Val_or_bot { v; _ }
      | Val v               -> eq ?n (conv `V v) e
    let neq1 = eq1 ~n:false
    let eq1 = eq1 ~n:true
    let eq = eq ~n:true

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
                                        | Mixed { g = g2; v = v2; _ }) -> `Var g1 &&?
                                                                          eq ~g:g2 (conv `V v1) (evar' @@ conv `V v2)
      | (Val_or_top { g; v = v1 }
        | Mixed { g; v = v1; _ }),      (Val_or_bot { v = v2; _ }
                                        | Val v2)
      | (Val_or_bot { v = v1; _ }
        | Val v1),                      (Val_or_top { g; v = v2 }
                                        | Mixed { g; v = v2; _ })      -> eq ~g (conv `V v1) (evar' @@ conv `V v2)
      | (Val_or_bot { v = v1; _ }
        | Val v1),                      (Val_or_bot { v = v2; _ }
                                        | Val v2)                      -> eq (conv `V v1) (evar' @@ conv `V v2)

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
      | Mixed { a; g; _ }   -> `Var g, `Var a
      | Val _               -> `True,  `True

    let value k t =
      function
      | Top
      | Bot
      | Top_or_bot _        ->(let v = aux (`Val (k, t)) in
                               push
                                 (match k with
                                 | `V -> havoc_lval (var' v) []
                                 | `M -> nondet_mem (var' v));
                               k, v)
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
      | `Var g, `Var a -> Mixed { a; g; v = v () }
      | `True,  `True  -> Val (v ())

    let ndv k ty size =
      let v = aux (`Val (`V, ty)) in
      push
        (match size with
        | None   -> havoc_lval (var' v) []
        | Some s -> alloc (var' v) @@ evar' @@ conv `V @@ value `V theMachine.upointType s);
      Val (k, conv k (`V, v))

    let bin k b e1 e2 t =
      let op v1 v2 =
        let v1, v2 = map_pair (conv `V) (v1, v2) in
        let v' = aux (`Val (`V, t)) in
        push [set (var' v') @@ exp @@ binop b (evar' v1) (evar' v2) t];
        k, conv k (`V, v')
      in
      let (g1, a1), (g2, a2) = map_pair split_g_a (e1, e2) in
      let wg =
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
          | `Or                          -> neq1 z e1 ||? neq1 z e2
          | `Bw_or                       -> eq1 (all_ones t) e1 ||? eq1 (all_ones t) e2
          | #Symbolic.Op.binary          -> `False
        else                                `False
      in
      let wa =
        match b with
        | `Or                 -> neq1 z e1
        | `And                -> eq1 z e1
        | #Symbolic.Op.binary -> `False
      in
      elem ~g:(g1 &&? g2 ||? wg) ~a:(a1 &&? (a2 ||? wa)) (fun () -> op (value `V t e1) @@ value `V t e2)

    let is_const =
      function
      | Top
      | Bot
      | Top_or_bot _        -> false
      | Val_or_top { v; _ }
      | Val_or_bot { v; _ }
      | Mixed { v; _ }
      | Val v               -> fst v = `V

    let sel k m a t =
      let (gm, am), (ga, aa) = map_pair split_g_a (m, a) in
      elem
        ~g:(gm &&? if is_const m then `True else ga)
        ~a:(am &&? aa)
        (fun () ->
           let m = conv `M (value `M t m) in
           let a = conv `V @@ value `V (TPtr (t, [])) a in
           let v = aux (`Val (`V, t)) in
           push @@ select (var' v) (evar' m) @@ evar' a;
           k, conv k (`V, v))

    let upd m a v t =
      let (gm, am), (ga, aa), (gv, av) = split_g_a m, split_g_a a, split_g_a v in
      elem
        ~g:(gm &&? (ga &&? gv ||? if is_const m then eq2 m v else `False))
        ~a:(am &&? aa &&? av)
        (fun () ->
           let m = conv `M (value `M t m) in
           let a = conv `V @@ value `V (TPtr (t, [])) a in
           let v = conv `V @@ value `V t v in
           let m' = aux (`Val (`M, t)) in
           push @@ update (var' m') (evar' m) (evar' a) (evar' v);
           `M, m')

    let ite =
      let op k i t e ty =
        let i = conv `V i in
        let t, e = map_pair (conv k) (t, e) in
        let v' = aux (`Val (k, ty)) in
        push [stmt @@ If (evar' i, mkBlock [set (var' v') @@ evar' t], mkBlock [set (var' v') @@ evar' e], loc)];
        k, v'
      in
      fun k i t e ty ->
        let (gi, ai), (gt, at), (ge, ae) = split_g_a i, split_g_a t, split_g_a e in
        elem
          ~g:(gi &&? gt &&? ge ||? neq1 z i &&? gt ||? eq1 z i &&? ge ||? eq2 t e)
          ~a:(ai &&? (neq1 z i &&? at ||? eq1 z i &&? ae))
          (fun () -> op k (value `V intType i) (value k ty t) (value k ty e) ty)

    module H_stack = FCHashtbl.Make (Datatype.List (Stmt))

    type cache =
        C :
          ('v, 'm) readables *
          ('cv -> ('v, 'm, [`V]) Symbolic.t -> (('v, 'm, [`V]) Symbolic.t -> elem lazy_t) -> elem lazy_t) *
          'cv *
          ('cm -> ('v, 'm, [`M]) Symbolic.t -> (('v, 'm, [`M]) Symbolic.t -> elem lazy_t) -> elem lazy_t) *
          'cm
        -> cache

    let get_def s =
      match[@warning "-4"] s.skind with
      | Instr (Call (_, { enode = Lval (Var v, NoOffset); _ }, _, _)) ->(Kernel_function.get_definition @@
                                                                         Globals.Functions.get v)
      | _                                                             -> Console.fatal
                                                                           "Summaries.Local.get_def: not a direct call"

    let conv_elem k =
      function
      | Top -> Top
      | Bot -> Bot
      | Top_or_bot _ as t   -> t
      | Val_or_top { g; v } -> Val_or_top { g; v = k, conv k v }
      | Val_or_bot { a; v } -> Val_or_bot { a; v = k, conv k v }
      | Mixed { a; g; v }   -> Mixed { a; g; v = k, conv k v }
      | Val v               -> Val (k, conv k v)

    let rec eval :
      type tv tm. _ -> _ -> _
      -> (module I.E.Local with type S.Symbolic.tv = tv and type S.Symbolic.tm = tm)
      -> [ `V of tv | `M of tm ] -> _ =
      fun cache stack lcache ((module L') as l) s ->
        let C (r, memo_v, cv, memo_m, cm) = lcache in
        let module S' = L'.S.Symbolic in
        let Refl = eq_readables r S'.readable in
        let Refl = S'.eq in
        let memo f =
          match s with
          | `V v ->(let e = memo_v cv v (fun v -> f @@ `V v) in
                    ignore @@ memo_m cm (Symbolic.coerce v) (fun _ -> lazy (conv_elem `M @@ Lazy.force e));
                    e)
          | `M m -> memo_m cm m (fun m -> f @@ `M m)
        in
        memo @@
        fun s ->
        lazy
          (let eval' = eval cache stack lcache l in
           let let_
                 (type cev cem cee)
                 stmt
                 (w : < crv : S'.Readable.v; crm : S'.Readable.m; cev : cev; cem : cem; cee : cee > binding)
                 (e : cee)
                 (s : [ `V of (cev, cem, _) Symbolic.t | `M of (cev, cem, _) Symbolic.t ]) =
             let f = get_def stmt in
             let I.E.Some { local = (module L''); _ } = I.get info R.flag f in
             let module S'' = L''.S.Symbolic in
             let stack = stmt :: stack in
             match w with
             | S''.W r ->(let Refl = eq_readables r S''.readable in
                          let Refl = S''.eq in
                          let lcache =
                            H_stack.memo
                              cache
                              stack
                              (fun _ ->
                                 let cv = S''.V.H.create 32 in
                                 let cm = S''.M.H.create 32 in
                                 let memo_v f k v =
                                   ignore @@ S''.V.H.memo cv (S''.V.var @@ f k) (fun _ -> eval' @@ `V v)
                                 in
                                 let memo_m f k m =
                                   ignore @@ S''.M.H.memo cm (S''.M.mem @@ f k) (fun _ -> eval' @@ `M m)
                                 in
                                 L''.F.Poly.Var.M.iter (memo_v (fun v -> `Poly_var v))   e.S''.poly_vars;
                                 L''.F.Poly.Mem.M.iter (memo_m (fun m -> `Poly_mem m))   e.S''.poly_mems;
                                 I.G.Var.M.iter        (memo_v (fun v -> `Global_var v)) e.S''.global_vars;
                                 I.G.Mem.M.iter        (memo_m (fun m -> `Global_mem m)) e.S''.global_mems;
                                 C (r, S''.V.H.memo, cv, S''.M.H.memo, cm))
                          in
                          Lazy.force @@ eval cache stack lcache (module L'') s)
             | _      -> Console.fatal "Summaries.Local.eval: unexpected reads witness"
           in
           let eval = Lazy.force % eval' in
           let k = match s with `V _ -> `V | `M _ -> `M in
           let open Symbolic in
           match s with
           | `V { node = Top; _ }
           | `M { node = Top; _ }                  -> top
           | `V { node = Bot; _ }
           | `M { node = Bot; _ }                  -> bot
           | `V { node = Cst c; _ }
           | `M { node = Cst c; _ }                -> cst k c
           | `V { node = Adr g; _ }
           | `M { node = Adr g; _ }                -> adr k g
           | `V { node = Var (`Poly_var v); _ }
           | `M { node = Var (`Poly_var v); _ }    -> vrb k (v :> varinfo)
           | `V { node = Var (`Global_var v); _ }
           | `M { node = Var (`Global_var v); _ }  -> vrb k (v :> varinfo)
           | `M { node = Mem (`Poly_mem m); _ }    -> mem (m :> R.t * fieldinfo option)
           | `M { node = Mem (`Global_mem m); _ }  -> mem (m :> R.t * fieldinfo option)
           | `V { node = Ndv (_, l, s); _ }
           | `M { node = Ndv (_, l, s); _ }        -> ndv k (typeOfLval l) (opt_map (fun v -> eval @@ `V v) s)
           | `M { node = Ndm (_, l); _ }           -> ndm (typeOfLval l)
           | `V { node = Una (u, a, t); _ }
           | `M { node = Una (u, a, t); _ }        -> una k u (eval @@ `V a) t
           | `V { node = Bin (b, a1, a2, t); _ }
           | `M { node = Bin (b, a1, a2, t); _ }   -> bin k b (eval @@ `V a1) (eval @@ `V a2) t
           | `V { node = Sel (m, a, t); _ }
           | `M { node = Sel (m, a, t); _ }        -> sel k (eval @@ `M m) (eval @@ `V a) t
           | `M { node = Upd (m, a, v, t); _ }     -> upd (eval @@ `M m) (eval @@ `V a) (eval @@ `V v) t
           | `V { node = Ite (_, i, t, e, ty); _ } -> ite k (eval @@ `V i) (eval @@ `V t) (eval @@ `V e) ty
           | `M { node = Ite (_, i, t, e, ty); _ } -> ite k (eval @@ `V i) (eval @@ `M t) (eval @@ `M e) ty
           | `V { node = Let (s, w, e, v); _ }     -> let_ s w e (`V v)
           | `M { node = Let (s, w, e, m); _ }     -> let_ s w e (`M m))

    let assign =
      let mk_w =
        let mk_mem m = may_map (fun m -> `Mem m) ~dft:`Skip @@ mk_mem m in
        fun w ->
          if
            match w with
            | `Result            -> I.E.has_result_dep E.eff
            | #L.W.readable as w -> L.R.(mem_some (of_write w) @@ I.E.depends E.eff)
          then
            match (w : L.W.t :> I.writable) with
            | `Global_mem m -> mk_mem m
            | `Global_var v -> `Var (mk_var v)
            | `Local_mem  _ -> `Skip
            | `Local_var  v -> `Var (mk_var v)
            | `Poly_mem   m -> mk_mem m
            | `Poly_var   v -> `Var (mk_var v)
            | `Result       -> `Var (var retvar)
          else
            `Skip
      in
      let insert k v m =
        let open Local.Var.M in
        match find k m with
        | l                   -> add k (v :: l) m
        | exception Not_found -> add k [] m
      in
      fun l ->
        let (tops, grds, vals, bots) =
          List.fold_left
            (fun (tops, grds, vals, bots) (w, e) ->
               match e with
               | Top
               | Top_or_bot _        -> w :: tops, grds,                     vals,               bots
               | Bot                 -> tops,      grds,                     vals,               w :: bots
               | Val_or_top { g; v }
               | Mixed { g; v; _ }   -> tops,      insert g (w, snd v) grds, vals,               bots
               | Val_or_bot { v; _ }
               | Val v               -> tops,      grds,                     (w, snd v) :: vals, bots)
            ([], Local.Var.M.empty, [], [])
            l
        in
        if bots = [] then
          let froms w =
            List.rev @@
            L.R.fold
              (fun r ->
                 match mk_w r with
                 | `Var lv -> List.cons @@ new_exp ~loc (Lval lv)
                 | `Mem e  -> List.cons e
                 | `Skip   -> id)
              (L.A.find w @@ I.E.assigns E.eff)
              []
          in
          let nondet w =
            match mk_w w with
            | `Var lv -> havoc_lval lv (froms w)
            | `Mem e  -> havoc_mem  e  (froms w)
            | `Skip   -> []
          in
          let sym w v =
            match mk_w w with
            | `Var lv -> [set lv (evar' v)]
            | `Mem e  -> assign e (evar' v)
            | `Skip   -> []
          in
          List.iter (push % nondet) tops;
          Local.Var.M.iter
            (fun g wvs ->
               let det = mkBlock @@ List.concat_map (uncurry sym) wvs in
               let nondet = mkBlock @@ List.concat_map (uncurry @@ const' nondet) wvs in
               push [stmt @@ If (evar' g, det, nondet, loc)])
            grds;
          List.iter (push % uncurry sym) vals

    let assume l =
      push @@
      assume
        (List.concat_map
           (function
           | Top
           | Val _
           | Val_or_top _        -> []
           | Bot                 -> [z]
           | Top_or_bot a
           | Val_or_bot { a; _ }
           | Mixed { a; _ }      -> [evar' a])
           l |>
         function
         | a :: ass -> List.fold_left (fun acc a -> mkBinOp ~loc BAnd acc a) a ass
         | []       -> one)

    let body () =
      let s = I.E.summary E.eff in
      let Refl = L.S.eq in
      let Refl = L.S.Symbolic.eq in
      let open L.S in
      let open L.S.Symbolic in
      let rvo = Kf.retvar @@ Globals.Functions.get F.f.svar in
      let cache = H_stack.create 4 in
      let lcache = C (readable, V.H.memo, V.H.create 32, M.H.memo, M.H.create 32) in
      H_stack.add cache [] lcache;
      let eval = Lazy.force % eval cache [] lcache (module L) in
      let pre = eval @@ `V s.pre in
      let ass =
        [] |>
        L.F.Poly.Mem.M.fold (fun m v -> List.cons (`Poly_mem m, eval @@ `M v)) s.post.poly_mems |>
        I.G.Mem.M.fold (fun m v -> List.cons (`Global_mem m, eval @@ `M v)) s.post.global_mems |>
        I.G.Var.M.fold (fun vr vl -> List.cons (`Global_var vr, eval @@ `V vl))  s.post.global_vars |>
        L.F.Local.Var.M.fold
          (fun vr vl ->
             if may_map ~dft:false (Varinfo.equal (vr :> varinfo)) rvo
             then List.cons (`Result, eval @@ `V vl)
             else id)
          s.local_vars
      in
      assume [pre];
      let p = aux `Grd in
      assign [`Local_var p, pre];
      push @@ [stmt @@ If (evar' p, mkBlock @@ error (), mkBlock [], loc)];
      assume @@ List.map snd ass;
      assign ass;
      if not (isVoidType retvar.vtype) then push [stmt @@ Return (Some (evar retvar), loc)]
  end

  let generate =
    let open List in
    let module H_d = Fundec.Hashtbl in
    let module S_d = Fundec.Set in
    let h_ins = H_d.create 256 in
    fun sccs ->
      ensure_havoc_function_present ();
      ensure_choice_function_present ();
      ensure_alloc_function_present ();
      ensure_memory_function_present ();
      ensure_select_function_present ();
      ensure_update_function_present ();
      ensure_const_function_present ();
      ensure_nondet_mem_function_present ();
      ensure_assign_function_present ();
      ensure_assume_function_present ();
      ensure_error_function_present ();
      let ds = sccs |> flatten |> Kernel_function.(filter_map is_definition get_definition) |> S_d.of_list in
      let file = Ast.get () in
      visitFramacFile
        (object
          inherit frama_c_inplace
          method! vfunc d =
            let name = d.svar.vname in
            if S_d.mem d ds
            && not (Options.(Alloc_functions.mem name || Assume_functions.mem name || Path_assume_functions.mem name))
            then
              H_d.add h_ins d d;
            SkipChildren
        end)
        file;
      H_d.filter_map_inplace
        (fun _ d ->
           let I.E.Some { local = (module L); eff } = I.get info R.flag d in
           let module L = Make_local (L) (struct let eff = eff end) in
           L.body ();
           some @@ L.f)
        h_ins;
      ignore @@
      visitFramacFile
        (object
          inherit frama_c_inplace
          method! vglob_aux =
            function
              [@warning "-4"]
            | GFun (d, _) as g when H_d.mem h_ins d -> ChangeTo [g; GFun (H_d.find h_ins d, Location.unknown)]
            | _                                     -> SkipChildren
        end)
        file;
      H_d.clear h_ins
end
