
[@@@warning "-42-44-45-48"]

open Cil_types
open Cil_datatype
open Cil
open Extlib

open Common
open Info

module Make (Analysis : Region.Analysis) = struct

  module I = Analysis.I

  module Make_local
      (L : I.E.Local)
      (E : sig val eff : (L.A.t, L.R.t, L.S.t) I.E.t end)
      (Import : sig
         val w_lval : lval -> [> L.W.readable] option
       end)
  = struct
    open L
    open F
    open S
    open Import

    module Path_trie : sig
      type t
      val cut : exp -> Symbolic.V.t -> bool -> t -> t
      val merge : t -> t -> t
      val inst_v : Symbolic.V.t -> typ -> t -> Symbolic.V.t
      val inst_m : Symbolic.M.t -> typ -> t -> Symbolic.M.t
    end = struct
      type t =
        | Top
        | Bot
        | Ite of exp * Symbolic.V.t * t * t
      let rec merge t1 t2 =
        match t1, t2 with
        | Top,                  _
        | _,                    Top                      -> Top
        | Bot,                  t
        | t,                    Bot                      -> t
        | Ite (c0, s0, t1, e1), Ite (c1, s1, t2, e2)
          when Exp.equal c0 c1
            && Symbolic.V.equal s0 s1                    -> Ite (c0, s0, merge t1 t2, merge e1 e2)
        | Ite (c0, s0, t1, e1), (Ite (c1, _, _, _) as t)
          when Exp.compare c0 c1 < 0                     -> Ite (c0, s0, merge t1 t, merge e1 t)
        | t1,                   Ite (c, s, t, e)         -> Ite (c, s, merge t1 t, merge t1 e)
      let rec cut c s f =
        function
        | Top                        -> Ite (c, s, Top, Bot)
        | Bot                        -> Bot
        | Ite (c', s', t, e)
          when Exp.equal c c'
            && Symbolic.V.equal s s' -> if f then t else e
        | Ite (c', _, _, _) as t
          when Exp.compare c c' < 0  -> Ite (c, s, t, Bot)
        | Ite (c', s', t, e)         -> Ite (c', s', cut c s f t, cut c s f e)
      let rec inst top bot ite v ty =
        function
        | Top              -> v
        | Bot              -> bot
        | Ite (c, s, t, e) -> ite c s (inst top bot ite v ty t) (inst top bot ite v ty e) ty
      let inst_v = Symbolic.V.(inst top bot ite)
      let inst_m = Symbolic.M.(inst top bot ite)
    end

    open Symbolic

    let unop =
      function
      | Neg _ -> `Minus
      | BNot  -> `Bw_neg
      | LNot  -> `Neg

    let binop =
      function
      | PlusA _
      | PlusPI
      | IndexPI   -> `Plus
      | MinusA _
      | MinusPI
      | MinusPP   -> `Minus
      | Mult _    -> `Mult
      | Div _     -> `Div
      | Mod _     -> `Mod
      | Shiftlt _ -> `Shift_left
      | Shiftrt   -> `Shift_right
      | Lt        -> `Lt
      | Gt        -> `Gt
      | Le        -> `Le
      | Ge        -> `Ge
      | Eq        -> `Eq
      | Ne        -> `Ne
      | BAnd      -> `Bw_and
      | BXor      -> `Bw_xor
      | BOr       -> `Bw_or
      | LAnd      -> `And
      | LOr       -> `Or

    let rec eval_addr =
      let rec offset s ty acc =
        function
        | NoOffset        -> acc
        | Field (fi, off) ->(let rty = TPtr (fi.ftype, []) in
                             offset
                               s
                               fi.ftype
                               (V.una
                                  (`Cast rty)
                                  (V.bin
                                     `Plus
                                     (V.una (`Cast charPtrType) acc charPtrType)
                                     (V.cst @@
                                      CInt64
                                        (Integer.of_int @@ (fst @@ bitsOffset ty @@ Field (fi, NoOffset)) lsr 3,
                                         theMachine.ptrdiffKind,
                                         None))
                                     charPtrType)
                                  rty)
                               off)
        | Index (e, off)  ->(let ty = Ast_info.direct_element_type ty in
                             offset
                               s
                               ty
                               (V.bin `Plus acc (the (eval_expr s e)) @@ TPtr (ty, []))
                               off)
      in
      let local =
        let module H = Varinfo.Hashtbl in
        let h = H.create 4096 in
        let add s =
          swap @@
          List.fold_left
            (fun acc vi ->
               let ty =
                 let ty = vi.vtype in
                 if isArrayType ty
                 then TPtr (Ast_info.direct_element_type ty, [])
                 else TPtr (ty, [])
               in
               H.add
                 h
                 vi
                 (V.una (`Cast ty) (V.bin `Plus s (V.cst @@ CInt64 (Integer.of_int acc, IInt, None)) charPtrType) ty);
               acc + bytesSizeOf vi.vtype)
        in
        Globals.Functions.iter_on_fundecs
          (fun d ->
             let s = V.una (`Cast charPtrType) (V.ndt (List.hd d.sallstmts) @@ var d.svar) charPtrType in
             ignore
               (0 |>
                add s d.sformals |>
                add s d.slocals));
        H.find h
      in
      fun s (lh, off) ->
        match lh with
        | Var v when v.vglob -> offset s v.vtype (V.adr (Global_var.of_varinfo v)) off
        | Var v              -> offset s v.vtype (local v) off
        | Mem e              -> offset s (typeOfLhost lh) (the (eval_expr s e)) off
    and eval_lval s lv : Symbolic.tv option =
      let open Symbolic in
      let Refl = Symbolic.eq in
      opt_map
        (function
        | `Global_var v -> I.G.Var.M.find   v s.post.global_vars
        | `Local_var  v -> Local.Var.M.find v s.local_vars
        | `Poly_var   v -> Poly.Var.M.find  v s.post.poly_vars
        | `Global_mem m -> V.sel (I.G.Mem.M.find m s.post.global_mems) (eval_addr s lv) (typeOfLval lv)
        | `Local_mem  m -> V.sel (Local.Mem.M.find m s.local_mems)     (eval_addr s lv) (typeOfLval lv)
        | `Poly_mem   m -> V.sel (Poly.Mem.M.find m s.post.poly_mems)  (eval_addr s lv) (typeOfLval lv))
        (w_lval lv)
    and eval_expr =
      let size s = some @@ V.cst @@ CInt64 (Integer.of_int s, theMachine.kindOfSizeOf, None) in
      fun s e ->
        let eval e = the (eval_expr s e) in
        match e.enode with
        | Const c              -> some @@ V.cst c
        | Lval lv              -> eval_lval s lv
        | SizeOf ty            -> size @@ bytesSizeOf ty
        | SizeOfE e            -> size @@ bytesSizeOf @@ typeOf e
        | SizeOfStr s          -> size @@ String.length s + 1
        | AlignOf ty           -> size @@ bytesAlignOf ty
        | AlignOfE e           -> size @@ bytesAlignOf @@ typeOf e
        | UnOp (u, e, t)       -> some @@ V.una (unop u) (eval e) t
        | BinOp (b, e1, e2, t) -> some @@ V.bin (binop b) (eval e1) (eval e2) t
        | CastE (ty, _, e)     -> some @@ V.una (`Cast ty) (eval e) ty
        | AddrOf lv
        | StartOf lv           -> some @@ eval_addr s lv
        | Info (e, _)          -> eval_expr s e

    (*let assume*)
  end
end
