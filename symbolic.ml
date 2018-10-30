
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

    type 'a state = t -> 'a * t
    let (>>=) f1 f2 = f1 %> uncurry f2
    let return x s = x, s
    let (>>|) f1 f2 = f1 %> map_fst f2
    let read s = s, s
    let write s _ = (), s
    let get =
      function
      | Some x -> return x
      | None   -> Console.fatal "Symbolic.get: unexpected composite value"

    let find_global_var v = read >>| fun s -> I.G.Var.M.find_opt   v s.post.global_vars
    let find_global_mem m = read >>| fun s -> I.G.Mem.M.find_opt   m s.post.global_mems
    let find_poly_var   v = read >>| fun s -> Poly.Var.M.find_opt  v s.post.poly_vars
    let find_poly_mem   m = read >>| fun s -> Poly.Mem.M.find_opt  m s.post.poly_mems
    let find_local_var  v = read >>| fun s -> Local.Var.M.find_opt v s.local_vars
    let find_local_mem  m = read >>| fun s -> Local.Mem.M.find_opt m s.local_mems
    let set_global_var vr vl =
      read >>= fun s -> write { s with post = { s.post with global_vars = I.G.Var.M.add vr vl s.post.global_vars } }
    let set_global_mem m v =
      read >>= fun s -> write { s with post = { s.post with global_mems = I.G.Mem.M.add m v s.post.global_mems } }
    let set_poly_var vr vl =
      read >>= fun s -> write { s with post = { s.post with poly_vars = Poly.Var.M.add vr vl s.post.poly_vars } }
    let set_poly_mem m v =
      read >>= fun s -> write { s with post = { s.post with poly_mems = Poly.Mem.M.add m v s.post.poly_mems } }
    let set_local_var vr vl =
      read >>= fun s -> write { s with local_vars = Local.Var.M.add vr vl s.local_vars }
    let set_local_mem m v =
      read >>= fun s -> write { s with local_mems = Local.Mem.M.add m v s.local_mems }

    let rec eval_addr =
      let rec offset stmt ty acc =
        function
        | NoOffset        -> return acc
        | Field (fi, off) ->(let rty = TPtr (fi.ftype, []) in
                             offset
                               stmt
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
                             eval_expr stmt e >>= get >>= fun v ->
                             offset stmt ty (V.bin `Plus acc v @@ TPtr (ty, [])) off)
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
             let s = V.una (`Cast charPtrType) (V.ndv (List.hd d.sallstmts) @@ var d.svar) charPtrType in
             ignore
               (0 |>
                add s d.sformals |>
                add s d.slocals));
        H.find h
      in
      fun stmt (lh, off) ->
        match lh with
        | Var v when v.vglob -> offset stmt v.vtype (V.adr (Global_var.of_varinfo v)) off
        | Var v              -> offset stmt v.vtype (local v) off
        | Mem e              -> eval_expr stmt e >>= get >>= fun v -> offset stmt (typeOfLhost lh) v off
    and eval_lval =
      let ensure ~init ~find ~set x =
        find x >>=
        function
        | Some v -> return v
        | None   -> set x init >>| const init
      in
      fun stmt lv ?(init_v=V.ndv stmt lv) ?(init_m=M.ndm stmt lv) () : V.t option state ->
        let Refl = S.eq in
        let Refl = eq in
        let deref m : V.t state = eval_addr stmt lv >>| fun a -> V.sel m a @@ typeOfLval lv in
        match w_lval lv with
        | None   -> return None
        | Some w ->(w |>
                    (function
                    | `Global_var v -> ensure ~init:init_v ~find:find_global_var ~set:set_global_var v
                    | `Local_var  v -> ensure ~init:init_v ~find:find_local_var  ~set:set_local_var v
                    | `Poly_var   v -> ensure ~init:init_v ~find:find_poly_var   ~set:set_poly_var v
                    | `Global_mem m -> ensure ~init:init_m ~find:find_global_mem ~set:set_global_mem m >>= deref
                    | `Local_mem  m -> ensure ~init:init_m ~find:find_local_mem  ~set:set_local_mem m  >>= deref
                    | `Poly_mem   m -> ensure ~init:init_m ~find:find_poly_mem   ~set:set_poly_mem m   >>= deref) >>|
                    some)
    and eval_expr =
      let size s = return @@ some @@ V.cst @@ CInt64 (Integer.of_int s, theMachine.kindOfSizeOf, None) in
      fun stmt e ->
        let eval e = eval_expr stmt e >>= get in
        match e.enode with
        | Const c              -> return @@ some @@ V.cst c
        | Lval lv              -> eval_lval stmt lv ()
        | SizeOf ty            -> size @@ bytesSizeOf ty
        | SizeOfE e            -> size @@ bytesSizeOf @@ typeOf e
        | SizeOfStr s          -> size @@ String.length s + 1
        | AlignOf ty           -> size @@ bytesAlignOf ty
        | AlignOfE e           -> size @@ bytesAlignOf @@ typeOf e
        | UnOp (u, e, t)       -> eval e >>| fun e -> some @@ V.una (unop u) e t
        | BinOp (b, e1, e2, t) -> eval e1 >>= fun e1 -> eval e2 >>| fun e2 -> some @@ V.bin (binop b) e1 e2 t
        | CastE (ty, _, e)     -> eval e >>| fun e -> some @@ V.una (`Cast ty) e ty
        | AddrOf lv
        | StartOf lv           -> eval_addr stmt lv >>| some
        | Info (e, _)          -> eval_expr stmt e

    (*let assume*)
  end
end
