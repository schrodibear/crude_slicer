
[@@@warning "-42-44-45-48"]

open Cil_types
open Cil_datatype
open Cil
open Cil_printer
open Visitor
open Extlib

open Common
open Info

module Make (R : Region.Analysis) (M : sig val info : R.I.t end) = struct

  module I = R.I
  module R = struct
    include R.R
    include R
  end
  module U = R.U
  open M

  module Make_local
      (L : I.E.Local)
      (E : sig val eff : (L.A.t, L.R.t, L.S.t) I.E.t end)
      (Import : sig
         val w_lval : lval -> [> L.W.readable] option
       end)
  = struct
    module F = L.F
    module S = L.S
    module W = L.W
    open F
    open S
    open Import
    open Symbolic

    module Path_dd : sig
      type t
      val cut : exp -> V.t -> bool -> t -> t
      val merge : t -> t -> t
      val inst_v : V.t -> typ -> t -> V.t
      val inst_m : M.t -> typ -> t -> M.t
    end = struct
      type t =
        | Top
        | Bot
        | Ite of exp * V.t * t * t
      let rec merge t1 t2 =
        match t1, t2 with
        | Top,                  _
        | _,                    Top                      -> Top
        | Bot,                  t
        | t,                    Bot                      -> t
        | Ite (c0, s0, t1, e1), Ite (c1, s1, t2, e2)
          when Exp.equal c0 c1
            && V.equal s0 s1                             -> Ite (c0, s0, merge t1 t2, merge e1 e2)
        | Ite (c0, s0, t1, e1), (Ite (c1, _, _, _) as t)
          when Exp.compare c0 c1 < 0                     -> Ite (c0, s0, merge t1 t, merge e1 t)
        | t1,                   Ite (c, s, t, e)         -> Ite (c, s, merge t1 t, merge t1 e)
      let rec cut c s f =
        function
        | Top                        -> Ite (c, s, Top, Bot)
        | Bot                        -> Bot
        | Ite (c', s', t, e)
          when Exp.equal c c'
            && V.equal s s'          -> if f then t else e
        | Ite (c', _, _, _) as t
          when Exp.compare c c' < 0  -> Ite (c, s, t, Bot)
        | Ite (c', s', t, e)         -> Ite (c', s', cut c s f t, cut c s f e)
      module M_d =
        Map.Make
          (struct
            type t = exp * V.t
            let compare (e1, v1) (e2, v2) =
              let c = Exp.compare e1 e2 in
              if c <> 0 then c else V.compare v1 v2
          end)
      let rec opt : type k. (_ -> _ -> k u -> k u -> _ -> k u) -> _ -> k u -> k u =
        fun ite path v ->
          let Refl = eq in
          match v.Info.Symbolic.node with
          | Ite (c, s, t, e, _)
            when M_d.mem (c, s) path -> if M_d.find (c, s) path then opt ite path t else opt ite path e
          | Ite (c, s, t, e, ty)     -> ite
                                          c
                                          s
                                          (opt ite (M_d.add (c, s) true path) t)
                                          (opt ite (M_d.add (c, s) false path) e)
                                          ty
          | Top
          | Bot
          | Cst _
          | Adr _
          | Var _
          | Ndv _
          | Una _
          | Bin _
          | Sel _                    -> v
          | Let _                    -> v
          | Mem _                    -> v
          | Ndm _                    -> v
          | Upd _                    -> v
      let rec inst bot (ite : _ -> V.t -> _) path v ty =
        let Refl = eq in
        let inst c f = inst bot ite (M_d.add c f path) v ty in
        function
        | Top              -> opt ite path v
        | Bot              -> bot
        | Ite (c, s, t, e) -> ite c s (inst (c, s) true t) (inst (c, s) false e) ty
      let inst_v : V.t -> _ -> _ -> V.t = let Refl = eq in V.(inst bot ite) M_d.empty
      let inst_m : M.t -> _ -> _ -> M.t = let Refl = eq in M.(inst bot ite) M_d.empty
    end

    let loc = Location.unknown

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
                    | `Poly_var   v -> ensure ~init:init_v ~find:find_poly_var   ~set:set_poly_var v
                    | `Local_var  v -> ensure ~init:init_v ~find:find_local_var  ~set:set_local_var v
                    | `Global_mem m -> ensure ~init:init_m ~find:find_global_mem ~set:set_global_mem m >>= deref
                    | `Poly_mem   m -> ensure ~init:init_m ~find:find_poly_mem   ~set:set_poly_mem m   >>= deref
                    | `Local_mem  m -> ensure ~init:init_m ~find:find_local_mem  ~set:set_local_mem m  >>= deref) >>|
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

    let run = (|>)

    let assume stmt c flag (pdd, st) =
      let s, st = run st (eval_expr stmt c >>= get) in
      Path_dd.cut c s flag pdd, st

    let rec assign stmt lv e (pdd, st as state) =
      let Refl = S.eq in
      let Refl = eq in
      let ty = typeOf e in
      let set_v set vr =
        pdd,
        snd @@ run st (eval_expr stmt e >>= get >>= fun vl -> set vr @@ Path_dd.inst_v vl ty pdd : _ state)
      in
      let set_m find set m =
        pdd,
        snd @@
        run st
          (eval_lval stmt lv () >>= get >>= fun _ ->
           find m >>= get >>= fun mv ->
           eval_addr stmt lv >>= fun a ->
           eval_expr stmt e >>= get >>= fun v ->
           set m @@ Path_dd.inst_m (M.upd mv a v ty) ty pdd : _ state)
      in
      match w_lval lv with
      | Some (`Global_var v)                 -> set_v set_global_var v
      | Some (`Poly_var v)                   -> set_v set_poly_var v
      | Some (`Local_var v)                  -> set_v set_local_var v
      | Some (`Global_mem m)                 -> set_m find_global_mem set_global_mem m
      | Some (`Poly_mem m)                   -> set_m find_poly_mem set_poly_mem m
      | Some (`Local_mem m)                  -> set_m find_local_mem set_local_mem m
      | None                                 ->
        match[@warning "-4"] unrollType @@ typeOf e, e.enode with
        | TComp (ci, _, _), Lval lv'
          when ci.cstruct                    -> pdd,
                                                List.fold_left
                                                  (fun st fi ->
                                                     snd @@
                                                     assign
                                                       stmt
                                                       (addOffsetLval (Field (fi, NoOffset)) lv)
                                                       { e with
                                                         enode = Lval (addOffsetLval (Field (fi, NoOffset)) lv') }
                                                       (pdd, st))
                                                  st
                                                  ci.cfields
        | TComp (ci, _, _), Lval lv'         ->(let fi = List.hd ci.cfields in
                                                assign
                                                  stmt
                                                  (addOffsetLval (Field (fi, NoOffset)) lv)
                                                  { e with enode = Lval (addOffsetLval (Field (fi, NoOffset)) lv') }
                                                  state)
        | TArray (_, Some e, _, _), Lval lv' ->(let l = may_map ~dft:0 Integer.to_int @@ constFoldToInt e in
                                                pdd,
                                                Array.init l id |>
                                                Array.fold_left
                                                  ((fun st i ->
                                                     let i = integer ~loc i in
                                                     snd @@
                                                     assign
                                                       stmt
                                                       (addOffsetLval (Index (i, NoOffset)) lv)
                                                       { e with
                                                         enode = Lval (addOffsetLval (Index (i, NoOffset)) lv') }
                                                       (pdd, st)))
                                                  st)
        | TArray _,                 Lval _   -> state
        | _                                  -> Console.fatal "Symbolic.assign: unrecognized assignment: %a = %a"
                                                  pp_lval lv pp_exp e

    let retvar = Kf.retvar @@ Globals.Functions.get F.f.svar
    let retexp = opt_map (fun r -> if isStructOrUnionType r.vtype then mkAddrOf ~loc (var r) else evar r) retvar

    let mk_mem (r, fo) =
      let eo =
        opt_map
          (visitFramacExpr @@
           object
             inherit frama_c_inplace
             method! vexpr e =
               if R.Exp.is_ret e
               then ChangeTo (the retexp)
               else DoChildren
           end)
          (R.exp' r :> exp option)
      in
      opt_map
        (fun addr ->
           match fo with
           | None    -> mkMem ~addr ~off:NoOffset
           | Some fi -> mkMem ~addr ~off:(Field (fi, NoOffset)))
        eo

    let lval =
      let mem m =
        match mk_mem m with
        | Some lv -> lv
        | None    -> mkMem
                       ~addr:(mkCast
                                ~force:false
                                ~overflow:Check
                                ~e:(mkAddrOf ~loc @@ var F.f.svar)
                                ~newt:(TPtr ((fst m).R.typ, [])))
                       ~off:NoOffset
      in
      fun w ->
        match (w :> W.readable) with
        | `Global_var v -> var (v :> varinfo)
        | `Poly_var   v -> var (v :> varinfo)
        | `Local_var  v -> var (v :> varinfo)
        | `Global_mem m -> mem (m :> I.mem)
        | `Poly_mem   m -> mem (m :> I.mem)
        | `Local_mem  m -> mem (m :> I.mem)

    let type_of =
      let mem (r, fi) =
        match fi with
        | Some fi -> fi.ftype
        | None    -> r.R.typ
      in
      fun w ->
        match (w :> W.readable) with
        | `Global_var v -> (v :> varinfo).vtype
        | `Poly_var   v -> (v :> varinfo).vtype
        | `Local_var  v -> (v :> varinfo).vtype
        | `Global_mem m -> mem (m :> I.mem)
        | `Poly_mem   m -> mem (m :> I.mem)
        | `Local_mem  m -> mem (m :> I.mem)

    let one = CInt64 (Integer.one, IInt, None)

    let join_pre (v1 : V.t) (v2 : V.t) =
      let Refl = eq in
      match Info.Symbolic.(v1.node, v2.node) with
      | Cst (CInt64 (c, IInt, _)), v
        when Integer.is_one c                                -> V.cst one
      | v,                         Cst (CInt64 (c, IInt, _))
        when Integer.is_one c                                -> V.cst one
      | _,                         _                         -> V.bin `Or v1 v2 intType

    let call stmt ?lv kf es (pdd, s) : _ * S.t =
      let I.E.Some { local = (module L'); eff = eff' } = I.get info R.flag @@ Kernel_function.get_definition kf in
      let h_map = R.map stmt kf in
      let h_rev = R.H.create 512 in
      R.H_map.iter
        (fun u' u -> let r = U.repr u in R.H.replace h_rev r @@ R.S.add (U.repr u') @@ R.H.find_def h_rev r R.S.empty)
        h_map;
      let h_glob = R.H.create 16 in
      L'.A.iter
        (fun a f ->
           let handle =
             function
             | `Global_mem m -> R.H.replace h_glob (fst (m :> I.mem)) ()
             | #L'.W.t       -> ()
           in
           handle a;
           L'.R.iter handle f)
        (I.E.assigns eff');
      let h_clash = R.H.create 16 in
      R.H.iter
        (fun r s ->
           let s = if R.H.mem h_glob r then R.S.add r s else s in
           if R.S.cardinal s > 1 then R.S.iter (fun r' -> R.H.replace h_clash r' s) s)
        h_rev;
      let clashes =
        L'.A.fold
          (let writes (r, fi) mk =
             const @@
             if R.H.mem h_clash r then R.S.fold (L'.W.S.add % mk ?fi % U.of_repr) (R.H.find h_clash r) else id
           in
           function
           | `Global_var _
           | `Poly_var _
           | `Local_var _
           | `Local_mem _
           | `Result       -> const id
           | `Global_mem m -> writes (m :> I.mem) (fun ?fi u -> `Global_mem (I.G.Mem.mk ?fi u))
           | `Poly_mem m   -> writes (m :> I.mem) (fun ?fi u -> `Poly_mem (L'.F.Poly.Mem.mk ?fi u)))
          (I.E.assigns eff')
          L'.W.S.empty
      in
      let clashes =
        L'.A.fold
          (fun a f ->
             if
               L'.W.S.exists
                 (function
                 | #L'.W.readable as w -> L'.R.mem_some (L'.R.of_write w) f
                 | `Result             -> false)
                 clashes
             then L'.W.S.add a
             else id)
          (I.E.assigns eff')
          clashes
      in
      let check =
        let h = W.H.create 64 in
        fun w flag -> if W.H.memo h w (const flag) <> flag then Console.fatal "Symbolic.call: unexpected write clash"
      in
      let s' = I.E.summary eff' in
      let Refl = S.eq in
      let Refl = eq in
      let Refl = L'.S.eq in
      let Refl = L'.S.Symbolic.eq in
      let open L'.S in
      let open L'.S.Symbolic in
      let module V' = V in
      let module M' = M in
      let module V = S.Symbolic.V in
      let module M = S.Symbolic.M in
      let formals = Kernel_function.get_formals kf in
      let (es, s : V.t option list * S.t) =
        List.fold_right (fun e (es, s) -> map_fst (List.cons' es) @@ run s @@ eval_expr stmt e) es ([], s)
      in
      let prj_poly_var =
        let open List in
        let ass = combine (map (fun vi -> vi.vid) formals) @@ take (length formals) es in
        fun vi -> assoc vi.vid ass
      in
      let prj_poly_mem =
        let w_mem =
          let f = F.f.svar.vname in
          fun (r, fi) ->
            let u = R.H_map.find (U.of_repr r) h_map in
            match (U.repr u).R.kind with
            | `Global                          -> `Global_mem (I.G.Mem.mk ?fi u)
            | `Local f' when String.equal f f' -> `Local_mem  (Local.Mem.mk ?fi u)
            | `Poly f'  when String.equal f f' -> `Poly_mem   (Poly.Mem.mk ?fi u)
            | `Local f'
            | `Poly f'                         -> Console.fatal "Symbolic.call: broken invariant: writing to local \
                                                                 region %a of function %s from function %s"
                                                    R.pp (U.repr u) f' f
            | `Dummy                           -> Console.fatal "Symbolic.call: broken invariant: dummy region \
                                                                 encountered"
        in
        fun m -> w_mem (m : L'.F.Poly.Mem.t :> I.mem)
      in
      let inj_global_mem, inj_poly_mem, inj_local_mem =
        let w_mem =
          let f = L'.F.f.svar.vname in
          fun (r, fi) m ->
            R.S.fold
              (fun r ->
                 match r.R.kind with
                 | `Poly f' when String.equal f f' -> L'.F.Poly.Mem.(M.add (mk ?fi @@ U.of_repr r) m)
                 | #R.Kind.t                       -> id)
              (R.H.find_def h_rev r R.S.empty)
        in
        (fun m -> w_mem (m : I.G.Mem.t :> I.mem)),
        (fun m -> w_mem (m : Poly.Mem.t :> I.mem)),
        fun m -> w_mem (m : Local.Mem.t :> I.mem)
      in
      let env : _ env =
        let poly_vars : V.t L'.F.Poly.Var.M.t =
          L'.F.Poly.Var.(
            List.fold_right (fun v -> may_map (M.add @@ of_varinfo v) ~dft:id @@ prj_poly_var v) formals M.empty)
        in
        let poly_mems =
          L'.F.Poly.Mem.M.empty |>
          I.G.Mem.M.fold inj_global_mem s.post.global_mems |>
          Poly.Mem.M.fold inj_poly_mem s.post.poly_mems |>
          Local.Mem.M.fold inj_local_mem s.local_mems
        in
        {
          poly_vars;
          poly_mems;
          global_vars = s.post.global_vars;
          global_mems = s.post.global_mems
        }
      in
      let retvar' = Kf.retvar kf in
      let handle_v w' v s =
        let clashes = L'.W.S.mem (w' :> L'.W.t) clashes in
        match w' with
        | `Global_var g as w ->(check w clashes;
                                let v =
                                  if clashes
                                  then V.ndv stmt (lval w)
                                  else V'.prj stmt S.Symbolic.readable env v
                                in
                                snd @@ set_global_var g (Path_dd.inst_v v (type_of w) pdd) s)
        | `Result            ->(check `Result clashes;
                                let lv = the lv in
                                let ty = typeOfLval lv in
                                let v =
                                  if clashes
                                  then V.ndv stmt lv
                                  else V'.prj stmt S.Symbolic.readable env v
                                in
                                let set_v set vr = snd @@ set vr (Path_dd.inst_v v ty pdd) s in
                                let set_m find set m =
                                  snd @@
                                  run s
                                    (eval_lval stmt lv () >>= get >>= fun _ ->
                                     find m >>= get >>= fun mv ->
                                     eval_addr stmt lv >>= fun a ->
                                     set m @@ Path_dd.inst_m (M.upd mv a v ty) ty pdd)
                                in
                                match the (w_lval lv) with
                                | `Global_var v -> set_v set_global_var v
                                | `Poly_var v   -> set_v set_poly_var v
                                | `Local_var v  -> set_v set_local_var v
                                | `Global_mem m -> set_m find_global_mem set_global_mem m
                                | `Poly_mem m   -> set_m find_poly_mem set_poly_mem m
                                | `Local_mem m  -> set_m find_local_mem set_local_mem m)
      in
      let handle_m w' m s =
        let clashes = L'.W.S.mem (w' :> L'.W.t) clashes in
        let set set mem w =
          check (w :> W.t) clashes;
          let m =
            if clashes
            then M.ndm stmt (lval w)
            else M'.prj stmt S.Symbolic.readable env m
          in
          snd @@ set mem (Path_dd.inst_m m (type_of w) pdd) s
        in
        match w' with
        | `Global_mem g as w   -> set set_global_mem g w
        | `Poly_mem p'         ->
          match prj_poly_mem p' with
          | `Global_mem g as w -> set set_global_mem g w
          | `Poly_mem p as w   -> set set_poly_mem p w
          | `Local_mem l as w  -> set set_local_mem l w
      in
      let pre =
        let clashes =
          let deps' = I.E.depends eff' in
          L'.W.S.exists
            L'.R.(
              function
              | `Result             -> false
              | #L'.W.readable as w -> mem_some (of_write w) deps')
            clashes
        in
        let v =
          Path_dd.inst_v
            (if clashes
             then V.cst one
             else V'.prj stmt S.Symbolic.readable env s'.pre)
            intType
            pdd
        in
        S.Symbolic.V.merge ~join:join_pre s.pre v
      in
      pdd,
      { s with pre } |>
      I.G.Var.M.fold (fun v -> handle_v @@ `Global_var v) s'.post.global_vars |>
      I.G.Mem.M.fold (fun m -> handle_m @@ `Global_mem m) s'.post.global_mems |>
      L'.F.Poly.Mem.M.fold (fun m -> handle_m @@ `Poly_mem m) s'.post.poly_mems |>
      if has_some lv && not @@ isStructOrUnionType @@ Kernel_function.get_return_type kf
      then handle_v `Result L'.F.Local.Var.(M.find (of_varinfo @@ the retvar') s'.local_vars)
      else id
  end
end
