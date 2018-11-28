
[@@@warning "-42-44-45-48"]

open Cil_types
open Cil_datatype
open Cil
open Cil_printer
open Visitor
open Extlib
open Format

open Common
open Info

module Make
    (R : Region.Analysis)
    (M : sig val info : R.I.t end)
    (Import : functor (L : R.I.E.Local) -> sig val w_lval : lval -> [> L.W.readable] option end) = struct

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

    let var = Cil.var

    module Path_dd : sig
      type t
      val top : t
      val bot : t
      val cut : exp -> V.t -> bool -> t -> t
      val merge : t -> t -> t
      val inst_v : V.t -> typ -> t -> V.t
      val inst_m : M.t -> typ -> t -> M.t
      val pp : formatter -> t -> unit
    end = struct
      type t =
        | Top
        | Bot
        | Ite of exp * V.t * t * t
      let top = Top
      let bot = Bot
      let ite c s t e =
        match t, e with
        | Top,      Top -> Top
        | Bot,      Bot -> Bot
        | (Top
          | Bot
          | Ite _), _   -> Ite (c, s, t, e)
      let rec merge t1 t2 =
        match t1, t2 with
        | Top,                  _
        | _,                    Top                       -> Top
        | Bot,                  t
        | t,                    Bot                       -> t
        | Ite (c0, s0, t1, e1), Ite (c1, s1, t2, e2)
          when Exp.equal c0 c1
            && V.equal s0 s1                              -> ite c0 s0 (merge t1 t2) (merge e1 e2)
        | Ite (c0, s0, t1, e1), (Ite (c1, s1, _, _) as t)
          when Exp.compare c0 c1 < 0
            ||  Exp.compare c0 c1 = 0 &&
                V.compare s0 s1 < 0                       -> ite c0 s0 (merge t1 t) (merge e1 t)
        | t1,                   Ite (c, s, t, e)          -> ite c s (merge t1 t) (merge t1 e)
      module M_d =
        Map.Make
          (struct
            type t = exp * V.t
            let compare (e1, v1) (e2, v2) =
              let c = Exp.compare e1 e2 in
              if c <> 0 then c else V.compare v1 v2
          end)
      let rec opt : type k. k kind -> _ -> k u -> k u =
        fun k path v ->
          let open Info.Symbolic in
          let Refl = eq in
          let opt' c s f = opt k @@ M_d.add (c, s) f path in
          let opt k = opt k path in
          match v.node with
          | Ite (c, s, t, e, _)
            when M_d.mem (c, s) path -> if M_d.find (c, s) path then opt k t else opt k e
          | Ite (c, s, t, e, ty)     ->(let t, e = map_pair (uncurry @@ opt' c s) ((true, t), (false, e)) in
                                        if equal t e then t else Symbolic.ite k c s t e ty)
          | Top | Bot
          | Cst _ | Adr _ | Var _
          | Let _
          | Ndv (_, _, None)         -> v
          | Mem _                    -> v
          | Ndm _                    -> v
          | Ndv (s, l, Some a)       -> ndv k s ~size:(opt V a) l
          | Una (u, s, ty)           -> una k u (opt V s) ty
          | Bin (b, s1, s2, ty)      -> bin k b (opt V s1) (opt V s2) ty
          | Sel (m, a, ty)           -> sel k (opt M m) (opt V a) ty
          | Upd (m, a, v, ty)        -> upd (opt M m) (opt V a) (opt V v) ty
      let rec cut path c (s : V.t) f =
        let Refl = eq in
        let cut c' s' f' = cut (M_d.add (c', s') f' path) c s f in
        let so () = opt V path s in
        function
        | Top when f                   -> ite c (so ()) Top Bot
        | Top                          -> ite c (so ()) Bot Top
        | Bot                          -> Bot
        | Ite (c', s', t, e)
          when Exp.equal c c'
            && V.equal s s'            -> if f then t else e
        | Ite (c', s', _, _) as t
          when Exp.compare c c' < 0
            || Exp.compare c c' = 0 &&
               V.compare s s' < 0      -> if f then ite c (so ()) t Bot else ite c (so ()) Bot t
        | Ite (c', s', t, e)           -> ite c' s' (cut c' s' true t) (cut c' s' false e)
      let cut = cut M_d.empty
      let rec inst k path v ty =
        let Refl = eq in
        let inst c f = inst k (M_d.add c f path) v ty in
        function
        | Top              -> opt k path v
        | Bot              -> Symbolic.bot k
        | Ite (c, s, t, e) -> Symbolic.ite k c s (inst (c, s) true t) (inst (c, s) false e) ty
      let inst_v : V.t -> _ -> _ -> V.t = let Refl = eq in inst V M_d.empty
      let inst_m : M.t -> _ -> _ -> M.t  = let Refl = eq in inst M M_d.empty
      let rec pp fmt =
        let pr f = fprintf fmt f in
        function
        | Top              -> pr "T"
        | Bot              -> pr "_|_"
        | Ite (c, s, t, e) -> pr "@[(%a (%d)) ?@ %a :@ %a@]" Symbolic.V.pp s c.eid pp t pp e
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

    let get =
      function
      | Some x -> x
      | None   -> Console.fatal "Symbolic.get: unexpected composite value"

    let find_global_var v s = I.G.Var.M.find   v s.post.global_vars
    let find_global_mem m s = I.G.Mem.M.find   m s.post.global_mems
    let find_poly_var   v s = Poly.Var.M.find  v s.post.poly_vars
    let find_poly_mem   m s = Poly.Mem.M.find  m s.post.poly_mems
    let find_local_var  v s = Local.Var.M.find v s.local_vars
    let find_local_mem  m s = Local.Mem.M.find m s.local_mems
    let set_global_var vr vl s = { s with post = { s.post with global_vars = I.G.Var.M.add vr vl s.post.global_vars } }
    let set_global_mem m v s = { s with post = { s.post with global_mems = I.G.Mem.M.add m v s.post.global_mems } }
    let set_poly_var vr vl s = { s with post = { s.post with poly_vars = Poly.Var.M.add vr vl s.post.poly_vars } }
    let set_poly_mem m v s = { s with post = { s.post with poly_mems = Poly.Mem.M.add m v s.post.poly_mems } }
    let set_local_var vr vl s = { s with local_vars = Local.Var.M.add vr vl s.local_vars }
    let set_local_mem m v s = { s with local_mems = Local.Mem.M.add m v s.local_mems }

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
                             offset s ty (V.bin `Plus acc (get @@ eval_expr s e) @@ TPtr (ty, [])) off)
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
      fun s (lh, off) ->
        match lh with
        | Var v when v.vglob -> offset s v.vtype (V.adr (Global_var.of_varinfo v)) off
        | Var v              -> offset s v.vtype (local v) off
        | Mem e              -> offset s (typeOfLhost lh) (get @@ eval_expr s e) off
    and eval_lval s lv : V.t option =
      let Refl = S.eq in
      let Refl = eq in
      let deref m = V.sel m (eval_addr s lv) @@ typeOfLval lv in
      try
        opt_map
          (function
          | `Global_var v -> find_global_var v s
          | `Poly_var   v -> find_poly_var v s
          | `Local_var  v -> find_local_var v s
          | `Global_mem m -> deref @@ find_global_mem m s
          | `Poly_mem   m -> deref @@ find_poly_mem m s
          | `Local_mem  m -> deref @@ find_local_mem m s)
          (w_lval lv)
      with
      | Not_found ->
        some @@ V.ndv dummyStmt lv
    and eval_expr =
      let size s = some @@ V.cst @@ CInt64 (Integer.of_int s, theMachine.kindOfSizeOf, None) in
      fun s e ->
        let eval = get % eval_expr s in
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

    type state = Path_dd.t * S.t

    let assume c flag (pdd, s : state) : state =
      let Refl = S.eq in
      Path_dd.cut c (get @@ eval_expr s c) flag pdd, s

    let rec set =
      let integer =
        let module H = Datatype.Int.Hashtbl in
        let h = H.create 10 in
        fun i -> H.memo h i (integer ~loc)
      in
      fun lv off (v : _ -> V.t) pdd (s : S.t) : S.t ->
        let Refl = S.eq in
        let Refl = eq in
        let ty = typeOfLval lv in
        let set_v set vr = set vr (Path_dd.inst_v (v off) ty pdd) s in
        let set_m find set m =
          let vm = try find m s with Not_found -> M.ndm dummyStmt lv in
          set m (Path_dd.inst_m (M.upd vm (eval_addr s lv) (v off) ty) ty pdd) s
        in
        match[@warning "-4"] unrollType ty with
        | TComp (ci, _, _)
          when ci.cstruct          -> List.fold_left
                                        (fun s fi ->
                                           let fi = Field (fi, NoOffset) in
                                           set (addOffsetLval fi lv) (addOffset fi off) v pdd s)
                                        s
                                        ci.cfields
        | TComp (ci, _, _)         ->(let fi = Field (List.hd ci.cfields, NoOffset) in
                                      set (addOffsetLval fi lv) (addOffset fi off) v pdd s)
        | TArray (_, Some e, _, _) ->(let l = may_map ~dft:0 Integer.to_int @@ constFoldToInt e in
                                      Array.init l id |>
                                      Array.fold_left
                                        (fun s i ->
                                           let i = Index (integer i, NoOffset) in
                                           set (addOffsetLval i lv) (addOffset i off) v pdd s)
                                        s)
        | TArray _                 -> s
        | ty                       ->
          match w_lval lv with
          | Some (`Global_var v)   -> set_v set_global_var v
          | Some (`Poly_var v)     -> set_v set_poly_var v
          | Some (`Local_var v)    -> set_v set_local_var v
          | Some (`Global_mem m)   -> set_m find_global_mem set_global_mem m
          | Some (`Poly_mem m)     -> set_m find_poly_mem set_poly_mem m
          | Some (`Local_mem m)    -> set_m find_local_mem set_local_mem m
          | None                   -> Console.fatal "Symbolic.set: unexpected type: %a : %a" pp_lval lv pp_typ ty

    let assign lv e (pdd, s : state) =
      let Refl = S.eq in
      pdd,
      set
        lv
        NoOffset
        (function
        | NoOffset       -> get @@ eval_expr s e
        | Field _
        | Index _ as off ->
          match[@warning "-4"] e.enode with
          | Lval lv      -> get @@ eval_lval s (addOffsetLval off lv)
          | _            -> Console.fatal "Symbolic.assign: unrecognized assignment: %a = %a" pp_lval lv pp_exp e)
        pdd
        s

    let return eo s =
      opt_fold
        (function
          [@warning "-4"]
        | { enode = Lval lv; _ } as e -> assign lv e
        | _                           -> Console.fatal "Symbolic.return: not an lvalue")
        eo
        s

    let kf = Globals.Functions.get F.f.svar
    let retvar = Kf.retvar kf
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

    let dummy =
      let module H = FCHashtbl.Make (Datatype.Pair (Varinfo) (Typ)) in
      let h = H.create 10 in
      fun v newt ->
        H.memo
          h
          (v, newt)
          (fun _ ->
             mkMem
               ~addr:(
                 mkCast
                   ~force:false
                   ~overflow:Check
                   ~e:(mkAddrOf ~loc @@ var v)
                   ~newt)
               ~off:NoOffset)

    let lval =
      let mem m =
        match mk_mem m with
        | Some lv -> lv
        | None    -> dummy F.f.svar @@ TPtr ((fst m).R.typ, [])
      in
      let h = W.H.create 10 in
      fun w ->
        W.H.memo
          h
          (w :> W.t)
          (fun _ ->
             match (w :> W.readable) with
             | `Global_var v -> var (v :> varinfo)
             | `Poly_var   v -> var (v :> varinfo)
             | `Local_var  v -> var (v :> varinfo)
             | `Global_mem m -> mem (m :> I.mem)
             | `Poly_mem   m -> mem (m :> I.mem)
             | `Local_mem  m -> mem (m :> I.mem))

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

    let join =
      let open Info.Symbolic in
      let Refl = eq in
      let rec split v =
        match v.node with
        | Bin (`Or, v1, v2, _) -> V.S.union (split v1) (split v2)
        | Top | Bot
        | Cst _ | Adr _
        | Var _ | Ndv _
        | Una _ | Bin _
        | Sel _
        | Ite _ | Let _        -> V.S.singleton v
      in
      fun (v1 : V.t) (v2 : V.t) ->
        match v1.node, v2.node with
        | Cst (CInt64 (c, IInt, _)), _
          when Integer.is_one c                                -> V.one
        | _,                         Cst (CInt64 (c, IInt, _))
          when Integer.is_one c                                -> V.one
        | Cst (CInt64 (c, IInt, _)), _
          when Integer.is_zero c                               -> v2
        | _,                         Cst (CInt64 (c, IInt, _))
          when Integer.is_zero c                               -> v1
        | Ite _,                     _
        | _,                         Ite _                     -> Console.fatal "Symbolic.join: ite is being lost"
        | _,                         _
          when V.equal v1 v2                                   -> v1
        | (Top
          | Bot
          | Cst _
          | Adr _
          | Var _
          | Ndv _
          | Una _
          | Bin _
          | Sel _
          | Let _),                  _                         ->(let v1, v2 =
                                                                    map_pair (V.S.elements % split) (v1, v2)
                                                                  in
                                                                  let vs = v1 @ v2 in
                                                                  List.(fold_left
                                                                          (fun s1 s2 -> V.bin `Or s1 s2 intType)
                                                                          (hd vs)
                                                                          (tl vs)))

    let call ~same_scc stmt ?lv kf es (pdd, s : state) : state =
      let I.E.Some { local = (module L'); eff = eff' } = I.get info R.flag @@ Kernel_function.get_definition kf in
      let h_map = R.map stmt kf in
      let h_rev =
        let h = R.H.create 512 in
        R.H_map.iter
          (fun u' u -> let r = U.repr u in R.H.replace h r @@ R.S.add (U.repr u') @@ R.H.find_def h r R.S.empty)
          h_map;
        h
      in
      let clashes =
        let h_clash =
          let h_glob =
            let h = R.H.create 16 in
            let handle =
              function
              | `Global_mem m -> R.H.replace h (fst (m :> I.mem)) ()
              | #L'.W.t       -> ()
            in
            L'.A.iter (const' handle) (I.E.assigns eff');
            L'.R.iter handle (I.E.depends eff');
            h
          in
          let h = R.H.create 16 in
          R.H.iter
            (fun r s ->
               let s = if R.H.mem h_glob r then R.S.add r s else s in
               if R.S.cardinal s > 1 then R.S.iter (fun r' -> R.H.replace h r' s) s)
            h_rev;
          h
        in
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
           | `Poly_mem m   -> writes
                                (m :> I.mem)
                                (fun ?fi u ->
                                   match (U.repr u).R.kind with
                                   | `Poly f
                                     when String.equal f L'.F.f.svar.vname -> `Poly_mem (L'.F.Poly.Mem.mk ?fi u)
                                   | `Global                               -> `Global_mem (I.G.Mem.mk ?fi u)
                                   | `Poly _
                                   | `Local _
                                   | `Dummy                                -> Console.fatal "Symbolic.call: \
                                                                                             unexpected region kind"))
          (I.E.assigns eff')
          L'.W.S.empty |> fun clashes ->
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
      let es, formals =
        let open List in
        Kernel_function.get_formals kf |>
        combine es |>
        filter ((=) `None % R.of_var % snd) |>
        split
      in
      let es = List.map (eval_expr s) es in
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
        if not @@ L'.A.mem (w' :> L'.W.t) (I.E.assigns eff')
        then
          s
        else
          let clashes = same_scc || L'.W.S.mem (w' :> L'.W.t) clashes in
          match w' with
          | `Global_var g as w ->(check w clashes;
                                  let v =
                                    if clashes
                                    then V.ndv stmt (lval w)
                                    else V'.prj stmt S.Symbolic.readable env v
                                  in
                                  set_global_var g (Path_dd.inst_v v (type_of w) pdd) s)
          | `Result            ->(check `Result clashes;
                                  let lv = the lv in
                                  let v =
                                    if clashes
                                    then V.ndv stmt lv
                                    else V'.prj stmt S.Symbolic.readable env v
                                  in
                                  set lv NoOffset (const v) pdd s)
      in
      let handle_m w' m s =
        if not @@ L'.A.mem (w' :> L'.W.t) (I.E.assigns eff')
        then
          s
        else
          let clashes = same_scc || L'.W.S.mem (w' :> L'.W.t) clashes in
          let set set mem w =
            check (w :> W.t) clashes;
            let m =
              if clashes
              then M.ndm stmt (lval w)
              else M'.prj stmt S.Symbolic.readable env m
            in
            set mem (Path_dd.inst_m m (type_of w) pdd) s
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
             then V.one
             else
               let open Info.Symbolic in
               match s'.pre.node with
               | Bot                    -> V.bot
               | Cst (CInt64 (c, _, _))
                 when Integer.is_zero c -> V.zero
               | Top
               | Cst _ | Adr _
               | Var _ | Ndv _
               | Una _ | Bin _ | Sel _
               | Ite _ | Let _          -> V'.prj stmt S.Symbolic.readable env s'.pre)
            intType
            pdd
        in
        S.Symbolic.V.merge ~join stmt (dummy (Kernel_function.get_vi kf) intType) s.pre v
      in
      pdd,
      { s with pre } |>
      I.G.Var.M.fold (fun v -> handle_v @@ `Global_var v) s'.post.global_vars |>
      I.G.Mem.M.fold (fun m -> handle_m @@ `Global_mem m) s'.post.global_mems |>
      L'.F.Poly.Mem.M.fold (fun m -> handle_m @@ `Poly_mem m) s'.post.poly_mems |>
      if has_some lv && not @@ isStructOrUnionType @@ Kernel_function.get_return_type kf
      then
        handle_v
          `Result
          (if not same_scc
           then L'.F.Local.Var.(M.find (of_varinfo @@ the retvar') s'.local_vars)
           else V'.ndv stmt @@ Cil.var @@ the retvar)
      else
        id

    let rec fold_init f lv =
      function
      | SingleInit e             -> f lv e
      | CompoundInit (ct, initl) ->(let doinit off = const' @@ fold_init f (addOffsetLval off lv) in
                                    fun acc ->
                                      foldLeftCompound
                                        ~implicit:true
                                        ~doinit
                                        ~ct
                                        ~initl
                                        ~acc)

    let init = fold_init assign
    let reach stmt f (pdd, s : state) : state =
      let Refl = S.eq in
      pdd, { s with pre = V.merge ~join stmt (dummy f intType) s.pre @@ Path_dd.inst_v V.one intType pdd }
    let stub stmt lv (pdd, s) = pdd, set lv NoOffset (V.ndv stmt % (swap addOffsetLval) lv) pdd s
    let alloc stmt lv sz (pdd, s : state) =
      let Refl = S.eq in
      pdd, set lv NoOffset (const @@ V.ndv stmt ~size:(get @@ eval_expr s sz) lv) pdd s

    let start = List.hd F.f.sbody.bstmts

    let initial : state =
      let Refl = S.eq in
      let Refl = eq in
      Path_dd.top,
      S.empty |>
      L.R.fold
        (function
        | `Global_var g as w -> set_global_var g @@ V.var w
        | `Poly_var p as w   -> set_poly_var p @@ V.var w
        | `Local_var l as w  -> set_local_var l @@ V.ndv start @@ lval w
        | `Global_mem m as w -> set_global_mem m @@ M.mem w
        | `Poly_mem m as w   -> set_poly_mem m @@ M.mem w
        | `Local_mem m as w  -> set_local_mem m @@ M.ndm start @@ lval w)
        (I.E.depends E.eff)

    let before, after, set_before, set_after, reset_states =
      let b = H_stmt.create 64 in
      let module H = FCHashtbl.Make (Datatype.Pair (Stmt) (Datatype.Bool)) in
      let a = H.create 64 in
      let empty = Path_dd.bot, S.empty in
      (fun s -> H_stmt.find_def b s empty),
      (fun ?(cond=true) s -> H.find_def a (s, cond) empty),
      H_stmt.replace b,
      (fun ?(cond=true) s -> H.replace a (s, cond)),
      fun () -> H_stmt.clear b; H_stmt.replace b start initial; H.clear a
    let add_stop, stops, reset_stops =
      let stops = ref [] in
      (fun s -> stops := s :: !stops),
      (fun () -> !stops),
      fun () -> stops := []

    let merge stmt (pdd1, s1) (pdd2, s2) = Path_dd.merge pdd1 pdd2, merge ~join stmt lval s1 s2

    let expand =
      let h = H_stmt.create 64 in
      let set = H_stmt.replace h in
      List.iter
        (fun st ->
           match[@warning "-4"] st.skind with
           | Switch (e, _, ss, _) ->(let next =
                                       List.fold_right
                                         (fun s next ->
                                            let case =
                                              function
                                              | Case (e', _) -> mkBinOp ~loc Eq e e'
                                              | Default _    -> Cil.one ~loc
                                              | Label _      -> assert false
                                            in
                                            let stmt = mkStmt ~valid_sid:true in
                                            let goto = stmt @@ Goto (ref s, loc) in
                                            let skip = stmt @@ Instr (Skip loc) in
                                            let fork =
                                              stmt @@
                                              If (
                                                List.fold_right
                                                  (mkBinOp ~loc BOr % case)
                                                  (List.tl s.labels)
                                                  (case @@ List.hd s.labels),
                                                mkBlock [goto],
                                                mkBlock [skip],
                                                loc)
                                            in
                                            goto.preds <- [fork];
                                            goto.succs <- [s];
                                            set goto goto;
                                            s.preds <-
                                              List.map (fun s -> if Stmt.equal s st then goto else s) s.preds;
                                            skip.preds <- [fork];
                                            skip.succs <- [next];
                                            set skip skip;
                                            next.preds <- [skip];
                                            fork.succs <- [goto; skip];
                                            set fork fork;
                                            fork)
                                         ss
                                         List.(find (fun s -> not @@ exists (Stmt.equal s) ss) st.succs)
                                     in
                                     next.preds <- st.preds;
                                     set st next)
           | _                    -> set st st)
        F.f.sallstmts;
      H_stmt.find h

    let succs ?cond s =
      match[@warning "-4"] s.skind with
      | If (_, t, e, _) ->(let t, e = map_pair (fun b -> opt_of_list @@ List.take 1 b.bstmts) (t, e) in
                           [List.find
                              (fun s ->
                                 may_map ~dft:false (Stmt.equal s) (if the cond then t else e) ||
                                 may_map ~dft:false (not % Stmt.equal s) (if the cond then e else t))
                              s.succs])
      | _               -> s.succs

    let handle ~same_scc ?(cond=true) stmt =
      let finish ?(stop=false) (pdd, s as st : state) =
        let Refl = S.eq in
        let covers =
          let pdd', s' = after stmt in
          let pdd', pdd = map_pair V.(weaken stmt (dummy F.f.svar intType) % Path_dd.inst_v top intType) (pdd', pdd) in
          V.covers pdd' pdd && covers s' s
        in
        let stop = stop || covers in
        if stop
        then add_stop s.pre
        else begin
          List.iter (fun s -> set_before s @@ merge s (before s) st) (succs ~cond stmt);
          set_after ~cond stmt st
        end;
        stop
      in
      let dcall ?lv kf' args =
        if Kernel_function.is_definition kf'
        then call ~same_scc:(same_scc kf kf') stmt ?lv kf' args
        else may_map ~dft:id (stub stmt) lv
      in
      before stmt |>
      match[@warning "-4"] stmt.skind with
      | Instr (Set (lv, e, _))                                       -> finish % assign lv e
      | Instr (Local_init (vi, AssignInit i, _))                     -> finish % init (var vi) i
      | Instr (Call
                 (_,
                  { enode = Lval (Var f, NoOffset); _ },
                  _, _))
        when Options.Target_functions.mem f.vname                    -> finish
                                                                          ~stop:(hasAttribute
                                                                                   "noreturn" f.vattr) % reach stmt f
      | Instr (Call
                 (Some lv,
                  { enode = Lval (Var f, NoOffset); _ },
                  (e :: _), _))
        when Options.Alloc_functions.mem f.vname                     -> finish % alloc stmt lv e
      | Instr (Local_init
                 (vi, ConsInit (f, e :: _, Plain_func), _))
        when Options.Alloc_functions.mem f.vname                     -> finish % alloc stmt (var vi) e

      | Instr (Call (_,
                     { enode = Lval (Var f, NoOffset); _ }, [e], _))
        when Options.Assume_functions.mem f.vname                    -> finish % assume e true
      | Instr (Call (_,
                     { enode = Lval (Var f, NoOffset); _ }, [], _))
        when Options.Path_assume_functions.mem f.vname               -> finish ~stop:true
      | Instr (Call (lv,
                     { enode = Lval (Var f, NoOffset); _ },
                     args, _))                                       -> finish % dcall
                                                                                   ?lv (Globals.Functions.get f) args
      | Instr (Local_init (vi, ConsInit (f, args, Plain_func), _))   -> finish % dcall
                                                                                   ~lv:(var vi)
                                                                                   (Globals.Functions.get f)
                                                                                   args
      | Instr (Call (Some lv, _, _, _))                              -> finish % stub stmt lv
      | Instr (Call (None, _, _, _))                                 -> finish % id
      | Instr (Local_init (_, ConsInit (_, _, Constructor), _))      -> Console.fatal
                                                                          "Symbolic.handle: C++ constructors \
                                                                           are unsupported"
      | Return (eo, _)                                               -> finish % return eo
      | Instr (Asm _ | Skip _ | Code_annot _)
      | Goto _ | AsmGoto _ | Break _ | Continue _                    -> finish % id
      | If (e, _, _, _)                                              -> finish % assume e cond
      | Switch _                                                     -> assert false
      | Loop _ | Block _                                             -> finish % id
      | UnspecifiedSequence _                                        -> finish % id
      | Throw _ | TryCatch _ | TryFinally _ | TryExcept _            -> Console.fatal
                                                                          "Unsupported features: exceptions \
                                                                           and their handling"

    let fix =
      let push, clear, empty, pop =
        let q = Queue.create () in
        (fun s ->
           let s = expand s in
           let push ?c s =
             if
               try Queue.iter (fun (s', c') -> if Stmt.equal s s' && c = c' then raise Exit) q; true
               with Exit                                                                     -> false
             then
               Queue.push (s, c) q
           in
           match[@warning "-4"] s.skind with
           | If _ ->(push ~c:true s;
                     push ~c:false s)
           | _    -> push s),
        (fun () -> Queue.clear q),
        (fun () -> Queue.is_empty q),
        (fun () -> Queue.pop q)
      in
      fun same_scc ->
        clear ();
        push start;
        while not @@ empty () do
          let s, cond = pop () in
          if not (handle ~same_scc ?cond s) then List.iter push (succs ?cond s)
        done;
        let rs = Kernel_function.find_return @@ Globals.Functions.get F.f.svar in
        let r = snd @@ after rs in
        let Refl = S.eq in
        ({ r with pre = List.fold_left (V.merge ~join rs @@ dummy F.f.svar intType) r.pre @@ stops () } : S.t)

    let visitor same_scc =
      object
        inherit frama_c_inplace
        method start = reset_states (); reset_stops ()
        method! vfunc _ = SkipChildren
        method finish =
          let s = fix same_scc in
          if not @@ covers (I.E.summary E.eff) s then begin
            I.E.set_summary s E.eff;
            Flag.report I.flag
          end
      end
  end

  let fixpoints same_scc =
    let h = H_fundec.create 256 in
    Globals.Functions.iter_on_fundecs
      (fun d ->
         let I.E.Some { local = (module L); eff } = I.get info R.flag d in
         let module Import = Import (L) in
         let module L = Make_local (L) (struct let eff = eff end) (Import) in
         H_fundec.replace h d @@ L.visitor same_scc);
    h

  module Fixpoint = Fixpoint.Make (I)

  let compute sccs =
    let same_scc =
      let module M = Kf.Map in
      let scc_map, _ =
        List.(fold_left (fun (m, i) kfs -> fold_left (fun m kf -> M.add kf i m) m kfs, i + 1) (M.empty, 0) sccs)
      in
      fun kf kf' -> M.(find kf scc_map = find kf' scc_map)
    in
    Fixpoint.visit_until_convergence ~order:`topological (const @@ H_fundec.find @@ fixpoints same_scc) info sccs
end

let prepare () =
  visitFramacFile
    (object (self)
      inherit frama_c_inplace

      method! vstmt s =
        match[@warning "-4"] s.skind with
        | Return (Some { enode = Lval (Var v, NoOffset); _ }, _)
          when not v.vformal && not v.vglob                      -> SkipChildren
        | Return (Some e, loc)                                   ->(let f = the self#current_func in
                                                                    let ass, s' =
                                                                      let r =
                                                                        makeTempVar f @@ typeOf e
                                                                      in
                                                                      mkStmt
                                                                        ~valid_sid:true
                                                                        (Instr (Set (var r, e, loc))),
                                                                      mkStmt
                                                                        ~valid_sid:true
                                                                        (Return (some @@ evar r, loc))
                                                                    in
                                                                    f.sallstmts <-
                                                                      f.sallstmts @ [ass; s'];
                                                                    s.skind <- Block
                                                                                 (mkBlock [ass; s']);
                                                                    s.succs <- [ass];
                                                                    ass.succs <- [s'];
                                                                    ass.preds <- [s];
                                                                    s'.preds <- [ass];                 SkipChildren)
        | _                                                      ->                                    SkipChildren
    end)
    (Ast.get ())
