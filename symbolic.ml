
open Cil_types
open Cil_datatype
open Cil

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

    (*let eval_lval lv s : [`V of Symbolic.tv | `M of Symbolic.tm ] option =
      let open Symbolic in
      let Refl = Symbolic.eq in
      match w_lval lv with
      | Some (`Global_var v) -> Some (`V (I.G.Var.M.find v s.post.global_vars))
      | Some (`Local_var v) -> Some (`V (F.Local.Var.M.find v s.local_vars))
      | Some (`Poly_var v) -> Some (`V (F.Poly.Var.M.find v s.post.poly_vars))
      | `Global_mem _
      | `Local_mem _
      | `Poly_mem _        ->(let a =
                                match lv with
                                | Var _, _ ->
                              in)


      let assume*)
  end
end
