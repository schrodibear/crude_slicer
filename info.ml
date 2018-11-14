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

open Cil
open Cil_types
open Cil_printer
open Cil_datatype

open Format
open Extlib
open Common
open Data

module type Private_index = sig
  type t = private int
  val coerce : t -> int
  include Hashed_ordered_printable with type t := t
end

module type Index = sig
  include Private_index
  val mk : int -> t
  val z : t
end

module Make_index () : Index = struct
  type t = int
  let hash x = x
  let equal : int -> _ = (=)
  let compare : int -> _ = compare
  let coerce x = x
  let mk x = x
  let z = 0
  let pp = Format.pp_print_int
end

module type Criterion = sig
  type t
  val is_ok : t -> bool
end

module type Variable = sig
  type t = private varinfo

  include Criterion with type t := t
  val of_varinfo : varinfo -> t
  include Hashed_ordered_printable with type t := t
  module H : Reporting_bithashset with type elt := t
  module M : FCMap.S with type key := t
end

module Memory_field : sig
  type t = private fieldinfo

  include Criterion with type t := t
  val of_fieldinfo : fieldinfo -> t
  include Hashed_ordered_printable with type t := t
end = struct
  type t = fieldinfo

  let is_ok fi = fi.fcomp.cstruct && isArithmeticOrPointerType fi.ftype

  let of_fieldinfo fi =
    if is_ok fi
    then fi
    else Console.fatal "Memory_field.of_fieldinfo: not ok: %s.%s : %a" (compFullName fi.fcomp) fi.fname pp_typ fi.ftype

  include (Fieldinfo : Hashed_ordered with type t := t)
  let pp = pp_field
end

module type Representant = sig
  module Kind : sig
    type t = private [> `Global | `Poly of string | `Local of string]

    include Printable with type t := t
  end

  type t

  val name : t -> string
  val typ  : t -> typ
  val kind : t -> Kind.t

  val flag : Flag.t

  include Hashed_ordered_printable with type t := t
end

module type Unifiable = sig
  module R : Representant
  type t
  val repr : t -> R.t
  val of_repr : R.t -> t
end

module type Memory = sig
  module R : Representant
  module U : Unifiable with module R := R
  type t = private R.t * Memory_field.t option
  val mk : ?fi: fieldinfo -> U.t -> t
  include Hashed_ordered_printable with type t := t
  module H : Reporting_bithashset with type elt := t
  module M : FCMap.S with type key := t
end

module type Poly_memory = sig
  include Memory
  val prj : find:(U.t -> U.t) -> mk:(?fi: fieldinfo -> U.t -> 'a) -> t -> 'a
end

module type Generic_memory = Poly_memory

module type Global = sig
  module R : Representant
  module U : Unifiable with module R := R
  module Var : Variable
  module Mem : Memory with module R := R and module U := U
end

module type Function = sig
  module R : Representant
  module U : Unifiable with module R := R
  module Poly : sig
    module Var : Variable
    module Mem : Poly_memory with module R := R and module U := U
  end
  module Local : sig
    module Var : Variable
    module Mem : Memory with module R := R and module U := U
  end
  val f : fundec
end

module type Writes = sig
  module R : Representant
  module U : Unifiable with module R := R
  module G : Global    with module R := R and module U := U
  module F : Function  with module R := R and module U := U
  type frameable_var =
    [ `Global_var of G.Var.t
    | `Poly_var   of F.Poly.Var.t ]

  type frameable_mem =
    [ `Global_mem of G.Mem.t
    | `Poly_mem   of F.Poly.Mem.t ]

  type frameable =
    [ frameable_var | frameable_mem ]

  type readable =
    [ frameable
    | `Local_var of F.Local.Var.t
    | `Local_mem of F.Local.Mem.t ]

  type t = [ readable | `Result ]

  include With_containers with type t := t
  val equal' : [< t] -> [< t] -> bool
  val compare' : [< t] -> [< t] -> int
  val hash' : [< t] -> int
  val pp' : formatter -> [< t] -> unit
end

type ('w, _) reads = ..

module type Reads = sig
  module R : Representant
  module U : Unifiable with module R := R
  module G : Global    with module R := R and module U := U
  module F : Function  with module R := R and module U := U
  module W : Writes    with module R := R and module U := U and module G := G and module F := F

  type _ kind =
    | Global_var : G.Var.t       kind
    | Poly_var   : F.Poly.Var.t  kind
    | Local_var  : F.Local.Var.t kind
    | Global_mem : G.Mem.t       kind
    | Poly_mem   : F.Poly.Mem.t  kind
    | Local_mem  : F.Local.Mem.t kind

  type some = Some : 'a kind * 'a -> some

  type t

  type ('w, _) reads += W : (W.t, t) reads

  val of_write : [< W.readable ] -> some

  val create : Flag.t -> t
  val clear : t -> unit
  val import : from:t -> t -> unit
  val add_global_var : G.Var.t       -> t -> unit
  val add_poly_var   : F.Poly.Var.t  -> t -> unit
  val add_local_var  : F.Local.Var.t -> t -> unit
  val add_global_mem : G.Mem.t       -> t -> unit
  val add_poly_mem   : F.Poly.Mem.t  -> t -> unit
  val add_local_mem  : F.Local.Mem.t -> t -> unit
  val add : 'a kind -> 'a -> t -> unit
  val add_some : some -> t -> unit
  val sub : t -> from:t -> unit
  val mem : 'a kind -> 'a -> t -> bool
  val mem_some : some -> t -> bool
  val intersects : t -> t -> bool
  val flag : t -> Flag.t
  val copy : Flag.t -> t -> t

  val iter_global_vars : (G.Var.t       -> unit) -> t -> unit
  val iter_poly_vars   : (F.Poly.Var.t  -> unit) -> t -> unit
  val iter_local_vars  : (F.Local.Var.t -> unit) -> t -> unit
  val iter_global_mems : (G.Mem.t       -> unit) -> t -> unit
  val iter_poly_mems   : (F.Poly.Mem.t  -> unit) -> t -> unit
  val iter_local_mems  : (F.Local.Mem.t -> unit) -> t -> unit

  val fold_global_vars : (G.Var.t       -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_poly_vars   : (F.Poly.Var.t  -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_local_vars  : (F.Local.Var.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_global_mems : (G.Mem.t       -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_poly_mems   : (F.Poly.Mem.t  -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_local_mems  : (F.Local.Mem.t -> 'a -> 'a) -> t -> 'a -> 'a

  val iter : ([> W.readable] -> unit) -> t -> unit
  val fold : ([> W.readable] -> 'a -> 'a) -> t -> 'a -> 'a

  val is_empty : t -> bool
  val is_singleton : t -> bool
  val length : t -> int

  val pp : formatter -> t -> unit
end

module Variable (C : Criterion with type t := varinfo) () : Variable = struct
  type t = varinfo

  include C

  let of_varinfo vi =
    if C.is_ok vi then vi
    else               invalid_arg "Variable.of_varinfo"

  include (Varinfo : Hashed_ordered with type t := t)
  let pp = pp_varinfo

  module H = Reporting_bithashset (struct type nonrec t = t let equal = equal let hash = hash let pp = pp end) ()
  module M = Varinfo.Map
end

module type Op = sig
  type unary =
    [ `Cast of typ
    | `Minus
    | `Bw_neg
    | `Neg ]
  type binary =
    [ `Plus
    | `Minus
    | `Mult
    | `Div
    | `Mod
    | `Shift_left
    | `Shift_right
    | `Lt
    | `Gt
    | `Le
    | `Ge
    | `Eq
    | `Ne
    | `Bw_and
    | `Bw_xor
    | `Bw_or
    | `And
    | `Or ]
end

type (_, _) readable = ..

module type Readables = sig
  type v
  type m
  type (_, _) readable += W : (v, m) readable
  val f : fundec
end

type ('v, 'm) readables = (module Readables with type v = 'v and type m = 'm)

let eq_readables (type v1 m1 v2 m2) ((module R1) : (v1, m1) readables) (((module R2) : (v2, m2) readables))
  : (v1 * m1, v2 * m2) eq =
  match R1.W with
  | R2.W -> Refl
  | _    -> Console.fatal "Info.eq_readables: different witnesses"

type 'x binding = .. constraint 'x = < crv : 'crv; crm : 'crm; cev : 'cev; cem : 'cem; cee : 'cee >

module Global_var = Variable (struct let is_ok vi = vi.vglob end) ()

module Symbolic : sig
  module Op : Op
  module Id : Private_index
  type v = [`V]
  type m = [`M]
  type 'a any = [< v | m ] as 'a
  type ('v, 'm, 'k) node =
    | Top
    | Bot
    | Cst of constant
    | Adr of Global_var.t
    | Var of 'v
    | Mem : 'm -> (_, 'm, m) node
    | Ndv of stmt * lval * ('v, 'm, v) t option
    | Ndm : stmt * lval -> (_, _, m) node
    | Una of Op.unary * ('v, 'm, v) t * typ
    | Bin of Op.binary * ('v, 'm, v) t * ('v, 'm, v) t * typ
    | Sel of ('v, 'm, m) t * ('v, 'm, v) t * typ
    | Upd : ('v, 'm, m) t * ('v, 'm, v) t * ('v, 'm, v) t * typ -> ('v, 'm, m) node
    | Ite : exp * ('v, 'm, v) t * ('v, 'm, 'k) t * ('v, 'm, 'k) t * typ -> ('v, 'm, 'k) node
    | Let : stmt * < crv : 'crv; crm : 'crm; cev : 'cev; cem : 'cem; cee : 'cee > binding * 'cee * ('cev, 'cem, 'k) t
      -> ('crv, 'crm, 'k) node (* Should be handled from the INSIDE! *)
  and ('v, 'm, 'k) t = private
    {
      node : ('v, 'm, 'k) node;
      id   : Id.t
    }
  val mk : ('v, 'm, 'k) node -> ('v, 'm, 'k) t
  val coerce : ('v, 'm, _) t -> ('v, 'm, m) t
  module Node : sig
    type ('crv, 'crm) he =
      { f : 'cev 'cem 'cee. < crv : 'crv; crm : 'crm; cev : 'cev; cem : 'cem; cee : 'cee > binding -> 'cee -> int }
    [@@unboxed]
    val hash : ('v -> int) -> ('m -> int) -> ('v, 'm) he -> ('v, 'm, 'k) node -> int
    type ('crv, 'crm) ee =
      { f : 'cev1 'cem1 'cee1 'cev2 'cem2 'cee2.
              < crv : 'crv; crm : 'crm; cev : 'cev1; cem : 'cem1; cee : 'cee1 > binding
          -> 'cee1
          -> < crv : 'crv; crm : 'crm; cev : 'cev2; cem : 'cem2; cee : 'cee2 > binding
          -> 'cee2
          -> bool }
    [@@unboxed]
    val equal : ('v -> 'v -> bool) -> ('m -> 'm -> bool) -> ('v, 'm) ee
      -> ('v, 'm, 'k1) node -> ('v, 'm, 'k2) node -> bool
  end
  val compare : _ t -> _ t -> int
  val equal : _ t -> _ t -> bool
  val hash : _ t -> int
  type ('crv, 'crm) pe =
    { f : 'cev 'cem 'cee.
            formatter -> < crv : 'crv; crm : 'crm; cev : 'cev; cem : 'cem; cee : 'cee > binding -> 'cee -> unit }
  [@@unboxed]
  val pp : (formatter -> 'v -> unit) -> (formatter -> 'm -> unit) -> ('v ,'m) pe -> formatter -> ('v, 'm, 'k) t -> unit
end = struct
  module Id = Make_index ()
  module rec Op : Op = Op
  type v = [`V]
  type m = [`M]
  type 'a any = [< v | m ] as 'a
  type ('v, 'm, 'k) node =
    | Top
    | Bot
    | Cst of constant
    | Adr of Global_var.t
    | Var of 'v
    | Mem : 'm -> (_, 'm, m) node
    | Ndv of stmt * lval * ('v, 'm, v) t option
    | Ndm : stmt * lval -> (_, _, m) node
    | Una of Op.unary * ('v, 'm, v) t * typ
    | Bin of Op.binary * ('v, 'm, v) t * ('v, 'm, v) t * typ
    | Sel of ('v, 'm, m) t * ('v, 'm, v) t * typ
    | Upd : ('v, 'm, m) t * ('v, 'm, v) t * ('v, 'm, v) t * typ -> ('v, 'm, m) node
    | Ite : exp * ('v, 'm, v) t * ('v, 'm, 'k) t * ('v, 'm, 'k) t * typ -> ('v, 'm, 'k) node
    | Let : stmt * < crv : 'crv; crm : 'crm; cev : 'cev; cem : 'cem; cee : 'cee > binding * 'cee * ('cev, 'cem, 'k) t
      -> ('crv, 'crm, 'k) node (* Should be handled from the INSIDE! *)
  and ('v, 'm, 'k) t =
    {
      node : ('v, 'm, 'k) node;
      id   : Id.t
    }
  module Node = struct
    type ('crv, 'crm) he =
      { f : 'cev 'cem 'cee. < crv : 'crv; crm : 'crm; cev : 'cev; cem : 'cem; cee : 'cee > binding -> 'cee -> int }
    [@@unboxed]
    let hash =
      let hi v = Id.hash v.id in
      let hu =
        function
        | `Cast ty -> 5 * Typ.hash ty
        | `Minus   -> 1
        | `Bw_neg  -> 2
        | `Neg     -> 3
      in
      fun (type k) hv hm he : ((_, _, k) node -> _) ->
        function
        | Top                  -> 0
        | Bot                  -> 1
        | Cst c                -> 17 * Constant.hash c + 2
        | Adr g                -> 17 * Global_var.hash g + 3
        | Var v                -> 17 * hv v + 4
        | Mem m                -> 17 * hm m + 5
        | Ndv (s, l, a)        -> 17 * (1351 * Stmt.hash s + 257 * Lval.hash l + opt_hash hi a) + 6
        | Ndm (s, l)           -> 17 * (257 * Stmt.hash s + Lval.hash l) + 7
        | Una (u, a, t)        -> 17 * (1351 * hu u + 257 * hi a + Typ.hash t) + 8
        | Bin (b, v1, v2, t)   -> 17 * (105871 * Hashtbl.hash b + 1351 * hi v1 + 257 * hi v2 + Typ.hash t) + 9
        | Sel (m, a, t)        -> 17 * (1351 * hi m + 257 * hi a + Typ.hash t) + 10
        | Upd (m, a, v, t)     -> 17 * (105871 * hi m + 1351 * hi a + 257 * hi v + Typ.hash t) + 11
        | Ite (c, i, t, e, ty) -> 17 * (105871 * Exp.hash c + hi i + 1351 * hi t + 257 * hi e + Typ.hash ty) + 12
        | Let (s, b, e, v)     -> 17 * (1351 * Stmt.hash s + 257 * he.f b e + hi v) + 13
    type ('crv, 'crm) ee =
      { f : 'cev1 'cem1 'cee1 'cev2 'cem2 'cee2.
              < crv : 'crv; crm : 'crm; cev : 'cev1; cem : 'cem1; cee : 'cee1 > binding
          -> 'cee1
          -> < crv : 'crv; crm : 'crm; cev : 'cev2; cem : 'cem2; cee : 'cee2 > binding
          -> 'cee2
          -> bool }
    [@@unboxed]
    let equal =
      let ei v1 v2 = Id.equal v1.id v2.id in
      fun (type k1 k2) ev em (ee : (_, _) ee) (n1 : (_, _ , k1) node) (n2 : (_, _, k2) node) ->
        match n1, n2 with
        | Top,                       Top
        | Bot,                       Bot                       -> true
        | Cst c1,                    Cst c2                    -> Constant.equal c1 c2
        | Adr g1,                    Adr g2                    -> Global_var.equal g1 g2
        | Var v1,                    Var v2                    -> ev v1 v2
        | Mem m1,                    Mem m2                    -> em m1 m2
        | Ndv (s1, l1, a1),          Ndv (s2, l2, a2)          -> Stmt.equal s1 s2 &&
                                                                  Lval.equal l1 l2 &&
                                                                  opt_equal ei a1 a2
        | Ndm (s1, l1),              Ndm (s2, l2)              -> Stmt.equal s1 s2 && Lval.equal l1 l2
        | Una (u1, a1, t1),          Una (u2, a2, t2)          -> u1 = u2 && ei a1 a2 && Typ.equal t1 t2
        | Bin (b1, v11, v12, t1),    Bin (b2, v21, v22, t2)    -> b1 = b2 && ei v11 v21 && ei v12 v22 &&
                                                                  Typ.equal t1 t2
        | Sel (m1, a1, t1),          Sel (m2, a2, t2)          -> ei m1 m2 && ei a1 a2 && Typ.equal t1 t2
        | Upd (m1, a1, v1, t1),      Upd (m2, a2, v2, t2)      -> ei m1 m2 && ei a1 a2 && ei v1 v2 && Typ.equal t1 t2
        | Ite (c1, i1, t1, e1, ty1), Ite (c2, i2, t2, e2, ty2) -> Exp.equal c1 c2 &&
                                                                  ei i1 i2 &&
                                                                  ei t1 t2 &&
                                                                  ei e1 e2 &&
                                                                  Typ.equal ty1 ty2
        | Let (s1, b1, e1, v1),      Let (s2, b2, e2, v2)      -> Stmt.equal s1 s2 &&
                                                                  ee.f b1 e1 b2 e2 &&
                                                                  ei v1 v2
        |(Top
         | Bot
         | Cst _
         | Adr _
         | Var _
         | Ndv _
         | Una _
         | Bin _
         | Sel _
         | Ite _
         | Let _),                   _                         -> false
        | Mem _,                     _                         -> false
        | Ndm _,                     _                         -> false
        | Upd _,                     _                         -> false
  end

  let id = ref ~-1

  let mk node = incr id; { node; id = Id.mk !id }

  let rec coerce : type v m k. (v, m, k) t -> (v, m, _) t =
    function
    | { node = Top; _ }
    | { node = Bot; _ }
    | { node = Cst _; _ }
    | { node = Adr _; _ }
    | { node = Var _; _ }
    | { node = Ndv _; _ }
    | { node = Una _; _ }
    | { node = Bin _; _ }
    | { node = Sel _; _ } as v            -> v
    | { node = Mem _; _ } as v            -> v
    | { node = Ndm _; _ } as v            -> v
    | { node = Upd _; _ } as v            -> v
    | { node = Ite (c, i, t, e, ty); id } -> { node = Ite (c, i, coerce t, coerce e, ty); id }
    | { node = Let (s, b, e, v); id }     -> { node = Let (s, b, e, coerce v); id }

  let hash { id; _ } = Id.coerce id

  let equal v1 v2 = Id.equal v1.id v2.id

  let compare v1 v2 = Id.compare v1.id v2.id

  type ('crv, 'crm) pe = { f : 'cev 'cem 'cee.
                                 formatter
                             -> < crv : 'crv; crm : 'crm; cev : 'cev; cem : 'cem; cee : 'cee > binding
                             -> 'cee
                             -> unit }
  [@@unboxed]
  let rec pp : type k. _ -> _ -> _ -> _ -> (_, _, k) t -> _ =
    fun ppv ppm ppe fmt u ->
      let pp f = pp ppv ppm ppe f in
      let pr f = Format.fprintf fmt f in
      match u.node with
      | Top                 -> pr "T"
      | Bot                 -> pr "_|_"
      | Cst c               -> pr "%a" Constant.pretty c
      | Adr g               -> pr "&%a" Global_var.pp g
      | Var v               -> pr "%a" ppv v
      | Mem m               -> pr "%a" ppm m
      | Ndv (s, l, a)       -> pr "*_(%d,%a,%a)" s.sid Lval.pretty l (may % pp) a
      | Ndm (s, l)          -> pr "*_(%d,%a)" s.sid Lval.pretty l
      | Una (u, a, _)       ->(pr "(@[";
                               begin match u with
                               | `Cast t -> pr "(%a)" Cil_printer.pp_typ t
                               | `Minus  -> pr "-"
                               | `Bw_neg -> pr "~"
                               | `Neg    -> pr "!"
                               end;
                               pr " %a@])" pp a)
      | Bin (b, a1, a2, _)  ->(pr "([@%a@ " pp a1;
                               pr @@
                               begin match b with
                               | `Plus        -> "+"
                               | `Minus       -> "-"
                               | `Mult        -> "*"
                               | `Div         -> "/"
                               | `Mod         -> "%%"
                               | `Shift_left  -> "<<"
                               | `Shift_right -> ">>"
                               | `Lt          -> "<"
                               | `Gt          -> ">"
                               | `Le          -> "<="
                               | `Ge          -> ">="
                               | `Eq          -> "=="
                               | `Ne          -> "!="
                               | `Bw_and      -> "&"
                               | `Bw_xor      -> "^"
                               | `Bw_or       -> "|"
                               | `And         -> "&&"
                               | `Or          -> "||"
                               end;
                               pr "@ %a])" pp a2)
      | Sel (m, a, _)       -> pr "%a[@[%a@]]" pp m pp a
      | Upd (m, a, v, _)    -> pr "%a[@[%a@]@ <-@ @[%a@]]" pp m pp a pp v
      | Ite (c, i, t, e, _) -> pr "(@[%a (%d)@ ?@ %a@ :@ %a@])" pp i c.eid pp t pp e
      | Let (_, b, e, _)    -> ppe.f fmt b e
end

module type Summary = sig
  module R : Representant
  module U : Unifiable with module R := R
  module G : Global with module R := R and module U := U
  module F : Function with module R := R and module U := U
  module W : Writes with module R := R and module U := U and module G := G and module F := F

  module Symbolic : sig
    open Symbolic

    type ('v, 'm) env =
      {
        poly_vars   : ('v, 'm, v) t F.Poly.Var.M.t;
        poly_mems   : ('v, 'm, m) t F.Poly.Mem.M.t;
        global_vars : ('v, 'm, v) t G.Var.M.t;
        global_mems : ('v, 'm, m) t G.Mem.M.t
      }

    type 'k u = (W.frameable_var, W.frameable_mem, 'k) t
    type tv
    type tm

    val eq : (tv * tm, v u * m u) eq

    val compare : 'k u -> 'k u -> int
    val equal : 'k u -> 'k u -> bool
    val hash : 'k u -> int

    module Readable : Readables with type v = W.frameable_var and type m = W.frameable_mem

    val readable : (W.frameable_var, W.frameable_mem) readables

    type _ binding +=
        W : ('v, 'm) readables -> < crv : 'crv; crm : 'crm; cev : 'v; cem : 'm; cee : ('crv, 'crm) env > binding

    module V : sig
      type t = tv

      include With_containers with type t := t

      val top : t
      val bot : t
      val cst : constant -> t
      val adr : Global_var.t -> t
      val var : W.frameable_var -> t
      val ndv : stmt -> ?size:t -> lval -> t
      val una : Op.unary -> t -> typ -> t
      val bin : Op.binary -> t -> t -> typ -> t
      val sel : tm -> t -> typ -> t
      val ite : exp -> t -> t -> t -> typ -> t
      val prj : stmt -> ('v, 'm) readables -> ('v, 'm) env -> t -> ('v, 'm, v) Symbolic.t

      val strengthen : stmt -> lval -> t -> t
      val covers : t -> t -> bool
      val weaken : ?join:(t -> t -> t) -> stmt -> lval -> t -> t
      val merge : ?join:(t -> t -> t) -> stmt -> lval -> t -> t -> t
    end
    module M : sig
      type t = tm

      include With_containers with type t := t

      val top : t
      val bot : t
      val cst : constant -> t
      val adr : Global_var.t -> t
      val var : W.frameable_var -> t
      val mem : W.frameable_mem -> t
      val ndv : stmt -> ?size:tv -> lval -> t
      val ndm : stmt -> lval -> t
      val una : Op.unary -> tv -> typ -> t
      val bin : Op.binary -> tv -> tv -> typ -> t
      val sel : tm -> tv -> typ -> t
      val upd : tm -> tv -> tv -> typ -> t
      val ite : exp -> tv -> t -> t -> typ -> t
      val prj : stmt -> ('v, 'm) readables -> ('v, 'm) env -> t -> ('v, 'm, m) Symbolic.t

      val strengthen : stmt -> lval -> t -> t
      val covers : t -> t -> bool
      val weaken : ?join:(t -> t -> t) -> stmt -> lval -> t -> t
      val merge : ?join:(t -> t -> t) -> stmt -> lval -> t -> t -> t
    end
  end

  open Symbolic

  type u =
    {
      pre        : V.t;
      post       : (W.frameable_var, W.frameable_mem) env;
      local_vars : V.t F.Local.Var.M.t;
      local_mems : M.t F.Local.Mem.M.t
    }

  type t
  val eq : (t, u) eq
  val empty : t
  val strengthen : stmt -> (W.readable -> lval) -> t -> t
  val covers : t -> t -> bool
  val merge : join:(V.t -> V.t -> V.t) -> stmt -> (W.readable -> lval) -> t -> t -> t
end

module type Local = sig
  module Repr : Representant
  module U    : Unifiable with module R := Repr
  module G    : Global    with module R := Repr and module U := U
  module F    : Function  with module R := Repr and module U := U
  module W    : Writes    with module R := Repr and module U := U and module G := G and module F := F
  module R    : Reads     with module R := Repr and module U := U and module G := G and module F := F and module W := W
  module A    : Reporting_hashmap with module S := R and type key := W.t
  module S    : Summary   with module R := Repr and module U := U and module G := G and module F := F and module W := W
end

module type Requires = sig
  type t

  val create : Flag.t -> t
  val import : from:t -> t -> unit
  val add_body : fundec -> t -> unit
  val add_stmt : stmt -> t -> unit
  val copy : Flag.t -> t -> t

  val iter_bodies : (fundec -> unit) -> t -> unit
  val iter_stmts : (stmt -> unit) -> t -> unit
  val has_body : fundec -> t -> bool
  val has_stmt : stmt -> t -> bool
end

module Fundec = struct include Fundec let pp = pretty end
module Stmt = struct include Stmt let pp = pretty end

module Requires : Requires = struct
  module H_fundec = Reporting_bithashset (Fundec) ()
  module H_stmt = Reporting_bithashset (Stmt) ()

  type t =
    {
      bodies : H_fundec.t;
      stmts  : H_stmt.t
    }

  let create f = { bodies = H_fundec.create f; stmts = H_stmt.create f }
  let import ~from r =
    H_fundec.import ~from:from.bodies r.bodies;
    H_stmt.import ~from:from.stmts r.stmts
  let add_body f r = H_fundec.add f r.bodies
  let add_stmt s r = H_stmt.add s r.stmts
  let copy f r = { bodies = H_fundec.copy f r.bodies; stmts = H_stmt.copy f r.stmts }

  let iter_bodies f r = H_fundec.iter f r.bodies
  let iter_stmts f r = H_stmt.iter f r.stmts
  let has_body f r = H_fundec.mem f r.bodies
  let has_stmt s r = H_stmt.mem s r.stmts
end

module Void_ptr_var = Variable (struct let is_ok vi = isVoidPtrType vi.vtype end) ()

module type Effect = sig
  module R : Representant
  module U : Unifiable with module R := R
  module G : Global    with module R := R and module U := U

  module type Local = Local with module Repr := R and module U := U and module G := G

  type ('a, 'r, 's) t

  type some =
    | Some :
        { local : (module Local with type A.t = 'a and type R.t = 'r and type S.t = 's);
          eff : ('a, 'r, 's) t } -> some
  val create : Flag.t -> fundec -> some
  val assigns : ('a, _, _) t -> 'a
  val depends : (_, 'r, _) t -> 'r
  val add_result_dep : (_, _, _) t -> unit
  val add_requires : Requires.t -> (_, _, _) t -> unit
  val add_body_req : fundec -> (_, _, _) t -> unit
  val add_stmt_req : stmt -> (_, _, _) t -> unit
  val set_is_target : (_, _, _) t -> unit
  val add_tracking_var : Void_ptr_var.t -> (_, _, _) t -> unit
  val copy : Flag.t -> some -> some

  val is_target : (_, _, _) t -> bool
  val is_tracking_var : Void_ptr_var.t -> (_, _, _) t -> bool
  val has_result_dep : (_, _, _) t -> bool
  val iter_body_reqs : (fundec -> unit) -> some -> unit
  val iter_stmt_reqs : (stmt -> unit) -> some -> unit
  val has_body_req : fundec -> (_, _, _) t -> bool
  val has_stmt_req : stmt -> (_, _, _) t -> bool
  val has_stmt_req' : stmt -> some -> bool
  val flag : (_, _, _) t -> Flag.t

  val summary : (_, _, 's) t -> 's
  val set_summary : 's -> (_, _, 's) t -> unit

  val pp : formatter -> some -> unit
end

module Memory (R : Representant) (U : Unifiable with module R := R) (C : Criterion with type t := R.t) ()
  : Generic_memory with module R := R and module U := U = struct

  type t = R.t * Memory_field.t option

  let mk ?fi u =
    let r = U.repr u in
    if not (C.is_ok r) then
      Console.fatal "Memory.mk: wrong region (not OK): %s : %a vs. %a" (R.name r) pp_typ (R.typ r) R.Kind.pp (R.kind r);
    if isArithmeticOrPointerType (R.typ r) then
      match fi with
      | None    -> r, None
      | Some fi -> Console.fatal
                     "Memory.mk: fields can't be specified for primitive regions: %s.%s for %s"
                     fi.fcomp.cname fi.fname (R.name @@ U.repr u)
    else
      match[@warning "-4"] unrollTypeDeep (R.typ r), fi with
      | TComp (ci, _ ,_), Some fi
        when Compinfo.equal ci fi.fcomp -> r, Some (Memory_field.of_fieldinfo fi)
      | _,                None          -> Console.fatal
                                             "Memory.mk: improper region (with no field): %s : %a"
                                             (R.name r) pp_typ (R.typ r)
      | _,                Some fi       -> Console.fatal
                                             "Memory.mk: improper combination of region and field: \
                                              %s : %a and %s.%s : %a"
                                             (R.name r) pp_typ (R.typ r)
                                             (compFullName fi.fcomp) fi.fname pp_typ fi.ftype

  let prj ~find ~mk (r, fi : t) = mk ?fi:(fi :> fieldinfo option) @@ find @@ U.of_repr r

  let equal (r1, fo1) (r2, fo2) = R.equal r1 r2 && opt_equal Memory_field.equal fo1 fo2

  let hash (r, fo) = 997 * R.hash r + opt_hash Memory_field.hash fo

  let compare (r1, fo1) (r2, fo2) =
    let r = R.compare r1 r2 in
    if r <> 0 then r else opt_compare Memory_field.compare fo1 fo2

  let pp fmttr =
    let pp fmt = fprintf fmttr fmt in
    function
    | r, Some fi -> pp "%a->%a" R.pp r Memory_field.pp fi
    | r, None    -> pp "*%a" R.pp r

  module H = Reporting_bithashset (struct type nonrec t = t let equal = equal let hash = hash let pp = pp end) ()
  module M = Map.Make (struct type nonrec t = t let compare = compare end)
end

module Global (R : Representant) (U : Unifiable with module R := R) () :
  Global with module R := R and module U := U = struct

  module Var = Variable (struct let is_ok vi = isArithmeticOrPointerType vi.vtype && vi.vglob end) ()
  module Mem = Memory (R) (U) (struct let is_ok r = R.kind r = `Global end) ()
end

module Function (R : Representant) (U : Unifiable with module R := R) (F : sig val f : fundec end) () :
  Function with module R := R and module U := U = struct
  module Local = struct
    module Var =
      Variable
        (struct
          let is_ok vi =
            isArithmeticOrPointerType vi.vtype
            && not vi.vglob
            && not vi.vformal
            && List.exists (Varinfo.equal vi) F.f.slocals
        end)
        ()
    module Mem =
      Memory
        (R)
        (U)
        (struct let is_ok r = match R.kind r with `Local f when String.equal f F.f.svar.vname -> true | _ -> false end)
        ()
  end
  module Poly = struct
    module Var =
      Variable
        (struct
          let is_ok vi =
            isArithmeticOrPointerType vi.vtype
            && vi.vformal
            && List.exists (Varinfo.equal vi) F.f.sformals
        end)
        ()
    module Mem =
      Memory
        (R)
        (U)
        (struct let is_ok r = match R.kind r with `Poly f when String.equal f F.f.svar.vname -> true | _ -> false end)
        ()
  end
  let f = F.f
end

module Writes
    (R : Representant)
    (U : Unifiable with module R := R)
    (G : Global with module R := R and module U := U)
    (F : Function with module R := R and module U := U) :
  Writes with module R := R and module U := U and module G := G and module F := F = struct
  type frameable_var =
    [  `Global_var of G.Var.t
    | `Poly_var   of F.Poly.Var.t ]

  type frameable_mem =
    [ `Global_mem of G.Mem.t
    | `Poly_mem   of F.Poly.Mem.t ]

  type frameable = [ frameable_var | frameable_mem ]

  type readable =
    [ frameable
    | `Local_var  of F.Local.Var.t
    | `Local_mem  of F.Local.Mem.t ]

  module T = struct
    type t = [ readable | `Result ]

    let compare w1 w2 =
      match w1, w2 with
      | `Global_var v1, `Global_var v2  -> G.Var.compare v1 v2
      | `Global_var _,  _               -> -1
      | `Poly_var _,    `Global_var _   -> 1
      | `Poly_var v1,   `Poly_var v2    -> F.Poly.Var.compare v1 v2
      | `Poly_var _,    _               -> -1
      | `Local_var _,  (`Global_var _
                       | `Poly_var _)   -> 1
      | `Local_var v1, ` Local_var v2   -> F.Local.Var.compare v1 v2
      | `Local_var _,   _               -> -1
      | `Global_mem _, (`Global_var _
                       | `Poly_var _
                       | `Local_var _)  -> 1
      | `Global_mem m1, `Global_mem m2  -> G.Mem.compare m1 m2
      | `Global_mem _,  _               -> -1
      | `Poly_mem _,   (`Global_var _
                       | `Poly_var _
                       | `Local_var _
                       | `Global_mem _) -> 1
      | `Poly_mem m1,  `Poly_mem m2     -> F.Poly.Mem.compare m1 m2
      | `Poly_mem _,    _               -> -1
      | `Local_mem _,  (`Global_var _
                       | `Poly_var _
                       | `Local_var _
                       | `Global_mem _
                       | `Poly_mem _)   -> 1
      | `Local_mem m1, `Local_mem m2    -> F.Local.Mem.compare m1 m2
      | `Local_mem _,   _               -> -1
      | `Result,        `Result         -> 0
      | `Result,        #t              -> 1

    let equal w1 w2 =
      match[@warning "-4"] w1, w2 with
      | `Global_var v1, `Global_var v2 -> G.Var.equal       v1 v2
      | `Poly_var v1,   `Poly_var v2   -> F.Poly.Var.equal  v1 v2
      | `Local_var v1,  `Local_var v2  -> F.Local.Var.equal v1 v2
      | `Global_mem m1, `Global_mem m2 -> G.Mem.equal       m1 m2
      | `Poly_mem m1,   `Poly_mem m2   -> F.Poly.Mem.equal  m1 m2
      | `Local_mem m1,  `Local_mem m2  -> F.Local.Mem.equal m1 m2
      | `Result,        `Result        -> true
      | #t,             #t             -> false

    let hash =
      function
      | `Global_var v -> 7 * G.Var.hash v
      | `Poly_var v   -> 7 * F.Poly.Var.hash v  + 1
      | `Local_var v  -> 7 * F.Local.Var.hash v + 2
      | `Global_mem m -> 7 * G.Mem.hash m       + 3
      | `Poly_mem m   -> 7 * F.Poly.Mem.hash m  + 4
      | `Local_mem m  -> 7 * F.Local.Mem.hash m + 5
      | `Result       -> 6
  end
  include T
  module H = FCHashtbl.Make (T)
  module M = FCMap.Make (T)
  module S = FCSet.Make (T)

  let pp fmttr =
    let pp fmt = fprintf fmttr fmt in
    function
    | `Global_var v -> pp "^%a" G.Var.pp       v
    | `Poly_var v   -> pp "'%a" F.Poly.Var.pp  v
    | `Local_var v  -> pp "~%a" F.Local.Var.pp v
    | `Global_mem m -> pp "^%a" G.Mem.pp       m
    | `Poly_mem m   -> pp "'%a" F.Poly.Mem.pp  m
    | `Local_mem m  -> pp "~%a" F.Local.Mem.pp m
    | `Result       -> pp "!R"

  let compare' = compare
  let equal' = equal
  let hash' = hash
  let pp' = pp
end

module Reads
    (R : Representant)
    (U : Unifiable with module R := R)
    (G : Global with module R := R and module U := U)
    (F : Function with module R := R and module U := U)
    (W : Writes with module R := R and module U := U and module G := G and module F := F) :
  Reads with module R := R and module U := U and module G := G and module F := F and module W := W = struct

  type _ kind =
    | Global_var : G.Var.t       kind
    | Poly_var   : F.Poly.Var.t  kind
    | Local_var  : F.Local.Var.t kind
    | Global_mem : G.Mem.t       kind
    | Poly_mem   : F.Poly.Mem.t  kind
    | Local_mem  : F.Local.Mem.t kind

  type some = Some : 'a kind * 'a -> some

  type t =
    {
      global_vars : G.Var.H.t;
      poly_vars   : F.Poly.Var.H.t;
      local_vars  : F.Local.Var.H.t;
      global_mems : G.Mem.H.t;
      poly_mems   : F.Poly.Mem.H.t;
      local_mems  : F.Local.Mem.H.t
    }

  type ('w, _) reads += W : (W.t, t) reads

  let of_write : _ -> some =
    function
      [@warning "-42"]
    | `Global_var v -> Some (Global_var, v)
    | `Local_var  v -> Some (Local_var, v)
    | `Poly_var   v -> Some (Poly_var, v)
    | `Global_mem m -> Some (Global_mem, m)
    | `Local_mem  m -> Some (Local_mem, m)
    | `Poly_mem   m -> Some (Poly_mem, m)

  let create f =
    { global_vars = G.Var.H.create       f;
      poly_vars   = F.Poly.Var.H.create  f;
      local_vars  = F.Local.Var.H.create f;
      global_mems = G.Mem.H.create       f;
      poly_mems   = F.Poly.Mem.H.create  f;
      local_mems  = F.Local.Mem.H.create f }

  let clear r =
    G.Var.H.clear       r.global_vars;
    F.Poly.Var.H.clear  r.poly_vars;
    F.Local.Var.H.clear r.local_vars;
    G.Mem.H.clear       r.global_mems;
    F.Poly.Mem.H.clear  r.poly_mems;
    F.Local.Mem.H.clear r.local_mems

  let import ~from r =
    G.Var.H.import       ~from:from.global_vars r.global_vars;
    F.Poly.Var.H.import  ~from:from.poly_vars   r.poly_vars;
    F.Local.Var.H.import ~from:from.local_vars  r.local_vars;
    G.Mem.H.import       ~from:from.global_mems r.global_mems;
    F.Poly.Mem.H.import  ~from:from.poly_mems   r.poly_mems;
    F.Local.Mem.H.import ~from:from.local_mems  r.local_mems

  let add_global_var v r = G.Var.H.add       v r.global_vars
  let add_poly_var   v r = F.Poly.Var.H.add  v r.poly_vars
  let add_local_var  v r = F.Local.Var.H.add v r.local_vars
  let add_global_mem m r = G.Mem.H.add       m r.global_mems
  let add_poly_mem   m r = F.Poly.Mem.H.add  m r.poly_mems
  let add_local_mem  m r = F.Local.Mem.H.add m r.local_mems

  let add : type a. a kind -> a -> _ = fun k x r ->
    match k with
    | Global_var -> G.Var.H.add       x r.global_vars
    | Poly_var   -> F.Poly.Var.H.add  x r.poly_vars
    | Local_var  -> F.Local.Var.H.add x r.local_vars
    | Global_mem -> G.Mem.H.add       x r.global_mems
    | Poly_mem   -> F.Poly.Mem.H.add  x r.poly_mems
    | Local_mem  -> F.Local.Mem.H.add x r.local_mems

  let add_some (e : some) r = let Some (k, x) = e in add k x r

  let sub r ~from =
    G.Var.H.sub       r.global_vars ~from:from.global_vars;
    F.Poly.Var.H.sub  r.poly_vars   ~from:from.poly_vars;
    F.Local.Var.H.sub r.local_vars  ~from:from.local_vars;
    G.Mem.H.sub       r.global_mems ~from:from.global_mems;
    F.Poly.Mem.H.sub  r.poly_mems   ~from:from.poly_mems;
    F.Local.Mem.H.sub r.local_mems  ~from:from.local_mems

  let mem : type a. a kind -> a -> _ = fun k x r ->
    match k with
    | Global_var -> G.Var.H.mem       x r.global_vars
    | Poly_var   -> F.Poly.Var.H.mem  x r.poly_vars
    | Local_var  -> F.Local.Var.H.mem x r.local_vars
    | Global_mem -> G.Mem.H.mem       x r.global_mems
    | Poly_mem   -> F.Poly.Mem.H.mem  x r.poly_mems
    | Local_mem  -> F.Local.Mem.H.mem x r.local_mems

  let mem_some (e : some) r = let Some (k, x) = e in mem k x r

  let intersects r1 r2 =
    G.Var.H.intersects       r1.global_vars r2.global_vars ||
    F.Poly.Var.H.intersects  r1.poly_vars   r2.poly_vars   ||
    F.Local.Var.H.intersects r1.local_vars  r2.local_vars  ||
    G.Mem.H.intersects       r1.global_mems r2.global_mems ||
    F.Poly.Mem.H.intersects  r1.poly_mems   r2.poly_mems   ||
    F.Local.Mem.H.intersects r1.local_mems  r2.local_mems

  let flag r = G.Var.H.flag r.global_vars

  let copy f r =
    { global_vars = G.Var.H.copy      f r.global_vars;
      poly_vars = F.Poly.Var.H.copy   f r.poly_vars;
      local_vars = F.Local.Var.H.copy f r.local_vars;
      global_mems = G.Mem.H.copy      f r.global_mems;
      poly_mems = F.Poly.Mem.H.copy   f r.poly_mems;
      local_mems = F.Local.Mem.H.copy f r.local_mems }

  let iter_global_vars f r = G.Var.H.iter       f r.global_vars
  let iter_poly_vars   f r = F.Poly.Var.H.iter  f r.poly_vars
  let iter_local_vars  f r = F.Local.Var.H.iter f r.local_vars
  let iter_global_mems f r = G.Mem.H.iter       f r.global_mems
  let iter_poly_mems   f r = F.Poly.Mem.H.iter  f r.poly_mems
  let iter_local_mems  f r = F.Local.Mem.H.iter f r.local_mems

  let fold_global_vars f r = G.Var.H.fold       f r.global_vars
  let fold_poly_vars   f r = F.Poly.Var.H.fold  f r.poly_vars
  let fold_local_vars  f r = F.Local.Var.H.fold f r.local_vars
  let fold_global_mems f r = G.Mem.H.fold       f r.global_mems
  let fold_poly_mems   f r = F.Poly.Mem.H.fold  f r.poly_mems
  let fold_local_mems  f r = F.Local.Mem.H.fold f r.local_mems

  let iter f r =
    iter_global_mems (fun m -> f @@ `Global_mem m) r;
    iter_poly_mems   (fun m -> f @@ `Poly_mem   m) r;
    iter_local_mems  (fun m -> f @@ `Local_mem  m) r;
    iter_global_vars (fun v -> f @@ `Global_var v) r;
    iter_poly_vars   (fun v -> f @@ `Poly_var   v) r;
    iter_local_vars  (fun v -> f @@ `Local_var  v) r

  let fold f r =
    fold_global_mems (fun m -> f @@ `Global_mem m) r %>
    fold_poly_mems   (fun m -> f @@ `Poly_mem   m) r %>
    fold_local_mems  (fun m -> f @@ `Local_mem  m) r %>
    fold_global_vars (fun v -> f @@ `Global_var v) r %>
    fold_poly_vars   (fun v -> f @@ `Poly_var   v) r %>
    fold_local_vars  (fun v -> f @@ `Local_var  v) r

  let is_empty r =
    G.Var.H.is_empty       r.global_vars &&
    F.Poly.Var.H.is_empty  r.poly_vars   &&
    F.Local.Var.H.is_empty r.local_vars  &&
    G.Mem.H.is_empty       r.global_mems &&
    F.Poly.Mem.H.is_empty  r.poly_mems   &&
    F.Local.Mem.H.is_empty r.local_mems

  let length r =
    List.fold_left
      (+)
      0
      [G.Var.H.length       r.global_vars;
       F.Poly.Var.H.length  r.poly_vars;
       F.Local.Var.H.length r.local_vars;
       G.Mem.H.length       r.global_mems;
       F.Poly.Mem.H.length  r.poly_mems;
       F.Local.Mem.H.length r.local_mems]

  let is_singleton r = length r = 1

  let pp fmt r =
    fprintf fmt "@[{gv:%a,@ pv:%a,@ lv:%a,@ gm:%a,@ pm:%a,@ lm:%a}@]"
      G.Var.H.pp       r.global_vars
      F.Poly.Var.H.pp  r.poly_vars
      F.Local.Var.H.pp r.local_vars
      G.Mem.H.pp       r.global_mems
      F.Poly.Mem.H.pp  r.poly_mems
      F.Local.Mem.H.pp r.local_mems
end

module Summary
    (R : Representant)
    (U : Unifiable with module R := R)
    (G : Global with module R := R and module U := U)
    (F : Function with module R := R and module U := U)
    (W : Writes with module R := R and module U := U and module G := G and module F := F)
    () :
  Summary with module R := R and module U := U and module G := G and module F := F and module W := W = struct

  module Symbolic = struct
    open Symbolic

    type ('v, 'm) env =
      {
        poly_vars   : ('v, 'm, v) t F.Poly.Var.M.t;
        poly_mems   : ('v, 'm, m) t F.Poly.Mem.M.t;
        global_vars : ('v, 'm, v) t G.Var.M.t;
        global_mems : ('v, 'm, m) t G.Mem.M.t
      }

    type 'k u = (W.frameable_var, W.frameable_mem, 'k) t
    type tv = v u
    type tm = m u

    let eq = Refl

    module Readable = struct
      type v = W.frameable_var
      type m = W.frameable_mem
      type (_, _) readable += W : (v, m) readable
      let f = F.f
    end

    let readable : (W.frameable_var, W.frameable_mem) readables = (module Readable)

    type _ binding +=
        W : ('v, 'm) readables -> < crv : 'crv; crm : 'crm; cev : 'v; cem : 'm; cee : ('crv, 'crm) env > binding

    module Bare = struct
      open Node
      type _ k =
        | V : v k
        | M : m k
      type t = E : ('v, 'm) readables * 'k k * ('v, 'm, 'k) node -> t
      let hash (type v m) (r : (v, m) readables) (n : (v, m, _) node) =
        hash
          (fun f -> let Refl = eq_readables r readable in W.hash' f : v -> _)
          (fun f -> let Refl = eq_readables r readable in W.hash' f : m -> _)
          { f = fun (type e cv cm) (w : < crv : v; crm : m; cev : cv; cem : cm; cee : e > binding) (e : e) ->
              match w with
              | W _ ->(let fold hash v u acc = 15487399 * acc + 105871 * hash v + Id.hash u.id in
                       15487399 * F.Poly.Var.M.fold (fold F.Poly.Var.hash) e.poly_vars 0 +
                       105871 * F.Poly.Mem.M.fold (fold F.Poly.Mem.hash) e.poly_mems 0 +
                       1351 * G.Var.M.fold (fold G.Var.hash) e.global_vars 0 +
                       G.Mem.M.fold (fold G.Mem.hash) e.global_mems 0)
              | _   -> Console.fatal "Symbolic.Bare.hash: unexpected witness" }
          n
      let hash ( E (r, _, n)) = hash r n
      let equal
            (type v m) (r : (v, m) readables) (n1 : (v, m, _) node) (n2 : (v, m, _) node) =
        equal
          (fun f -> let Refl = eq_readables r readable in W.equal' f : v -> v -> _)
          (fun f -> let Refl = eq_readables r readable in W.equal' f : m -> m -> _)
          { f = fun (type cv1 cm1 cv2 cm2 e1 e2)
              (w1 : < crv : v; crm : m; cev : cv1; cem : cm1; cee : e1 > binding) (e1 : e1)
              (w2 : < crv : v; crm : m; cev : cv2; cem : cm2; cee : e2 > binding) (e2 : e2) ->
              match w1, w2 with
              | W _, W _ ->(let by_id v1 v2 = Id.equal v1.id v2.id in
                            F.Poly.Var.M.equal by_id e1.poly_vars e2.poly_vars &&
                            F.Poly.Mem.M.equal by_id e1.poly_mems e2.poly_mems &&
                            G.Var.M.equal by_id e1.global_vars e2.global_vars &&
                            G.Mem.M.equal by_id e1.global_mems e2.global_mems)
              | _        -> Console.fatal "Symbolic.Bare.equal: unexpected witness" }
          n1 n2
      let equal (E ((module R1) as r1 , _, n1)) (E ((module R2), _, n2)) =
        match R1.W with
        | R2.W -> equal r1 n1 n2
        | _    -> false
    end

    type mk = { f : 'v 'm 'k. ('v, 'm) readables -> 'k Bare.k -> ('v, 'm, 'k) node -> ('v, 'm, 'k) t } [@@unboxed]
    let mk : mk =
      let module Ex = struct type t = E : ('v, 'm) readables * 'k Bare.k * ('v, 'm, 'k) Symbolic.t -> t end in
      let module H = Hashtbl.Make (Bare) in
      let h = H.create 128 in
      { f = fun (type v m k) ((module R0) as r : (v, m) readables) (k0 : k Bare.k) n : (v, m, k) t ->
          let Ex.E ((module R1), k1, v) =
            let k = Bare.E (r, k0, n) in
            try
              H.find h k
            with Not_found ->
              let r = Ex.E (r, k0, mk n) in
              H.add h k r;
              r
          in
          match R1.W, (k1, k0) with
          | R0.W, Bare.(V, V) -> v
          | R0.W, Bare.(M, M) -> v
          | _,    Bare.(V, _) -> Console.fatal "Symbolic.mk: unexpected witness"
          | _,    Bare.(M, _) -> Console.fatal "Symbolic.mk: unexpected witness" }

    let mk' k = mk.f readable k

    let top k = mk' k Top
    let bot k = mk' k Bot
    let cst k c = mk' k @@ Cst c
    let adr k g = mk' k @@ Adr g
    let var k v = mk' k @@ Var v
    let mem m = mk' Bare.M @@ Mem m
    let ndv k s ?size l = mk' k @@ Ndv (s, l, size)
    let ndm s l = mk' Bare.M @@ Ndm (s, l)
    let una k u a t = mk' k @@ Una (u, a, t)
    let bin k b a1 a2 t = mk' k @@ Bin (b, a1, a2, t)
    let sel k m a t = mk' k @@ Sel (m, a, t)
    let upd m a v t = mk' Bare.M @@ Upd (m, a, v, t)
    let ite k c i t e ty = mk' k @@ Ite (c, i, t, e, ty)
    let prj k s r e v = mk.f r k @@ Let (s, W readable, e, v)

    let pp fmt =
      let pp_id fmt v = fprintf fmt "%a" Id.pp v.id in
      pp
        W.pp'
        W.pp'
        { f = fun (type v m e)
            fmt (w : < crv : W.frameable_var; crm : W.frameable_mem; cev : v; cem : m; cee : e > binding) (e : e) ->
            match w with
            | W _ -> Pretty_utils
                     .(fprintf fmt "(@[[{%a}@ {%a}@ {%a}@ {%a}]@ @] ...)"
                         (pp_iter2 ~sep:",@ " ~between:" -> " F.Poly.Var.M.iter F.Poly.Var.pp pp_id) e.poly_vars
                         (pp_iter2 ~sep:",@ " ~between:" -> " F.Poly.Mem.M.iter F.Poly.Mem.pp pp_id) e.poly_mems
                         (pp_iter2 ~sep:",@ " ~between:" -> " G.Var.M.iter G.Var.pp pp_id) e.global_vars
                         (pp_iter2 ~sep:",@ " ~between:" -> " G.Mem.M.iter G.Mem.pp pp_id) e.global_mems)
            | _   -> Console.fatal "Symbolic.pp: unexpected witness" }
        fmt

    let nondet (type k) : k Bare.k -> _ -> ?size:_ -> _ -> k u =
      let open Bare in
      fun k s ?size l ->
        match k with
        | V -> ndv V s ?size l
        | M -> ndm s l

    let strengthen (type k) k s l (v : k u) : k u =
      match v.node with
      | Bot
      | Cst _
      | Adr _
      | Var _
      | Ndv _
      | Una _
      | Bin _
      | Sel _
      | Ite _
      | Let _ -> v
      | Mem _ -> v
      | Ndm _ -> v
      | Upd _ -> v
      | Top   -> nondet k s l

    let covers (type k) (v1 : k u) (v2 : k u) =
      match v1.node, v2.node with
      | Top,       _
      | _,        Bot    -> true
      | _,        _
        when equal v1 v2 -> true
      | (Bot
        | Cst _
        | Adr _
        | Var _
        | Ndv _
        | Una _
        | Bin _
        | Sel _
        | Ite _
        | Let _), _      -> false
      | Mem _,    _      -> false
      | Ndm _,    _      -> false
      | Upd _,    _      -> false
    let sid = Sid.next ()
    let dummy_int = Cil.var @@ makeVarinfo true false "pre" intType
    let rec merge : type k. k Bare.k -> ?join:(k u -> k u -> k u) -> _ -> _ -> k u -> k u -> k u =
      fun k ?join s l v1 v2 ->
        let merge_v v1 v2 =
          let s = { s with sid } in
          let l = dummy_int in
          Bare.(merge V s l (weaken V s l v1) (weaken V s l v2))
        and merge = merge k ?join s l
        in
        let join_ () = may_map ~dft:(nondet k s l) (fun j -> j v1 v2) join in
        match v1.node, v2.node with
        | Top,                       _
        | _,                         Top                       -> top k
        | Bot,                       _                         -> v2
        | _,                         Bot                       -> v1
        | Ite (c1, i1, t1, e1, ty1), Ite (c2, i2, t2, e2, _)
          when Exp.equal c1 c2
            && equal i1 i2                                     -> ite k c1 i1 (merge t1 t2) (merge e1 e2) ty1
        | Ite (c1, i1, t1, e1, ty),  Ite (c2, i2, t2, e2, _)
          when Exp.equal c1 c2 && not (has_some join)          -> ite
                                                                    k c1 (merge_v i1 i2) (merge t1 t2) (merge e1 e2) ty
        | Ite (c1, i1, t1, e1, ty1), Ite (c2, _, _, _, _)
          when Exp.compare c1 c2 < 0                           -> ite k c1 i1 (merge t1 v2) (merge e1 v2) ty1
        | _,                         Ite (c, i, t, e, ty)      -> ite k c i (merge v1 t) (merge v1 e) ty
        | Ite (c, i, t, e, ty),      _                         -> ite k c i (merge t v2) (merge e v2) ty
        | _,                         _
          when equal v1 v2                                     -> v1
        | Ndv (s1, l1, Some a1),     Ndv (s2, l2, Some a2)
          when Stmt.equal s1 s2 && Lval.equal l1 l2            -> nondet k s1 ~size:(merge_v a1 a2) l1
        |(Cst _
         | Adr _
         | Var _
         | Ndv _
         | Una _
         | Bin  _
         | Sel _
         | Let _),                   _                         -> join_ ()
        | Mem _,                     _                         -> join_ ()
        | Ndm _,                     _                         -> join_ ()
        | Upd _,                     _                         -> join_ ()
    and weaken : type k. k Bare.k -> ?join:(k u -> k u -> k u) ->_ -> _ -> k u -> k u =
      fun k ?join s l v ->
        let weaken = weaken k s l in
        let merge = merge k ?join s l in
        match v.node with
        | Ite (c, i,
               { node = Ite (ct, _, tt, et, _); _ },
               { node = Ite (ce, _, te, ee, _); _ },
               ty)
          when Exp.(equal c ct && equal ct ce)       -> ite k c i
                                                          (merge (weaken tt) (weaken et))
                                                          (merge (weaken te) (weaken ee)) ty
        | Ite (c, i,
               { node = Ite (ct, _, tt, et, _); _ },
               e, ty)
          when Exp.equal c ct                        -> ite k c i (merge (weaken tt) (weaken et)) (weaken e) ty
        | Ite (c, i, t,
               { node = Ite (ce, _, te, ee, _); _ },
               ty)
          when Exp.equal c ce                        -> ite k c i (weaken t) (merge (weaken te) (weaken ee)) ty
        | Ite (c, i, t, e, ty)                       -> ite k c i (weaken t) (weaken e) ty
        | (Top
          | Bot
          | Cst _
          | Adr _
          | Var _
          | Ndv _
          | Una _
          | Bin _
          | Sel _
          | Let _)                                   -> v
        | Mem _                                      -> v
        | Ndm _                                      -> v
        | Upd _                                      -> v

    let merge k ?join s l v1 v2 = merge k ?join s l (weaken k ?join s l v1) (weaken k ?join s l v2)

    module V = struct
      module T = struct
        type t = tv
        let hash = hash
        let equal = equal
        let compare = compare
      end
      include T
      module H = FCHashtbl.Make (T)
      module M = FCMap.Make (T)
      module S = FCSet.Make (T)

      open Bare
      let top = top V
      let bot = bot V
      let cst = cst V
      let adr = adr V
      let var = var V
      let ndv = ndv V
      let una = una V
      let bin = bin V
      let sel = sel V
      let ite = ite V
      let prj r = prj V r

      let strengthen = strengthen V
      let weaken = weaken V
      let covers = covers
      let merge = merge V
      let pp = pp
    end

    module M = struct
      module T = struct
        type t = tm
        let hash = hash
        let equal = equal
        let compare = compare
      end
      include T
      module H = FCHashtbl.Make (T)
      module M = FCMap.Make (T)
      module S = FCSet.Make (T)

      open Bare
      let top = top M
      let bot = bot M
      let cst = cst M
      let adr = adr M
      let var = var M
      let mem = mem
      let ndv = ndv M
      let ndm = ndm
      let una = una M
      let bin = bin M
      let sel = sel M
      let upd = upd
      let ite = ite M
      let prj r = prj M r

      let strengthen = strengthen M
      let weaken = weaken M
      let covers = covers
      let merge = merge M
      let pp = pp
    end

    let compare = compare
    let equal = equal
    let hash = hash
  end

  type u =
    {
      pre        : Symbolic.V.t;
      post       : (W.frameable_var, W.frameable_mem) Symbolic.env;
      local_vars : Symbolic.V.t F.Local.Var.M.t;
      local_mems : Symbolic.M.t F.Local.Mem.M.t
    }

  type t = u
  let eq = Refl

  open Symbolic
  let empty =
    {
      pre = V.bot;
      post =
        {
          poly_vars   = F.Poly.Var.M.empty;
          poly_mems   = F.Poly.Mem.M.empty;
          global_vars = G.Var.M.empty;
          global_mems = G.Mem.M.empty
        };
      local_vars = F.Local.Var.M.empty;
      local_mems = F.Local.Mem.M.empty
    }
  let strengthen stmt f s =
    let strengthen streng map wr = map @@ streng stmt % f % wr in
    let strengthen_v f = strengthen V.strengthen f and strengthen_m f = strengthen M.strengthen f in
    {
      pre = s.pre;
      post =
        {
          poly_vars   = strengthen_v F.Poly.Var.M.mapi  (fun v -> `Poly_var v)   s.post.poly_vars;
          poly_mems   = strengthen_m F.Poly.Mem.M.mapi  (fun m -> `Poly_mem m)   s.post.poly_mems;
          global_vars = strengthen_v G.Var.M.mapi       (fun v -> `Global_var v) s.post.global_vars;
          global_mems = strengthen_m G.Mem.M.mapi       (fun m -> `Global_mem m) s.post.global_mems
        };
      local_vars      = strengthen_v F.Local.Var.M.mapi (fun v -> `Local_var v)  s.local_vars;
      local_mems      = strengthen_m F.Local.Mem.M.mapi (fun m -> `Local_mem m)  s.local_mems
    }
  let covers s1 s2 =
    covers s2.pre s1.pre &&
    let covers_ find m k v = try covers (find k m) v with Not_found -> false in
    F.Poly.Var.M.(for_all  (covers_ find s1.post.poly_vars)   s2.post.poly_vars) &&
    F.Poly.Mem.M.(for_all  (covers_ find s1.post.poly_mems)   s2.post.poly_mems) &&
    G.Var.M.(for_all       (covers_ find s1.post.global_vars) s2.post.global_vars) &&
    G.Mem.M.(for_all       (covers_ find s1.post.global_mems) s2.post.global_mems) &&
    F.Local.Var.M.(for_all (covers_ find s1.local_vars)       s2.local_vars) &&
    F.Local.Mem.M.(for_all (covers_ find s1.local_mems)       s2.local_mems)
  let merge ~join stmt f s1 s2 =
    let merge mrg wr k v1 v2 = opt_fold (fun v2 _ -> some @@ opt_fold (mrg stmt @@ f @@ wr k) v1 v2) v2 v1 in
    let merge_v wr = merge V.merge wr and merge_m wr = merge M.merge wr in
    {
      pre = V.merge ~join stmt dummy_int s1.pre s2.pre;
      post =
        {
          poly_vars   =
            F.Poly.Var.M.merge (merge_v @@ fun v -> `Poly_var v)   s1.post.poly_vars   s2.post.poly_vars;
          poly_mems   =
            F.Poly.Mem.M.merge (merge_m @@ fun m -> `Poly_mem m)   s1.post.poly_mems   s2.post.poly_mems;
          global_vars =
            G.Var.M.merge      (merge_v @@ fun v -> `Global_var v) s1.post.global_vars s2.post.global_vars;
          global_mems =
            G.Mem.M.merge      (merge_m @@ fun m -> `Global_mem m) s1.post.global_mems s2.post.global_mems;
        };
      local_vars      = F.Local.Var.M.merge (merge_v @@ fun v -> `Local_var v) s1.local_vars       s2.local_vars;
      local_mems      = F.Local.Mem.M.merge (merge_m @@ fun m -> `Local_mem m) s1.local_mems       s2.local_mems
    }
end

module H_void_ptr_var = Reporting_bithashset (Void_ptr_var) ()

module Effect
    (R : Representant)
    (U : Unifiable with module R := R)
    (G : Global with module R := R and module U := U)
  : Effect with module R := R and module U := U and module G := G = struct

  type ('a, 'r, 's) t =
    {
      assigns            : 'a;
      tracking           : H_void_ptr_var.t;
      mutable is_target  : bool;
      depends            : 'r;
      mutable result_dep : bool;
      requires           : Requires.t;
      mutable summary    : 's;
      flag               : Flag.t;
    }

  module type Local = Local with module Repr := R and module U := U and module G := G

  type some =
    | Some :
        { local : (module Local with type A.t = 'a and type R.t = 'r and type S.t = 's);
          eff : ('a, 'r, 's) t } -> some

  let create f fundec : some =
    let module F = Function (R) (U) (struct let f = fundec end) () in
    let module W = Writes (R) (U) (G) (F) in
    let module S = Summary (R) (U) (G) (F) (W) () in
    let module R = Reads (R) (U) (G) (F) (W) in
    let module A = Reporting_hashmap (W) (R) in
    let module Local = struct module F = F module W = W module A = A module R = R module S = S end in
    Some {
      local = (module Local);
      eff = {
        assigns    = A.create f;
        tracking   = H_void_ptr_var.create f;
        is_target  = false;
        depends    = R.create f;
        result_dep = false;
        requires   = Requires.create f;
        summary    = S.empty;
        flag       = f
      }}

  let assigns e = e.assigns
  let depends e = e.depends
  let add_result_dep e = if not e.result_dep then Flag.report e.flag; e.result_dep <- true
  let add_requires d e = Requires.import ~from:d e.requires
  let set_is_target e = if not e.is_target then Flag.report e.flag; e.is_target <- true

  let add_body_req f e = Requires.add_body f e.requires
  let add_stmt_req s e = Requires.add_stmt s e.requires
  let has_body_req f e = Requires.has_body f e.requires
  let has_stmt_req s e = Requires.has_stmt s e.requires
  let has_stmt_req' s (Some { eff; _ } : some) = has_stmt_req s eff
  let add_tracking_var v e = H_void_ptr_var.add v e.tracking
  let copy f (Some { local = (module L) as local; eff = e } : some) : some =
    Some {
      local;
      eff = {
        assigns    = L.A.copy f e.assigns;
        tracking   = H_void_ptr_var.copy f e.tracking;
        is_target  = e.is_target;
        depends    = L.R.copy f e.depends;
        result_dep = e.result_dep;
        requires   = Requires.copy f e.requires;
        summary    = e.summary;
        flag       = f }}

  let is_target e = e.is_target
  let has_result_dep e = e.result_dep
  let is_tracking_var v e = H_void_ptr_var.mem v e.tracking
  let iter_body_reqs f (Some { eff; _ } : some) = Requires.iter_bodies f eff.requires
  let iter_stmt_reqs f (Some { eff; _ } : some) = Requires.iter_stmts f eff.requires
  let flag e = e.flag

  let summary e = e.summary
  let set_summary s e = e.summary <- s

  let pp fmt (Some { local = (module L); eff = e } : some) =
    fprintf fmt "@[{@[<2>ass:@\n%a;@]@\n@[<2>track:@\n%a;@]@\n@[<2>tar:@\n%B;@]@\n@[<2>deps:@\n%a@]@\n@[<2>RD:%B@]}@]"
      L.A.pp e.assigns H_void_ptr_var.pp e.tracking e.is_target L.R.pp e.depends e.result_dep
end

module Field_key =
  Datatype.Triple_with_collections (Compinfo) (Typ) (Datatype.Integer) (struct let module_name = "field key" end)

module H_field = Field_key.Hashtbl
module H_fundec = Fundec.Hashtbl
module H_stmt = Stmt.Hashtbl
module H_stmt_conds = struct
  include Stmt.Hashtbl

  module Hide = struct
    let cache = create 256 (* Work-around the value restriction and avoid re-exporting the cache *)
    module Show = struct
      let iter_all f h =
        clear cache;
        iter (const' @@ fun k -> memo cache k @@ fun k -> f k @@ find_all h k) h
    end
  end
  include Hide.Show
end

type 'a offs = [ `Field of fieldinfo | `Container_of_void of 'a ] list

type 'eff t =
  {
    goto_vars   : varinfo H_stmt.t;
    goto_next   : stmt H_stmt.t;
    stmt_vars   : varinfo H_stmt_conds.t;
    offs_of_key : (fieldinfo * typ) offs H_field.t;
    effects     : 'eff H_fundec.t
  }

module Readers (R : Representant) = struct
  type mem = R.t * fieldinfo option

  type readable =
    [ `Global_var of varinfo
    | `Poly_var   of varinfo
    | `Local_var  of varinfo
    | `Global_mem of mem
    | `Poly_mem   of mem
    | `Local_mem  of mem ]

  type writable = [ readable | `Result ]
end

module type Info = sig
  module R : Representant
  module U : Unifiable with module R := R
  module G : Global with module R := R and module U := U
  module E : Effect with module R := R and module U := U and module G := G

  type nonrec 'a offs = 'a offs
  type nonrec t = E.some t

  include module type of Readers (R)

  val create : unit -> t
  val get : t -> Flag.t -> fundec -> E.some
  val flag : Flag.t
  val clear : t -> unit
end

module Make (R : Representant) (U : Unifiable with module R := R) () :
  Info with module R := R and module U := U = struct

  module G = Global (R) (U) ()
  module E = Effect (R) (U) (G)

  type nonrec 'a offs = 'a offs
  type nonrec t = E.some t

  include Readers (R)

  let create () =
    {
      goto_vars = H_stmt.create 128;
      goto_next = H_stmt.create 128;
      stmt_vars = H_stmt_conds.create 32;
      offs_of_key = H_field.create 64;
      effects = H_fundec.create 1024
    }

  let get fi fl f =
    try
      H_fundec.find fi.effects f
    with
    | Not_found ->
      let r = E.create fl f in
      H_fundec.replace fi.effects f r;
      r

  let flag = R.flag

  let clear i = H_fundec.clear i.effects
end
