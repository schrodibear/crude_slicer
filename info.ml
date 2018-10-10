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

open Cil
open Cil_types
open Cil_printer
open Cil_datatype

open Format
open Extlib
open! Common
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
end

module type Writes = sig
  module R : Representant
  module U : Unifiable with module R := R
  module G : Global    with module R := R and module U := U
  module F : Function  with module R := R and module U := U
  type readable =
    [ `Global_var of G.Var.t
    | `Poly_var   of F.Poly.Var.t
    | `Local_var  of F.Local.Var.t
    | `Global_mem of G.Mem.t
    | `Poly_mem   of F.Poly.Mem.t
    | `Local_mem  of F.Local.Mem.t ]

  type t = [ readable  | `Result ]

  include Hashed_ordered_printable with type t := t
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

module type Op = sig
  type unary =
    [ `Cast of ikind
    | `Minus
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

type _ readable = ..

module type Readables = sig
  type r
  type _ readable += W : r readable
end

type 'r readables = (module Readables with type r = 'r)

type (_, _, _) binding = ..

module Symbolic : sig
  module Op : Op
  module Id : Private_index
  type 'r node =
    | Const of Integer.t
    | Read of 'r
    | Nondet of stmt * lval
    | Top
    | Bot
    | Ite of exp * 'r t * 'r t * 'r t
    | Unary of Op.unary * 'r t
    | Binary of Op.binary * 'r t * 'r t
    | Let : ('cr, 'r, 'e) binding * 'e * 'r t -> 'cr node (* Should be handled from the INSIDE! *)
  and 'r t = private
    {
      node : 'r node;
      id   : Id.t
    }
  val mk : 'r node -> 'r t
  module Node : sig
    type he = { f : 'cr 'r 'e . ('cr, 'r, 'e) binding -> 'e -> int }
    val hash : ('r -> int) -> he -> 'r node -> int
    type ee = { f : 'cr 'r1 'e1 'r2 'e2. ('cr, 'r1, 'e1) binding -> 'e1 -> ('cr, 'r2, 'e2) binding -> 'e2 -> bool }
    val equal : ('r -> 'r -> bool) -> ee -> 'r node -> 'r node -> bool
  end
  val hash : 'r t -> int
  val equal : 'r t -> 'r t -> bool
  type pe = { f : 'cr 'r 'e. formatter -> ('cr, 'r, 'e) binding -> 'e -> unit }
  val pp : (formatter -> 'r -> unit) -> pe -> formatter -> 'r t -> unit
end = struct
  module Id = Make_index ()
  module rec Op : Op = Op
  type 'r node =
    | Const of Integer.t
    | Read of 'r
    | Nondet of stmt * lval
    | Top
    | Bot
    | Ite of exp * 'r t * 'r t * 'r t
    | Unary of Op.unary * 'r t
    | Binary of Op.binary * 'r t * 'r t
    | Let : ('cr, 'r, 'e) binding * 'e * 'r t -> 'cr node
  and 'r t =
    {
      node : 'r node;
      id   : Id.t
    }
  module Node = struct
    type he = { f : 'cr 'r 'e . ('cr, 'r, 'e) binding -> 'e -> int }
    let hash hr he =
      function
      | Const c            -> 11 * Integer.hash c + 1
      | Read r             -> 11 * hr r + 2
      | Nondet (s, l)      -> 11 * (257 * Stmt.hash s + Lval.hash l) + 3
      | Top                -> 4
      | Bot                -> 5
      | Ite (c, i, t, e)   -> 11 * Id.(105871 * Exp.hash c + hash i.id + 1351 * hash t.id + 257 * hash e.id) + 6
      | Unary (u, a)       -> 11 * (257 * Hashtbl.hash u + Id.hash a.id) + 7
      | Binary (b, v1, v2) -> 11 * Id.(1351 * Hashtbl.hash b + 257 * hash v1.id + hash v2.id) + 8
      | Let (b, e, v)      -> 11 * (257 * he.f b e + Id.hash v.id) + 9
    type ee = { f : 'cr 'r1 'e1 'r2 'e2. ('cr, 'r1, 'e1) binding -> 'e1 -> ('cr, 'r2, 'e2) binding -> 'e2 -> bool }
    let equal er ee n1 n2 =
      match n1, n2 with
      | Const c1,              Const c2             -> Integer.equal c1 c2
      | Read r1,               Read r2              -> er r1 r2
      | Nondet (s1, l1),       Nondet (s2, l2)      -> Stmt.equal s1 s2 && Lval.equal l1 l2
      | Top,                   Top
      | Bot,                   Bot                  -> true
      | Ite (c1, i1, t1, e1),  Ite (c2, i2, t2, e2) -> Exp.equal c1 c2 &&
                                                       Id.(equal i1.id i2.id &&
                                                           equal t1.id t2.id &&
                                                           equal e1.id e2.id)
      | Unary (u1, a1),        Unary (u2, a2)       -> u1 = u2 && Id.equal a1.id a2.id
      | Binary (b1, v11, v12), Binary(b2, v21, v22) -> b1 = b2 && Id.(equal v11.id v21.id && equal v12.id v22.id)
      | Let (b1, e1, v1),      Let (b2, e2, v2)     -> ee.f b1 e1 b2 e2 && Id.equal v1.id v2.id
      | (Const _
        | Read _
        | Nondet _
        | Top
        | Bot
        | Ite _
        | Unary _
        | Binary _
        | Let _),              _                    -> false
  end

  let id = ref ~-1

  let mk node = incr id; { node; id = Id.mk !id }

  let hash { id; _ } = Id.coerce id

  let equal u1 u2 = Id.equal u1.id u2.id

  type pe = { f : 'cr 'r 'e. formatter -> ('cr, 'r, 'e) binding -> 'e -> unit }
  let rec pp ppr ppe fmt u =
    let pp = pp ppr ppe in
    let pr f = Format.fprintf fmt f in
    match u.node with
    | Const i            -> pr "%s" (Integer.to_string i)
    | Read r             -> pr "%a" ppr r
    | Nondet (s, l)      -> pr "*_(%d,%a)" s.sid Lval.pretty l
    | Top                -> pr "T"
    | Bot                -> pr "_|_"
    | Ite (c, i, t, e)   -> pr "(@[%a (%d)@ ?@ %a@ :@ %a@])" pp i c.eid pp t pp e
    | Unary (u, a)       ->(pr "(@[";
                            begin match u with
                            | `Cast i -> pr "(%a)" Cil_printer.pp_ikind i
                            | `Minus  -> pr "-"
                            | `Neg    -> pr "!"
                            end;
                            pr " %a@])" pp a)
    | Binary (b, a1, a2) ->(pr "([@%a@ " pp a1;
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
    | Let (b, e, _)      -> ppe.f fmt b e
end

module type Summary = sig
  module R : Representant
  module U : Unifiable with module R := R
  module G : Global with module R := R and module U := U
  module F : Function with module R := R and module U := U
  module W : Writes with module R := R and module U := U and module G := G and module F := F

  module Symbolic : sig
    open Symbolic

    type 'r env =
      {
        poly_vars   : 'r t F.Poly.Var.M.t;
        poly_mems   : 'r t F.Poly.Mem.M.t;
        global_vars : 'r t G.Var.M.t;
        global_mems : 'r t G.Mem.M.t
      }

    type nonrec t = W.readable t

    include Hashed_printable with type t := t
    module H : Hashtbl.S with type key := t

    module Readable : Readables with type r = W.readable

    val readable : W.readable readables

    type (_, _, _) binding += W : 'r readables -> ('cr, 'r, 'cr env) binding

    val const : Integer.t -> t
    val read : W.readable -> t
    val nondet : stmt -> lval -> t
    val top : t
    val bot : t
    val ite : exp -> t -> t -> t -> t
    val unary : Op.unary -> t -> t
    val binary : Op.binary -> t -> t -> t
    val prj : 'r readables -> 'r env -> t -> 'r Symbolic.t

    val strengthen : stmt -> lval -> t -> t
    val covers : t -> t -> bool
    val merge : t -> t -> t
  end

  type u =
    {
      pre        : Symbolic.t;
      post       : W.readable Symbolic.env;
      local_vars : Symbolic.t F.Local.Var.M.t;
      local_mems : Symbolic.t F.Local.Mem.M.t
    }

  type t
  val eq : (t, u) eq
  val empty : t
  val strengthen : stmt -> (W.readable -> lval) -> t -> t
  val covers : t -> t -> bool
  val merge : t -> t -> t
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
end

module Writes
    (R : Representant)
    (U : Unifiable with module R := R)
    (G : Global with module R := R and module U := U)
    (F : Function with module R := R and module U := U) :
  Writes with module R := R and module U := U and module G := G and module F := F = struct

  type readable =
    [ `Global_var of G.Var.t
    | `Poly_var   of F.Poly.Var.t
    | `Local_var  of F.Local.Var.t
    | `Global_mem of G.Mem.t
    | `Poly_mem   of F.Poly.Mem.t
    | `Local_mem  of F.Local.Mem.t ]

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
    | `Result,        _               -> 1

  let equal w1 w2 =
    match[@warning "-4"] w1, w2 with
    | `Global_var v1, `Global_var v2 -> G.Var.equal       v1 v2
    | `Poly_var v1,   `Poly_var v2   -> F.Poly.Var.equal  v1 v2
    | `Local_var v1,  `Local_var v2  -> F.Local.Var.equal v1 v2
    | `Global_mem m1, `Global_mem m2 -> G.Mem.equal       m1 m2
    | `Poly_mem m1,   `Poly_mem m2   -> F.Poly.Mem.equal  m1 m2
    | `Local_mem m1,  `Local_mem m2  -> F.Local.Mem.equal m1 m2
    | `Result,        `Result        -> true
    | _                              -> false

  let hash =
    function
    | `Global_var v -> 7 * G.Var.hash v
    | `Poly_var v   -> 7 * F.Poly.Var.hash v  + 1
    | `Local_var v  -> 7 * F.Local.Var.hash v + 2
    | `Global_mem m -> 7 * G.Mem.hash m       + 3
    | `Poly_mem m   -> 7 * F.Poly.Mem.hash m  + 4
    | `Local_mem m  -> 7 * F.Local.Mem.hash m + 5
    | `Result       -> 6

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

    type 'r env =
      {
        poly_vars   : 'r t F.Poly.Var.M.t;
        poly_mems   : 'r t F.Poly.Mem.M.t;
        global_vars : 'r t G.Var.M.t;
        global_mems : 'r t G.Mem.M.t
      }

    type nonrec t = W.readable t

    module Readable = struct
      type r = W.readable
      type _ readable += W : r readable
    end

    let readable : W.readable readables = (module Readable)

    type (_, _, _) binding += W : 'r readables -> ('cr, 'r, 'cr env) binding

    module Bare = struct
      open Node
      type t = E : 'r readables * 'r node -> t
      let hash (type r) (r : r readable) (n : r node) =
        hash
          (match r with
          | Readable.W -> (W.hash :> W.readable -> _)
          | _          -> fun _ -> Console.fatal "Symbolic.Bare.hash: unexpected witness" : r -> _)
          { f = fun (type cr r e) (w : (cr, r, e) binding) (e : e) ->
              match w with
              | W _ ->(let fold hash v u acc = 15487399 * acc + 105871 * hash v + Id.hash u.id in
                       15487399 * F.Poly.Var.M.fold (fold F.Poly.Var.hash) e.poly_vars 0 +
                       105871 * F.Poly.Mem.M.fold (fold F.Poly.Mem.hash) e.poly_mems 0 +
                       1351 * G.Var.M.fold (fold G.Var.hash) e.global_vars 0 +
                       G.Mem.M.fold (fold G.Mem.hash) e.global_mems 0)
              | _   -> Console.fatal "Symbolic.Bare.hash: unexpected witness" }
          n
      let hash (E ((module R), n)) = hash R.W n
      let equal (type r) (r1 : r readable) (n1 : r node) (r2 : r readable) (n2 : r node) =
        equal
          (match r1, r2 with
          | Readable.(W, W) -> (W.equal :> W.readable -> W.readable -> _)
          | _               -> fun _ -> Console.fatal "Symbolic.Bare.equal: unexpected witness" : r -> r -> _ )
          { f = fun (type cr r1 e1 r2 e2)
              (w1 : (cr, r1, e1) binding) (e1 : e1) (w2 : (cr, r2, e2) binding) (e2 : e2) ->
              match w1, w2 with
              | W _, W _ ->(let by_id v1 v2 = Id.equal v1.id v2.id in
                            F.Poly.Var.M.equal by_id e1.poly_vars e2.poly_vars &&
                            F.Poly.Mem.M.equal by_id e1.poly_mems e2.poly_mems &&
                            G.Var.M.equal by_id e1.global_vars e2.global_vars &&
                            G.Mem.M.equal by_id e1.global_mems e2.global_mems)
              | _        -> Console.fatal "Symbolic.Bare.equal: unexpected witness" }
          n1 n2
      let equal (E ((module R1), n1)) (E ((module R2), n2)) =
        match R1.W with
        | R2.W -> equal R1.W n1 R2.W n2
        | _    -> false
    end

    type mk = { f : 'r. 'r readables -> 'r node -> 'r Symbolic.t }
    let mk =
      let module Ex = struct type ex = E : 'r readables * 'r Symbolic.t -> ex end in
      let module H = Hashtbl.Make (Bare) in
      let h = H.create 128 in
      { f = fun (type r) ((module R) as r : r readables) (n : r node) : r Symbolic.t ->
          let Ex.E ((module R1), r) =
            let key = Bare.E (r, n) in try H.find h key with Not_found -> let r = Ex.E (r, mk n) in H.add h key r; r
          in
          match R1.W with
          | R.W -> r
          | _   -> Console.fatal "Symbolic.mk: got unexpected symbolic value after hashconsing" }
    let mk' = mk.f readable

    let const i = mk' @@ Const i
    let read r = mk' @@ Read r
    let nondet s l = mk' @@ Nondet (s, l)
    let top = mk' Top
    let bot = mk' Bot
    let ite c i t e = mk' @@ Ite (c, i, t, e)
    let unary u a = mk' @@ Unary (u, a)
    let binary b a1 a2 = mk' @@ Binary (b, a1, a2)
    let prj r e v = mk.f r @@ Let (W readable, e, v)

    let hash = hash
    let equal = equal

    module H = Hashtbl.Make (struct type nonrec t = t let hash = hash let equal = equal end)

    let pp =
      let pp_id fmt v = fprintf fmt "%a" Id.pp v.id in
      pp
        (W.pp :> _ -> W.readable -> _)
        { f = fun (type cr r e) fmt (w : (cr, r, e) binding) (e : e) ->
            match w with
            | W _ -> Pretty_utils
                     .(fprintf fmt "(@[[{%a}@ {%a}@ {%a}@ {%a}]@ @] ...)"
                         (pp_iter2 ~sep:",@ " ~between:" -> " F.Poly.Var.M.iter F.Poly.Var.pp pp_id) e.poly_vars
                         (pp_iter2 ~sep:",@ " ~between:" -> " F.Poly.Mem.M.iter F.Poly.Mem.pp pp_id) e.poly_mems
                         (pp_iter2 ~sep:",@ " ~between:" -> " G.Var.M.iter G.Var.pp pp_id) e.global_vars
                         (pp_iter2 ~sep:",@ " ~between:" -> " G.Mem.M.iter G.Mem.pp pp_id) e.global_mems)
            |_    -> Console.fatal "Symbolic.pp: unexpected witness" }

    let rec strengthen s l v =
      match v.node with
      | Const _
      | Read _
      | Nondet _
      | Bot
      | Unary _
      | Binary _
      | Ite _
      | Let _     -> v
      | Top       -> nondet s l
    let covers v1 v2 =
      match v1.node, v2.node with
      | Top,       _
      | _,         Bot   -> true
      | n1,        n2
        when equal v1 v2 -> true
      | (Const _
        | Read _
        | Nondet _
        | Bot
        | Ite _
        | Unary _
        | Binary _
        | Let _),  _     -> false
    let merge v1 v2 =
      match v1.node, v2.node with
      | Top,  _
      | _,                    Top                  -> top
      | Bot,                  _                    -> v1
      | _,                    Bot                  -> v2
      | Ite (c1, i1, t1, e1), Ite (c2, i2, t2, e2)
        when Exp.equal c1 c2
          && equal i1 i2
          && (t1.node = Bot || t2.node = Bot)
          && (e1.node = Bot || e2.node = Bot)      -> ite
                                                        c1
                                                        i1
                                                        (if t2.node = Bot then t1 else t2)
                                                        (if e2.node = Bot then e1 else e2)
      | n1,                   n2
        when equal v1 v2                           -> v1
      | _,    _                                    -> top
  end

  type u =
    {
      pre        : Symbolic.t;
      post       : W.readable Symbolic.env;
      local_vars : Symbolic.t F.Local.Var.M.t;
      local_mems : Symbolic.t F.Local.Mem.M.t
    }

  type t = u
  let eq = Refl
  let empty =
    Symbolic.
      {
        pre = top;
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
    let strengthen map wr = map @@ Symbolic.strengthen stmt % f % wr in
    {
      pre = s.pre;
      post =
        {
          poly_vars   = strengthen F.Poly.Var.M.mapi  (fun v -> `Poly_var v)   s.post.poly_vars;
          poly_mems   = strengthen F.Poly.Mem.M.mapi  (fun m -> `Poly_mem m)   s.post.poly_mems;
          global_vars = strengthen G.Var.M.mapi       (fun v -> `Global_var v) s.post.global_vars;
          global_mems = strengthen G.Mem.M.mapi       (fun m -> `Global_mem m) s.post.global_mems
        };
      local_vars      = strengthen F.Local.Var.M.mapi (fun v -> `Local_var v)  s.local_vars;
      local_mems      = strengthen F.Local.Mem.M.mapi (fun m -> `Local_mem m)  s.local_mems
    }
  let covers s1 s2 =
    Symbolic.covers s2.pre s1.pre &&
    let covers find m k v = try Symbolic.covers (find k m) v with Not_found -> false in
    F.Poly.Var.M.(for_all  (covers find s1.post.poly_vars)   s2.post.poly_vars) &&
    F.Poly.Mem.M.(for_all  (covers find s1.post.poly_mems)   s2.post.poly_mems) &&
    G.Var.M.(for_all       (covers find s1.post.global_vars) s2.post.global_vars) &&
    G.Mem.M.(for_all       (covers find s1.post.global_mems) s2.post.global_mems) &&
    F.Local.Var.M.(for_all (covers find s1.local_vars)       s2.local_vars) &&
    F.Local.Mem.M.(for_all (covers find s1.local_mems)       s2.local_mems)
  let merge s1 s2 =
    let merge _ = opt_fold @@ some %% swap (opt_fold Symbolic.merge) in
    {
      pre = Symbolic.merge s1.pre s2.pre;
      post =
        {
          poly_vars   = F.Poly.Var.M.merge  merge s1.post.poly_vars   s2.post.poly_vars;
          poly_mems   = F.Poly.Mem.M.merge  merge s1.post.poly_mems   s2.post.poly_mems;
          global_vars = G.Var.M.merge       merge s1.post.global_vars s2.post.global_vars;
          global_mems = G.Mem.M.merge       merge s1.post.global_mems s2.post.global_mems;
        };
      local_vars      = F.Local.Var.M.merge merge s1.local_vars       s2.local_vars;
      local_mems      = F.Local.Mem.M.merge merge s1.local_mems       s2.local_mems
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
