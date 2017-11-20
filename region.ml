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

[@@@warning "-4-6-48"]

open Cil
open Cil_types
open Cil_printer
open Cil_datatype

open Extlib
open! Common

module Representant = struct
  module Kind = struct
    type t = [ `Global | `Poly of string  | `Local of string | `Dummy ]

    let equal k1 k2 =
      match k1, k2 with
      | `Global,   `Global      -> true
      | `Poly f1,  `Poly f2
      | `Local f1, `Local f2
        when String.equal f1 f2 -> true
      | `Dummy,    `Dummy       -> true
      | (`Global
        | `Poly _
        | `Local _
        | `Dummy), (`Global
                   | `Poly _
                   | `Local _
                   | `Dummy)    -> false

    let hash =
      let open! Datatype in
      function
      | `Global  -> 1
      | `Poly f  -> 5 * String.hash f + 2
      | `Local f -> 5 * String.hash f + 3
      | `Dummy   -> 4

    let choose k1 k2 =
      match k1, k2 with
      | `Global,  `Global                        -> `Any
      | `Global,  (`Poly _ | `Local _ | `Dummy)  -> `First
      | `Poly _,  `Global                        -> `Second
      | `Poly _,  `Poly _                        -> `Any
      | `Poly _,  (`Local _ | `Dummy)            -> `First
      | `Local _, (`Global | `Poly _)            -> `Second
      | `Local _, `Local _                       -> `Any
      | `Local _, `Dummy                         -> `First
      | `Dummy,   (`Global | `Poly _ | `Local _) -> `Second
      | `Dummy,   `Dummy                         -> `Any

    let pp fmttr =
      Format.fprintf fmttr %
      function
      | `Global  -> "^"
      | `Poly _  -> "'"
      | `Local _ -> "~"
      | `Dummy   -> "?"
  end

  type 'a region =
    {
      id   : int;
      name : string Lazy.t;
      exp  : 'a Lazy.t option;
      typ  : typ;

      mutable kind : Kind.t
    }

  module type Exp = sig
    type t = private exp
    val loc : Location.t
    val addr : varinfo -> exp
    val var : varinfo -> exp
    val ret : exp
    val is_ret : exp -> bool
    val arrow : t -> fieldinfo -> t
    val deref : t -> t
    val dot : t -> fieldinfo -> t
    val container : t -> fieldinfo -> t
    val dot_void : t -> t
    val container_of_void : t -> typ -> t
  end

  module Exp : sig
    include Exp
    val mk : typ -> exp -> t
    val arrow_opt : t region -> fieldinfo -> t Lazy.t option
    val deref_opt : t region -> t Lazy.t option
    val dot_opt : t region -> fieldinfo -> t Lazy.t option
    val container_opt : t region -> fieldinfo -> t Lazy.t option
    val dot_void_opt : t region -> t Lazy.t option
    val container_of_void_opt : t region -> typ -> t Lazy.t option
  end = struct
    type t = exp

    let loc = Location.unknown

    let mk ty e =
      let newt = TPtr (Ty.normalize ty, []) in
      mkCast ~force:false ~overflow:Check ~e ~newt

    let norm e =
      let ty = typeOf e in
      let e =
        match unrollType ty, e.enode with
        | TPtr _, _       -> e
        | _,      Lval lv -> mkAddrOrStartOf ~loc:e.eloc lv
        | _               -> Console.fatal "Region.Exp.norm: neither pointer nor lval: %a" pp_exp e
      in
      let newt = Ty.normalize ty in
      if need_cast ty newt
      then mkCast ~force:false ~overflow:Check ~e ~newt
      else e

    let addr = norm % mkAddrOrStartOf ~loc % var
    let var = norm % evar ~loc
    let ret = new_exp ~loc (Const (CStr "!R!"))
    let is_ret = Exp.equal ret

    let arrow addr fi = norm @@ new_exp ~loc @@ Lval (mkMem ~addr ~off:(Field (fi, NoOffset)))
    let deref addr    = norm @@ new_exp ~loc @@ Lval (mkMem ~addr ~off:NoOffset)
    let dot   addr fi = norm @@ mkAddrOrStartOf ~loc @@ mkMem ~addr ~off:(Field (fi, NoOffset))
    let container e fi = Exp.container_of ~loc [`Field fi] e
    let dot_void e             = mkCast ~force:true ~overflow:Check ~e ~newt:voidPtrType
    let container_of_void e ty = mkCast ~force:true ~overflow:Check ~e ~newt:(TPtr (ty, []))

    let opt f r = opt_map (fun e -> lazy (f !!e)) r.exp
    let opt2 f r fi = opt_map (fun e -> lazy (f !!e fi)) r.exp

    let    arrow_opt,  deref_opt,      dot_opt,      container_opt,     dot_void_opt,      container_of_void_opt =
      opt2 arrow,  opt deref,     opt2 dot,     opt2 container,     opt dot_void,     opt2 container_of_void
  end

  type t = Exp.t region

  let name r = !! (r.name)
  let typ r = r.typ
  let exp r = r.exp
  let exp' r = opt_map (!!) r.exp
  let kind r = r.kind

  let equal r1 r2 = r1.id = r2.id
  let hash r = r.id
  let compare r1 r2 = compare r1.id r2.id
  let choose r1 r2 = Kind.choose r1.kind r2.kind

  module H = Hashtbl.Make (struct type nonrec t = t let equal, hash = equal, hash end)

  let id = ref ~-1

  let mk ~name ~e:exp ~typ ~kind =
    let typ = Ty.normalize typ in
    incr id;
    { id = !id; name; exp; typ; kind }

  let global name e typ = mk ~name:(lazy name) ~e:(opt_map (Lazy.from_val % Exp.mk typ) e) ~typ ~kind:`Global
  let poly fname name e typ =
    mk ~name:(lazy (fname ^ "::" ^ name)) ~e:(Some (lazy (Exp.mk typ e))) ~typ ~kind:(`Poly fname)
  let local fname name typ = mk ~name:(lazy (fname ^ ":::" ^ name)) ~e:None ~typ ~kind:(`Local fname)

  let demote r = r.kind <- `Dummy

  let check_field f r fi =
    match unrollType r.typ with
    | TComp (ci, _, _)
      when ci.cstruct && Compinfo.equal ci fi.fcomp -> ()
    | ty                                            -> Console.fatal
                                                         "%s: not a struct with field %s.%s: %a"
                                                         f fi.fcomp.cname fi.fname pp_typ ty

  let arrow r fi =
    check_field "Representant.arrow" r fi;
    if not (isPointerType fi.ftype) then
      Console.fatal "Representant.arrow: not a pointer field: %s.%s : %a" fi.fname fi.fcomp.cname pp_typ fi.ftype;
    mk
      ~name:(lazy (name r ^ "->" ^ fi.fname))
      ~e:(Exp.arrow_opt r fi)
      ~typ:(Ast_info.pointed_type fi.ftype)
      ~kind:r.kind

  let deref r =
    if not (isPointerType r.typ) then
      Console.fatal "Representant.deref: not a pointer region: %s : %a" (name r) pp_typ r.typ;
    mk ~name:(lazy ("*(" ^ name r ^ ")")) ~e:(Exp.deref_opt r) ~typ:(Ast_info.pointed_type r.typ) ~kind:r.kind

  let check_detached f fi =
    if not (isStructOrUnionType fi.ftype || isArrayType fi.ftype || fi.faddrof) then
      Console.fatal
        "%s: not a struct/union, array or addressed field: %s.%s : %a (&: %B)"
        f fi.fcomp.cname fi.fname pp_typ fi.ftype fi.faddrof

  let dot r fi =
    check_field "Representant.dot" r fi;
    check_detached "Representant.dot" fi;
    mk ~name:(lazy (name r ^ "." ^ fi.fname)) ~e:(Exp.dot_opt r fi) ~typ:(Ty.unbracket fi.ftype) ~kind:r.kind

  let container r fi =
    check_detached "Representant.container" fi;
    if not Ty.(compatible (unbracket fi.ftype) r.typ) then
      Console.fatal
        "Representant.container: illegal use of `container_of': %s.%s : %a vs. %s : %a"
        fi.fcomp.cname fi.fname pp_typ fi.ftype (name r) pp_typ r.typ;
    if not fi.fcomp.cstruct then
      Console.fatal "Representant.container: container should be a structure: %s" fi.fcomp.cname;
    mk
      ~name:(lazy ("(" ^ name r ^ ", " ^ fi.fcomp.cname ^ "." ^ fi.fname ^ ")"))
      ~e:(Exp.container_opt r fi)
      ~typ:(TComp (fi.fcomp, empty_size_cache (), []))
      ~kind:r.kind

  let dot_void r = mk ~name:(lazy (name r ^ ".void")) ~e:(Exp.dot_void_opt r) ~typ:voidType ~kind:r.kind

  let container_of_void r typ =
    let name' =
      match unrollType typ with
      | TComp (ci, _, _) when ci.cstruct -> ci.cname
      | TComp _                          -> Console.fatal
                                              "Representant: container_of_void: shouldn't be union: %a"
                                              pp_typ typ
      | TVoid _                          -> Console.fatal
                                              "Representant: container_of_void: shouldn't be void: %a"
                                              pp_typ typ
      | ty                               -> Format.asprintf "`%a'" pp_typ ty
    in
    begin match unrollType r.typ with
    | TVoid _                              -> ()
    | TComp (ci, _, _) when not ci.cstruct -> ()
    | ty                                   -> Console.fatal
                                                "Representant.container_of_void: can only take (_, %s.void) \
                                                 from void or union region: %s : %a"
                                                name' (name r) pp_typ ty
    end;
    mk ~name:(lazy ("(" ^ name r ^ ", " ^ name' ^ ".void)")) ~e:(Exp.container_of_void_opt r typ) ~typ ~kind:r.kind

  let pp fmttr r = Format.fprintf fmttr "%a%s" Kind.pp r.kind (name r)
end

module type Representant = sig
  module Kind : sig type t end
  type t
  val choose : t -> t -> [> `First | `Second | `Any ]

  module Exp : sig
    type t
  end

  val name : t -> string
  val exp : t -> Exp.t Lazy.t option
  val report : t -> is_repr_of:t -> unit

  val flag : Flag.t

  include Hashed_printable with type t := t
  module H : Hashtbl.S with type key := t
end

module type Unifiable = sig
  type t
  type repr
  val of_repr : repr -> t
  val unify : t -> t -> unit
  val repr : t -> repr

  val pp : Format.formatter -> t -> unit

  val clear : unit -> unit
end

module Make_unifiable (R : Representant) () : Unifiable with type repr = R.t = struct
  type t = R.t
  type repr = R.t
  let of_repr = id

  module H = R.H

  let reprs = H.create 8192
  let ranks = H.create 8192

  let rec repr r =
    match repr (H.find reprs r) with
    | r'                  -> H.replace reprs r r'; r'
    | exception Not_found -> r

  let rank r = try H.find ranks r with Not_found -> 0

  let unify r1 r2 =
    let r1, r2 = repr r1, repr r2 in
    if R.equal r1 r2 then ()
    else
      let set r1 ~as_repr_of:r2 =
        let k1, k2 = rank r1, rank r2 in
        H.replace reprs r2 r1;
        R.report r1 ~is_repr_of:r2;
        if k1 <= k2 then H.replace ranks r1 (k2 + 1)
      in
      let choice =
        match R.choose r1 r2 with
        | `First | `Second as c -> c
        | `Any                  ->
          let k1, k2 = rank r1, rank r2 in
          if      k1 > k2                                            then `First
          else if k2 > k1                                            then `Second
          else if has_some (R.exp r1)                                then `First
          else                                                            `Second
      in
      match choice with
      | `First  -> set r1 ~as_repr_of:r2
      | `Second -> set r2 ~as_repr_of:r1

  let pp fmt = Format.fprintf fmt "%a" R.pp % repr

  let clear () =
    H.clear reprs;
    H.clear ranks
end

module type Hashmap = sig
  module R : Representant
  module U : Unifiable with type repr = R.t
  type t
  val create : unit -> t
  val add : U.t -> U.t -> t -> unit
  val add' : t -> U.t -> U.t -> unit
  val mem : U.t -> t -> bool
  val find : U.t -> t -> U.t
  val find_or_call : create:(R.t -> R.t) -> call:(U.t -> U.t -> unit) -> t -> U.t -> [> `Old | `New] * U.t
  val iter : (U.t -> unit) -> U.t -> t -> unit
  val clear : t -> unit
end

module Make_hashmap (R : Representant) (U : Unifiable with type repr = R.t) :
  Hashmap with module R := R and module U := U = struct

  module H = R.H
  type t = U.t H.t
  let create () = H.create 8192
  let add u v h = H.replace h (U.repr u) v
  let add' h u v = add u v h
  let mem u h = H.mem h (U.repr u)
  let find u h = H.find h (U.repr u)
  let find_or_call ~create ~call h u =
    try
      `Old, find u h
    with
    | Not_found ->
      let u' = U.of_repr @@ create (U.repr u) in
      add u u' h;
      call u' u;
      `New, u'
  let iter f u h = try f (H.find h (U.repr u)) with Not_found -> ()
  let clear h = H.clear h
end

module type Pair_hashmap = sig
  module R : Representant
  module U : Unifiable with type repr = R.t
  module K : Hashtbl.HashedType
  type t
  val create : unit -> t
  val add : U.t -> K.t -> U.t -> t -> unit
  val add' : t -> U.t -> K.t -> U.t -> unit
  val find : U.t -> K.t -> t -> U.t
  val find_or_call :
    create:(R.t -> K.t -> R.t) -> call:(U.t -> K.t -> U.t -> unit) -> t -> U.t -> K.t -> [> `Old | `New] * U.t
  val iter : (K.t -> U.t -> unit) -> U.t -> t -> unit
  val clear : t -> unit
end

module Make_pair_hashmap (R : Representant) (U : Unifiable with type repr = R.t) (K : Hashtbl.HashedType) :
  Pair_hashmap with module R := R and module U := U and module K := K = struct

  module H =
    Hashtbl.Make
      (struct
        type t = R.t * K.t
        let equal (r1, k1) (r2, k2) = R.equal r1 r2 && K.equal k1 k2
        let hash (r, k) = 199 * R.hash r + K.hash k
      end)
  module H_k = R.H

  type t = U.t H.t * K.t H_k.t
  let create () = H.create 8192, H_k.create 1024
  let add u k v (h, ks) =
    let r = U.repr u in
    H.replace h (r, k) v;
    if not (List.exists (K.equal k) @@ H_k.find_all ks r) then H_k.add ks r k
  let add' h u k v = add u k v h
  let find u k (h, _) = H.find h (U.repr u, k)
  let find_or_call ~create ~call h u k =
    try
      `Old, find u k h
    with
    | Not_found ->
      let u' = U.of_repr @@ create (U.repr u) k in
      add u k u' h;
      call u' k u;
      `New, u'
  let iter f u (h, ks) =
    let r = U.repr u in
    List.iter (fun k -> f k @@ H.find h (r, k)) (H_k.find_all ks r)

  let clear (h, ks) = H.clear h; H_k.clear ks
end

module type Representant_intf = sig
  module Kind : sig
    type t = [ `Global | `Poly of string  | `Local of string | `Dummy ]
    val equal : [< t] -> [< t ] -> bool
    val hash : [< t] -> int
    val pp : Format.formatter -> [< t ] -> unit
  end

  type 'a region = private
    {
      id   : int;
      name : string Lazy.t;
      exp  : 'a Lazy.t option;
      typ  : typ;
      mutable kind : Kind.t
    }

  module Exp : Representant.Exp

  type t = Exp.t region

  val name : t -> string
  val exp : t -> Exp.t Lazy.t option
  val exp' : t -> Exp.t option
  val typ : t -> typ
  val kind : t -> Kind.t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
  val flag : Flag.t
  val all_void_xs : unit -> (int * t list) list
  val pp : Format.formatter -> t -> unit
end

module type Representant_full = sig
  include Representant_intf with type 'a region = 'a Representant.region
  include Representant with module Kind := Kind and module Exp := Exp and type t := t
  val global : string -> exp option -> typ -> t
  val poly : string -> string -> exp -> typ -> t
  val local : string -> string -> typ -> t
  val demote : t -> unit
  val arrow : t -> fieldinfo -> t
  val deref : t -> t
  val dot : t -> fieldinfo -> t
  val container : t -> fieldinfo -> t
  val dot_void : t -> t
  val container_of_void : t -> typ -> t
end

module type Separation_options = sig
  val region_length : int
  val region_depth : int
  val region_count : int

  val check_locality : bool
end

module Separation : functor (_ : Separation_options) () -> sig
  module R : Representant_full
  module U : Unifiable with type repr = R.t
  module H' : Hashmap with module R := R and module U := U

  val arrow : U.t -> fieldinfo -> U.t
  val deref : U.t -> U.t
  val dot : U.t -> fieldinfo -> U.t
  val dot_void : U.t -> U.t
  val container : U.t -> fieldinfo -> U.t
  val container_of_void : U.t -> typ -> U.t
  val arrows : (fieldinfo -> U.t -> unit) -> U.t -> unit
  val derefs : (U.t -> unit) -> U.t -> unit
  val dots : (fieldinfo -> U.t -> unit) -> U.t -> unit
  val dot_voids : (U.t -> unit) -> U.t -> unit
  val containers : (fieldinfo -> U.t -> unit) -> U.t -> unit
  val containers_of_void : (typ -> U.t -> unit) -> U.t -> unit

  module H_map : sig
    type t
    val find : U.t -> t -> U.t
    val iter : (U.t -> U.t -> unit) -> t -> unit
    val create : unit -> t
  end

  val unify : U.t -> U.t -> unit
  val reflect : map:H_map.t -> U.t -> on:U.t -> unit
  val constrain : map:H_map.t -> by:U.t list -> U.t list -> unit

  val widen : U.t list -> unit

  val switch : string option -> unit
  val assert_stratification : U.t -> unit

  val clear : unit -> unit
end = functor (O : Separation_options) () -> struct
  module R = struct
    include Representant

    let flag = Flag.create "convergence"

    let h_void_xs = H.create 2048

    let mk r =
      let typ = Ty.normalize r.typ in
      if r.kind <> `Dummy then begin
        Flag.report flag;
        let ty, n = Ty.deref typ in
        if isVoidType ty then H.replace h_void_xs r n
      end;
      r

    let report _r1 ~is_repr_of:r2 =
      if isVoidType @@ fst @@ Ty.deref r2.typ then H.remove h_void_xs r2;
      if r2.kind <> `Dummy then Flag.report flag

    let all_void_xs () =
      H.fold
        (fun r n ->
           let rec insert r n l =
             let open List in
             function
             | []                           -> rev_append l [n, [r]]
             | (n', rs) :: es   when n' = n -> rev_append l @@ (n', r :: rs) :: es
             | n', _ as e :: es when n' < n -> insert r n (e :: l) es
             | _ :: _ as es                 -> rev_append l @@ (n, [r]) :: es
           in
           insert r n [])
        h_void_xs
        []

    let choose r1 r2 =
      begin
        if not O.check_locality
        then
          ()
        else
          match r1.kind, r2.kind with
          | (`Poly f1
            | `Local f1),  (`Poly f2
                           | `Local f2)
            when not (String.equal f1 f2) -> Console.fatal
                                               "Representant.Kind.choose: broken invariant: \
                                                should not try unifying regions from diff. functions: %s and %s"
                                               f1 f2
          | (`Global
            | `Poly _
            | `Local _
            | `Dummy),     (`Global
                           | `Poly _
                           | `Local _
                           | `Dummy)      -> ()
      end;
      choose r1 r2

    let      global,         poly,        local =
      mk %%% global, mk %%%% poly, mk %%% local
    let     arrow,      deref,       dot,       container,      dot_void,       container_of_void =
      mk %% arrow, mk % deref, mk %% dot, mk %% container, mk % dot_void, mk %% container_of_void
  end

  let current = ref None

  let switch fo = current := fo

  let check_region r =
    if not O.check_locality
    then
      Ok ()
    else
      match r.R.kind with
      | `Local f | `Poly f
        when
          may_map ~dft:false
            (String.equal f) !current -> Ok ()
      | `Local f | `Poly f as k       -> Error (k, f)
      | `Global | `Dummy              -> Ok ()

  module U = struct
    include Make_unifiable (R) ()

    let unify =
      let check ~intruder:u' u =
        let r = repr u in
        if not (R.equal r @@ repr u') then
          match check_region r with
          | Ok    ()     -> ()
          | Error (k, f) -> Console.fatal "Separation.unify: locality violation: \
                                           an outer region %a leaked into a \
                                           `%a' region %a of function %s"
                              R.pp (repr u') R.Kind.pp k R.pp r f
      in
      fun u1 u2 ->
        if O.check_locality then begin
          check ~intruder:u1 u2;
          check ~intruder:u2 u1
        end;
        unify u1 u2
  end

  module H_f = Make_pair_hashmap (R) (U) (Fieldinfo)
  module H_t = Make_pair_hashmap (R) (U) (Typ)
  module H'  = Make_hashmap (R) (U)

  let h_arrow = H_f.create ()
  let h_deref = H'.create ()
  let h_dot = H_f.create ()
  let h_dot_void = H'.create ()
  let h_container = H_f.create ()
  let h_container_of_void = H_t.create ()

  let arrow = H_f.find_or_call ~create:R.arrow ~call:(fun _ _ _ -> ()) h_arrow
  let deref = H'.find_or_call ~create:R.deref ~call:(fun _ _ -> ()) h_deref
  let dot = H_f.find_or_call ~create:R.dot ~call:(H_f.add' h_container) h_dot
  let dot_void =
    H'.find_or_call
      ~create:R.dot_void
      ~call:(fun u' u -> H_t.add u' (U.repr u).R.typ u h_container_of_void)
      h_dot_void
  let container = H_f.find_or_call ~create:R.container ~call:(H_f.add' h_dot) h_container
  let container_of_void u ty =
    let ty = Ty.normalize ty in
    if isVoidType ty then
      `Old, u
    else
      H_t.find_or_call ~create:R.container_of_void ~call:(fun u' _ u -> H'.add u' u h_dot_void) h_container_of_void u ty

  let check2 f u k =
    match f u k with
    | `Old, _ as r                    -> r
    | `New, u as r                    ->
      match check_region (U.repr u) with
      | Ok    ()                      -> r
      | Error (k, f)                  -> Console.fatal "Separation.check: locality violation: \
                                                        a `%a' region %a was created in function %s"
                                           R.Kind.pp k R.pp (U.repr u) f

  let check1 f u = check2 (const' f) u ()

  let arrow,        deref,        dot,        container,        dot_void,        container_of_void =
    check2 arrow, check1 deref, check2 dot, check2 container, check1 dot_void, check2 container_of_void

  let arrows f u = H_f.iter f u h_arrow
  let derefs f u = H'.iter f u h_deref
  let dots f u = H_f.iter f u h_dot
  let dot_voids f u = H'.iter f u h_dot_void
  let containers f u = H_f.iter f u h_container
  let containers_of_void f u = H_t.iter f u h_container_of_void

  let assert_stratification =
    let check s u1 u2 =
      let r1, r2 = U.(repr u1, repr u2) in
      let k1, k2 = R.(kind r1, kind r2) in
      match k1, k2 with
      | `Global,  `Global
      | `Poly _,  `Global
      | `Local _, `Global      -> ()
      | `Poly f,  `Poly f'
        when
          not O.check_locality
          || String.equal f f' -> ()
      | `Local f, (`Poly f'
                  | `Local f')
        when
          not O.check_locality
          || String.equal f f' -> ()
      | `Dummy,   _
      | _,        `Dummy       -> Console.fatal "Separation.stratification: leftover dummy region: %a is %s of %a"
                                    R.pp r1 s R.pp r2
      | _                      -> Console.fatal "Separation.stratification: stratification violation: %a is %s of %a"
                                    R.pp r1 s R.pp r2
    in
    let visited = H'.create () in
    fun u ->
      let rec loop s u u' =
        let open Format in
        try
          ignore @@ H'.find u' visited
        with Not_found ->
          check s u u';
          H'.add u' u' visited;
          arrows             (fun fi -> loop (asprintf "`%a' pointer field" pp_field fi) u')   u';
          derefs             (loop "deref" u')                                                 u';
          dots               (fun fi -> loop (asprintf "`%a' composite field" pp_field fi) u') u';
          dot_voids          (loop "(void *) cast" u')                                         u';
          containers         (fun fi -> loop (asprintf "`%s.%a' container"
                                                (compFullName fi.fcomp) pp_field fi) u')       u';
          containers_of_void (fun ty -> loop (asprintf "(%a *) cast" pp_typ ty) u')            u'
      in
      loop "self reference" u u;
      H'.clear visited

  module Arc = struct
    type t =
      | Deref
      | Dot_void
      | Arrow     of fieldinfo
      | Dot       of fieldinfo
      | Container of fieldinfo
      | Container_of_void of typ
    let arrow     fi = Arrow fi
    let dot       fi = Dot fi
    let container fi = Container fi
    let container_of_void typ = Container_of_void typ
    let equal a1 a2 =
      match a1, a2 with
      | Deref,                  Deref
      | Dot_void,               Dot_void               -> true
      | Arrow fi1,              Arrow fi2
      | Dot fi1,                Dot fi2
      | Container fi1,          Container fi2          -> Fieldinfo.equal fi1 fi2
      | Container_of_void ty1,  Container_of_void ty2  -> Typ.equal ty1 ty2
      | (Deref
        | Dot_void
        | Dot _
        | Arrow _
        | Container _
        | Container_of_void _), (Deref
                                | Dot_void
                                | Dot _
                                | Arrow _
                                | Container _
                                | Container_of_void _) -> false
    let hash =
      function
      | Deref                 -> 1
      | Dot_void              -> 2
      | Arrow     fi          -> 7 * Fieldinfo.hash fi + 3
      | Dot       fi          -> 7 * Fieldinfo.hash fi + 4
      | Container fi          -> 7 * Fieldinfo.hash fi + 5
      | Container_of_void typ -> 7 * Typ.hash typ + 6
  end

  module Key = struct
    type t = R.Kind.t * typ
    let equal (k1, ty1) (k2, ty2) = R.Kind.equal k1 k2 && Typ.equal ty1 ty2
    let hash (k, ty) = 104729 * R.Kind.hash k + Typ.hash ty
    let of_unifiable u = let r = U.repr u in r.R.kind, Ty.normalize r.R.typ
  end

  module Origin = struct
    type t =
      | Root
      | Child of Key.t * Arc.t

    let equal o1 o2 =
      match o1, o2 with
      | Root,           Root           -> true
      | Child (k1, a1), Child (k2, a2) -> Key.equal k1 k2 && Arc.equal a1 a2
      | (Root
        | Child _),     (Root
                        | Child _)     -> false
    let hash =
      function
      | Root         -> 0
      | Child (k, a) -> 15487399 * Key.hash k + 3 * Arc.hash a
  end

  module H_uu : sig
    type t
    val create : unit -> t
    val add : Origin.t -> U.t -> Origin.t -> U.t -> t -> unit
    val mem : U.t -> U.t -> t -> bool
    val iter : (Origin.t -> U.t -> Origin.t -> U.t -> unit) -> t -> unit
    val clear : t -> unit
  end = struct
    module H = Hashtbl.Make
        (struct
          type t = U.t * U.t
          let equal (u1, u2) (u3, u4) =
            let r1, r2, r3, r4 = U.(repr u1, repr u2, repr u3, repr u4) in
            R.equal r1 r3 && R.equal r2 r4
          let hash (u1, u2) =
            let r1, r2 = U.(repr u1, repr u2) in
            997 * R.hash r1 + R.hash r2
        end)
    type t = (Origin.t * Origin.t) H.t
    open! H
    let create () = create 16
    let add o1 u1 o2 u2 h = replace h (u1, u2) (o1, o2)
    let mem u1 u2 h = mem h (u1, u2)
    let iter f h = iter (fun (u1, u2) (o1, o2) -> f o1 u1 o2 u2) h
    let clear = clear
  end

  type 'x reflector =
    { reflect2 : 'k. 'h -> 'o -> 'o -> 'u -> ('u -> 'k -> 'fl * 'u) -> 'k -> 'u -> unit }
    constraint 'x = < o: 'o; u: 'u; h: 'h; fl: 'fl; ..>;;

  let traverse
        ~symm ?(guard=const4 true) ~reflect2 ?(pre=ignore4) ?(update=ignore4) ?(post=ignore4) =
    let reflect_all h =
      let key = Key.of_unifiable in
      let open Origin in
      let reflect u1 u2 a = reflect2.reflect2 h (Child (key u1, a)) (Child (key u2, a)) u2 in
      let reflect1 u1 u2 a  f   = reflect u1 u2 a      (const' f) ()
      and reflect2 u1 u2 mk f k = reflect u1 u2 (mk k) f          k  in
      fun u1 u2 ->
        let reflect1 = reflect1 u1 u2 and reflect2 mk = reflect2 u1 u2 mk in
        let module A = Arc in
        H_f.iter (reflect2 A.arrow             arrow)             u1 h_arrow;
        H'.iter  (reflect1 A.Deref             deref)             u1 h_deref;
        H_f.iter (reflect2 A.dot               dot)               u1 h_dot;
        H'.iter  (reflect1 A.Dot_void          dot_void)          u1 h_dot_void;
        H_f.iter (reflect2 A.container         container)         u1 h_container;
        H_t.iter (reflect2 A.container_of_void container_of_void) u1 h_container_of_void
    in
    let rec loop o1 o2 u1 u2 =
      if guard o1 u1 o2 u2 then
        let r1, r2 = U.(repr u1, repr u2) in
        let t1, t2 = map_pair (Ty.normalize % R.typ) (r1, r2) in
        if not (Ty.compatible t1 t2) then
          Console.fatal
            "Separation.traverse: encountered regions of different types: %a : %a, %a : %a"
            U.pp u1 pp_typ t1 U.pp u2 pp_typ t2;
        let h = H_uu.create () in
        reflect_all h u1 u2;
        if symm then reflect_all h u2 u1;
        pre o1 u1 o2 u2;
        H_uu.iter (fun o1' u1' o2' u2' -> loop o1' o2' u1' u2'; update o1 r1 o2 r2) h;
        post o1 u1 o2 u2
    in
    loop Origin.Root Origin.Root

  module H_map : sig
    type t
    val create : unit -> t
    val add : U.t -> U.t -> t ->  unit
    val replace : t -> U.t -> U.t -> unit [@@warning "-32"]
    val find : U.t -> t -> U.t
    val mem : U.t -> U.t -> t -> bool
    val find_repr : U.t -> U.t -> t -> U.t
    val collapse : (U.t -> U.t list -> unit) -> t -> unit
    val iter : (U.t -> U.t -> unit) -> t -> unit
    val clear : t -> unit
  end = struct
    module H = R.H
    type t = U.t list H.t
    open! H
    let put ?(add=true) h u1 u2 =
      let r1 = U.repr u1 in
      let us = if add then try find h r1 with Not_found -> [] else [] in
      replace h r1 (u2 :: us)
    let add u1 u2 h = put h u1 u2
    let replace = put ~add:false
    let find_all u h = try find h (U.repr u) with Not_found -> []
    let find u h = List.hd @@ find h (U.repr u)
    let mem u1 u2 h = List.exists (R.equal (U.repr u2) % U.repr) @@ find_all u1 h
    let find_repr u1 u2 h = List.find ((<>) `First % R.choose (U.repr u2) % U.repr) @@ find_all u1 h
    let collapse f h =
      iter List.(fun _ vs -> f (hd vs) @@ tl vs) h;
      filter_map_inplace List.(const @@ some % singleton % hd) h
    let iter f h = iter (fun k -> List.iter @@ f @@ U.of_repr k) h
    let clear = clear
    let create () = create 512
  end
  module H_l : sig
    type t
    val create : unit -> t
    val add : Origin.t -> U.t -> t -> unit
    val remove : Origin.t -> U.t -> t -> unit
    val replace : Origin.t -> U.t -> t -> unit
    val update : Origin.t -> R.t -> t -> unit
    val find : Origin.t -> U.t -> t -> U.t * int
    val clear : t -> unit
    val maxl : int
    val maxd : int
    val maxc : int
  end = struct
    module H = Hashtbl.Make
        (struct
          type t = Origin.t * Key.t
          let equal (o1, k1) (o2, k2) = Origin.equal o1 o2 && Key.equal k1 k2
          let hash (o, k) = 179425879 * Origin.hash o + Key.hash k
        end)
    type t = (U.t * int) H.t
    open! H
    let  maxl,          maxd,         maxc =
      O.(region_length, region_depth, region_count)
    let create () = create 128
    let key o u = o, Key.of_unifiable u
    let derefable ty =
      match unrollType ty with
      | TPtr (TFun _, _)   -> false
      | TPtr _
      | TArray _
      | TComp _
      | TBuiltin_va_list _ -> true
      | TVoid _
      | TInt _
      | TFloat _
      | TFun _
      | TEnum _            -> false
      | TNamed _           -> assert false
    let put add o u h =
      let _, (_, ty) as k = key o u in
      if derefable ty then
        match find h k with
        | _, d                -> add h k (u, d + 1)
        | exception Not_found -> add h k (u, 0)
    let update o r h =
      let u = U.of_repr r in
      let k = key o u in
      match find h k with
      | _, d                -> replace h k (u, d)
      | exception Not_found -> ()
    let add = put add
    let replace = put replace
    let remove o u h = remove h (key o u)
    let find o u h = find h (key o u)
    let clear = clear
  end

  let instantiate =
    let loops = H_l.create () in
    fun ~map ->
      let reflect2 h o1' o2' u2 f k u1' =
        let add u1' u2' =
          H_map.add     u1'     u2' map;
          H_uu.add  o1' u1' o2' u2' h
        in
        match f u2 k with
        | `Old, u2' when H_map.mem u1' u2' map   -> ()
        | `Old, u2'                              -> add u1' u2'
        | `New, u2'                              ->
          match H_map.find_repr u1' u2' map with
          | u2''                                 ->(R.demote (U.repr u2');
                                                    U.unify u2' u2'')
          | exception Not_found                  ->
            match H_l.find o2' u2' loops with
            | u2'', d when d >= H_l.maxl         ->(R.demote (U.repr u2');
                                                    U.unify u2' u2'';
                                                    add u1' u2'')
            | _                                  -> add u1' u2'
            | exception Not_found                -> add u1' u2'
      in
      let reflect2 = { reflect2 } in
      fun u1 u2 ->
        H_map.add u1 u2 map;
        traverse
          ~symm:false
          ~reflect2
          ~pre:(fun _ u1 o2 u2 ->
            H_l.add o2 u2 loops;
            if (U.repr u1).R.kind = `Global then H_map.add u1 u1 map)
          ~post:(fun _ _ o2 u2 -> H_l.remove o2 u2 loops)
          u1 u2;
        H_l.clear loops

  let unify =
    let loops = H_l.create () in
    let queued = H_uu.create () in
    let depth = ref 0 in
    let reflect2 h o1' o2' u2 f k u1' =
      let add u1' u2' =
        if not H_uu.(mem u1' u2' queued || mem u2' u1' queued) then begin
          H_uu.add o1' u1' o2' u2' h;
          H_uu.add o1' u1' o2' u2' queued
        end
      in
      let add_new u1' u2' =
        let r2' = U.repr u2' in
        match R.choose (U.repr u1') r2' with
        | `First  -> U.unify u1' u2'
        | `Any    ->(R.demote r2';
                     U.unify u1' u2')
        | `Second -> add u1' u2'
      in
      match f u2 k with
      | `Old, u2'                         -> add u1' u2'
      | `New, u2'                         ->
        match H_l.find o2' u2' loops with
        | u2'', c when c >= H_l.maxc
                    || !depth >= H_l.maxd ->(R.demote (U.repr u2');
                                             U.unify u2' u2'';
                                             add u1' u2'')
        | _                               -> add_new u1' u2'
        | exception Not_found             -> add_new u1' u2'
    in
    let reflect2 = { reflect2 } in
    let diff_kind r1 r2 = not R.(Kind.equal r1.kind r2.kind) in
    fun u1 u2 ->
      depth := 0;
      traverse
        ~symm:true
        ~guard:(fun _ u1 _ u2 -> not U.(R.equal (repr u1) @@ repr u2))
        ~reflect2
        ~pre:(fun o1 u1 o2 u2 ->
          H_l.replace o1 u1 loops;
          if U.(diff_kind (repr u1) @@ repr u2) then H_l.replace o2 u2 loops;
          incr depth;
          U.unify u1 u2)
        ~update:(fun o1 r1 o2 r2 ->
          H_l.update o1 r1 loops;
          if diff_kind r1 r2 then H_l.update o2 r2 loops)
        ~post:(fun _ _ _ _ -> decr depth)
        u1 u2;
      H_l.clear loops;
      H_uu.clear queued

  let reflect ~map u ~on:u' =
    H_map.clear map;
    instantiate ~map u u';
    H_map.collapse (List.iter % unify) map

  let constrain ~map ~by us =
    H_map.clear map;
    List.iter2 (instantiate ~map) by us;
    H_map.collapse (List.iter % unify) map

  let widen us =
    let q = Queue.create () in
    let uu = H_l.create () in
    let queued = H'.create () in
    let push o u =
      if not (H'.mem u queued) then begin
        Queue.push (o, u) q;
        H'.add u u queued;
        H_l.add o u uu
      end
    in
    let open Origin in
    List.iter (push Root) us;
    let key = Key.of_unifiable in
    let push1 u a    = push (Child (key u, a)) in
    let push2 u mk k = push1 u (mk k) in
    while not (Queue.is_empty q) do
      let o, u = Queue.pop q in
      begin match H_l.find o u uu with
      | u', _               -> unify u u'
      | exception Not_found -> ()
      end;
      let open! Arc in
      let push1 = push1 u and push2 x = push2 u x in
      H_f.iter (push2 arrow)             u h_arrow;
      H'.iter  (push1 Deref)             u h_deref;
      H_f.iter (push2 dot)               u h_dot;
      H'.iter  (push1 Dot_void)          u h_dot_void;
      H_f.iter (push2 container)         u h_container;
      H_t.iter (push2 container_of_void) u h_container_of_void
    done

  let arrow = snd %% arrow
  let deref = snd % deref
  let dot = snd %% dot
  let dot_void = snd % dot_void
  let container = snd %% container
  let container_of_void = snd %% container_of_void

  let clear () =
    U.clear ();
    R.H.clear R.h_void_xs;
    H_f.clear h_arrow;
    H'.clear  h_deref;
    H_f.clear h_dot;
    H'.clear  h_dot_void;
    H_f.clear h_container;
    H_t.clear h_container_of_void
end

module type Analysis = sig
  module R : Representant_intf with type 'a region = 'a Representant.region
  module U : Unifiable with type repr = R.t
  module I : Info.Info with module R := R and module U := U

  val match_container_of1 : exp_node -> (exp * (fieldinfo * typ) Info.offs) option
  val match_container_of2 : exp_node -> (exp * (fieldinfo * typ) Info.offs) option
  val match_dot : exp_node -> (exp * (fieldinfo * typ) Info.offs) option

  type ('a, 'b) offs = [ `Field of 'a | `Container_of_void of 'b ]
  type +'a maybe_region =
    [< `Location of U.t * (unit -> [ `None | `Value of U.t ])
    |  `Value of U.t
    |  `None ] as 'a

  val take : [< (fieldinfo, typ) offs | `Container of fieldinfo | `Dot_void | `Arrow of fieldinfo ] list -> U.t -> U.t
  val inv : [< ('a, 'b) offs ] list -> [> `Container of 'a | `Dot_void ] list
  val retvar : varinfo -> varinfo
  val of_var : ?f:string -> varinfo -> [ `Location of _ | `Value of _  | `None ] maybe_region
  val of_string : [ `S of string | `WS of int64 list ] -> [ `Location of _ ] maybe_region
  val of_lval : ?f:string -> lval -> [ `Location of _ | `Value of _  | `None ] maybe_region
  val of_expr : ?f:string -> exp -> [ `Value of _ | `None ] maybe_region
  val location : [ `Location of _ | `Value of _  | `None ] maybe_region -> U.t
  val compute_regions : unit -> unit
  val dot_voids : (U.t -> unit) -> U.t -> unit
  val containers_of_void : (typ -> U.t -> unit) -> U.t -> unit
  module H_map : sig
    type t
    val find : U.t -> t -> U.t
    val iter : (U.t -> U.t -> unit) -> t -> unit
  end
  val map : stmt -> kernel_function -> H_map.t
  val maps : stmt -> (kernel_function * H_map.t) list
  val arg_regions : stmt -> ?f:string -> kernel_function -> lval option -> exp list -> U.t list
  val param_regions : kernel_function -> U.t list
  val relevant_region : ?f:string -> U.t -> bool
  val initial_deps : kernel_function -> ((typ I.offs * fieldinfo option) list * U.t * U.t) list

  val callee_approx : Kf.t list Exp.Hashtbl.t option

  val clear : unit -> unit
end

module Analysis
    (C : sig
       val offs_of_key : (fieldinfo * typ) Info.offs Info.H_field.t
       val callee_approx : Kf.t list Exp.Hashtbl.t option
       val mode : [ `Poly_rec | `Mono_rec | `Global ]
       val widen : bool
       val assert_stratification : bool
       val recognize_container_of2 : bool
       val region_length : int
       val region_depth : int
       val region_count : int
     end) ()
  : Analysis
= struct
  module Separation =
    Separation
      (struct
        let   region_length, region_depth, region_count =
          C.(region_length, region_depth, region_count)
        let check_locality = match C.mode with `Poly_rec -> true | `Mono_rec | `Global -> false
      end)
      ()

  open Separation
  module R = R
  module U = U

  module H_field = Info.H_field
  module I = Info.Make (R) (U) ()

  module H_v = Varinfo.Hashtbl
  module H_s =
    Hashtbl.Make
      (struct
        module Int64_list = Datatype.List (Datatype.Int64)
        type t = [`S of string | `WS of int64 list]
        let equal s1 s2 =
          match s1, s2 with
          | `S s1, `S s2     -> String.equal s1 s2
          | `WS ws1, `WS ws2 -> Int64_list.equal ws1 ws2
          | `S _, `WS _
          | `WS _, `S _      -> false
        let hash = function `S s -> Datatype.String.hash s | `WS ws -> 7 * Int64_list.hash ws + 3
      end)
  module H_l = Lval.Hashtbl
  module H_e = Exp.Hashtbl

  let h_var = H_v.create 4096
  let h_str = H_s.create 256
  let h_lval = H_l.create 4096
  let h_expr = H_e.create 4096

  let match_container_of1 =
    let rec match_offset ?(acc=[]) =
      function
      | NoOffset        when acc <> []        -> Some (List.rev acc)
      | NoOffset                              -> None
      | Field (fi, off) when fi.fcomp.cstruct -> match_offset ~acc:(`Field fi :: acc) off
      | Field (fi, off)                       -> match_offset
                                                   ~acc:(`Container_of_void (fi, Ty.(normalize @@ unbracket fi.ftype))
                                                         :: acc)
                                                   off
      | Index _                               -> None
    in
    function
    | CastE (pstr, _,
             { enode = BinOp (MinusPI,
                              { enode = CastE (chrptr, _, mptr); _ },
                              { enode =
                                  CastE (size_t, _,
                                         { enode = AddrOf (Mem { enode = CastE (pstr', _, zero); _ }, off); _ });
                                _ }, _); _ })
      when
        isPointerType pstr && isPointerType pstr' && isCharPtrType chrptr && isPointerType (typeOf mptr) &&
        not (need_cast theMachine.typeOfSizeOf size_t) && isZero zero &&
        let str = Ast_info.pointed_type pstr and str' = Ast_info.pointed_type pstr' in
        match unrollType str, unrollType str' with
        | TComp (ci, _, _), TComp (ci', _, _)
          when ci.cstruct && ci'.cstruct && Compinfo.equal ci ci' -> true
        | _ -> false
      ->
      opt_map (fun off -> mptr, off) @@ match_offset off
    | _ -> None

  let match_container_of2 =
    function
    | BinOp ((PlusPI | IndexPI),
             { enode = CastE (pstr, _, e); _ },
             { enode = Const (CInt64 (c, (IULongLong | IULong), _)); _ }, _)
      when isPointerType pstr ->
      begin match unrollType @@ Ast_info.pointed_type pstr, unrollType (typeOf e) with
      | TComp (ci, _, _), (TPtr _ | TArray _ as ty) when ci.cstruct ->
        begin try
          Some (e, H_field.find C.offs_of_key (ci, Ty.deref_once ty, c))
        with
        | Not_found -> None
        end
      | _ -> None
      end
    | _ -> None

  let match_container_of2 = if C.recognize_container_of2 then match_container_of2 else const None

  let match_dot =
    let is_uchar_ptr_type ty =
      match unrollType ty with
      | TPtr (TInt (IUChar, _), _) -> true
      | _                          -> false
    in
    function
    | BinOp ((PlusPI | IndexPI),
             { enode = CastE (chrptr, _, e); _ },
             { enode = Const (CInt64 (c, (IULongLong | IULong), _)); _ }, _)
      when is_uchar_ptr_type chrptr && isPointerType (typeOf e) ->
      let ty = Ast_info.pointed_type (typeOf e) in
      begin match unrollType ty with
      | TComp (ci, _, _) ->
        begin try
          Some (e, H_field.find C.offs_of_key (ci, uintType, c))
        with
        | Not_found -> None
        end
      | _ -> None
      end
    | _ -> None

  let match_dot = if C.recognize_container_of2 then match_dot else const None

  (* Notice about handling integers used as pointers: they don't have regions, i.e. it's unsound(!),
     we just create a fresh region each time we cast an integer to a pointer, but this is done
     separately for each case below *)
  let deref u = if isPointerType (U.repr u).R.typ then `Value (deref u) else `None

  let resolve_addressible addrof typ u () =
    if addrof && not @@ isArrayType typ then deref u
    else if isArrayType typ             then `Value u
    else                                     `None

  type ('a, 'b) offs = [ `Field of 'a | `Container_of_void of 'b ]

  let rec take offs u =
    match offs with
    | []                            -> u
    | `Field fi ::             offs -> take offs @@ dot u fi
    | `Container fi ::         offs -> take offs @@ container u fi
    | `Container_of_void ty :: offs -> take offs @@ container_of_void u ty
    | `Dot_void ::             offs -> take offs @@ dot_void u
    | `Arrow fi ::             offs -> take offs @@ arrow u fi

  let inv offs =
    let rec loop acc =
      function
      | []                           -> acc
      | `Field fi ::            offs -> loop (`Container fi :: acc) offs
      | `Container_of_void _ :: offs -> loop (`Dot_void :: acc) offs
    in
    loop [] offs

  let memoize ~find ~replace h fn ?f x =
    try find h x
    with
    | Not_found ->
      let r = fn ?f x in
      replace h x r;
      r

  type +'a maybe_region =
    [< `Location of U.t * (unit -> [ `None | `Value of U.t ])
    |  `None
    |  `Value of U.t ] as 'a

  let retvar, is_retvar, clear_retvars =
    let h_to_retvar = H_v.create 1024 in
    let h_retvars = H_v.create 1024 in
    (fun vi ->
       H_v.memo h_to_retvar vi @@
       fun vi ->
       let vi = copyVarinfo vi @@ "!" ^ vi.vname in
       H_v.replace h_retvars vi ();
       vi),
    H_v.mem h_retvars,
    fun () -> H_v.clear h_to_retvar; H_v.clear h_retvars

  (* Also used to retrieve return regions, when applied to retvars *)
  let rec of_var ?f x =
    let of_var =
      let open! H_v in
      memoize ~find ~replace h_var @@
      fun ?f v ->
      let retvar = is_retvar v in
      let vaddrof = v.vaddrof && not retvar in
      let typ = Ty.rtyp_if_fun v.vtype in
      if not (isStructOrUnionType typ || isArrayType typ || vaddrof || isPointerType typ ||
              isFunctionType v.vtype && not retvar)
      then
        `None
      else
        let u =
          let typ' =
            if (vaddrof && not @@ isArrayType typ) || isStructOrUnionType typ
            then Ty.normalize typ
            else Ty.deref_once typ
          in
          U.of_repr @@
          match retvar, unrollType typ, f with
          | true,  TComp _, Some f                         -> R.local  f ("!" ^ f)                 typ'
          | true,  _,       Some f                         -> R.poly   f f               R.Exp.ret typ'
          | true,  _,       None                           -> Console.fatal "Retvar requested from global scope: %a"
                                                                pp_varinfo v

          | false, _,       _      when (isFunctionType
                                           v.vtype)        -> R.global   v.vname         (Some (R.Exp.addr v)) v.vtype

          | false, TComp _, _      when v.vglob            -> R.global   ("&" ^ v.vname) (Some (R.Exp.addr v)) typ'
          | false, _,       _      when v.vglob && vaddrof -> R.global   ("&" ^ v.vname) (Some (R.Exp.addr v)) typ'
          | false, _,       _      when v.vglob            -> R.global   v.vname         (Some (R.Exp.var v))  typ'
          | false, _,       None                           -> Console.fatal
                                                                "Non-global variable outside any function: %a"
                                                                pp_varinfo v

          | false, TComp _, Some f                         -> R.local  f ("&" ^ v.vname)               typ'
          | false, _,       Some f when vaddrof            -> R.local  f ("&" ^ v.vname)               typ'

          | false, _,       Some f when v.vformal          -> R.poly   f v.vname         (R.Exp.var v) typ'
          | false, _,       Some f                         -> R.local  f v.vname                       typ'
        in
        if isFunctionType v.vtype && not retvar
        then `Location (u, fun () -> `Value u)
        else if isStructOrUnionType typ || (isArrayType typ && not v.vformal) || vaddrof
        then `Location (u, resolve_addressible v.vaddrof typ u)
        else `Value u
    in
    of_var ?f x
  and of_string x =
    let of_string =
      let open! H_s in
      memoize ~find ~replace h_str @@
      fun ?f:_ s ->
      let u =
        let s' =
          match s with
          | `S s -> s
          | `WS s ->
            String.concat "" @@
            List.map
              (fun wc ->
                 String.init
                   8
                   (fun i ->
                      let sh = 56 - 8 * i in
                      Char.chr Int64.(to_int @@ shift_right_logical (logand wc @@ shift_left 0xFFL sh) sh)))
              s
        in
        U.of_repr @@ R.global ("\"" ^ s' ^ "\"") None (match s with `S _ -> charType | `WS _ -> theMachine.wcharType)
      in
      `Location (u, fun () -> `Value u)
    in
    of_string x
  and fresh =
    let counter = ref ~-1 in
    fun ?f ty ->
      incr counter;
      let name = "fresh#" ^ string_of_int !counter in
      let ty = Ty.deref_once ty in
      U.of_repr @@
      match f with
      | Some f -> R.local f   name      ty
      | None   -> R.global    name None ty
  and value : 'a. ?f:_ -> _ -> ([< `Location of _ | `Value of _ | `None ] as 'a) -> _ = fun ?f ty ->
    function
    | `Location (_, get) ->
      begin match get () with
      | `Value u         -> u
      | `None            -> fresh ?f ty
      end
    | `Value u           -> u
    | `None              -> fresh ?f ty
  and location =
    function
    | `Location (u, _)     -> u
    | `Value _ | `None     -> Console.fatal "Analysis.location: got value where memory location is needed"
  and of_lval ?f x =
    let of_lval =
      let open! H_l in
      memoize ~find ~replace h_lval @@
      fun ?f lv ->
      let of_var = of_var ?f in
      let of_lval = of_lval ?f in
      let of_expr = of_expr ?f in
      let value r = value ?f r in
      let lv', off = removeOffsetLval lv in
      let no_offset () =
        match fst lv' with
        | Var v -> of_var v
        | Mem e -> let u = value (typeOf e) (of_expr e) in `Location (u, fun () -> deref u)
      in
      let struct_field fi =
        let u = location (of_lval lv') in
        if fi.faddrof || isStructOrUnionType fi.ftype || isArrayType fi.ftype
        then let u = dot u fi in `Location (u, resolve_addressible fi.faddrof fi.ftype u)
        else `Location (u, fun () -> if isPointerType fi.ftype then `Value (arrow u fi) else `None)
      in
      let subunion () =
        let u = location (of_lval lv') in
        `Location (u, fun () -> `None)
      in
      let union_field fi =
        let u = container_of_void (location (of_lval lv')) (Ty.unbracket fi.ftype) in
        `Location (u,
                   if isArrayType fi.ftype        then fun () -> `Value u
                   else if isPointerType fi.ftype then fun () -> deref u
                   else                                fun () -> `None)
      in
      let index () =
        let r = of_lval lv' in
        let ty = typeOfLval lv in
        if isArrayType ty
        then r
        else let u = value ty r in `Location (u, fun () -> deref u)
      in
      match off with
      | NoOffset                                       -> no_offset ()
      | Field (fi, NoOffset) when fi.fcomp.cstruct     -> struct_field fi
      | Field (fi, NoOffset) when Ty.is_union fi.ftype -> subunion ()
      | Field (fi, NoOffset)                           -> union_field fi
      | Index (_, NoOffset)                            -> index ()
      | _                                              -> Console.fatal "Region.of_lval: broken invariant: \
                                                                         remaining offset after removeOffsetLval"
    in
    of_lval ?f x
  and of_expr ?f x =
    let of_expr =
      let open! H_e in
      memoize ~find ~replace h_expr @@
      fun ?f e ->
      let of_lval = of_lval ?f in
      let of_expr = of_expr ?f in
      let value r = value ?f r in
      let rtyp_if_fun =
        match e.enode with
        | Lval (Var vi, NoOffset) when is_retvar vi -> Ty.rtyp_if_fun
        | _                                         -> id
      in
      if not @@ isPointerType @@ rtyp_if_fun @@ typeOf e
      then
        `None
      else
        let cast ty e =
          let ty' = let ty' = typeOf e in if isIntegralType ty' then ty else ty' in
          let ty, ty' = map_pair Ty.deref_once (ty, ty') in
          let r = of_expr e in
          if Ty.compatible ty ty'
          then
            `Value (value (TPtr (ty, [])) r)
          else (* Both can't be void */union since they are compatible! *)
            let r = value (TPtr (ty', [])) r in
            match unrollType ty, unrollType ty' with
            | (TVoid _ | TComp ({ cstruct = false; _ }, _, _)), _  -> `Value (dot_void r)
            | ty, (TVoid _ | TComp ({ cstruct = false; _ }, _, _)) -> `Value (container_of_void r ty)
            | ty, ty' ->
              match Ci.(match_deep_first_subfield_of ty ty', match_deep_first_subfield_of ty' ty) with
              | Some offs, _                                       -> `Value (take offs r)
              | _,         Some offs                               -> `Value (take (inv offs) r)
              | _                                                  -> `Value (container_of_void (dot_void r) ty)

        in
        match match_container_of1 e.enode, match_container_of2 e.enode, match_dot e.enode with
        | Some (e, offs), _, _
        | _, Some (e, offs), _              -> `Value (take (inv offs) @@ value (typeOf e) @@ of_expr e)
        | _, _, Some (e, offs)              -> `Value (take (Ci.norm_offset offs) @@ value (typeOf e) @@ of_expr e)
        | None, None, None                  ->
          match e.enode with
          | Const (CStr s)                  -> `Value (value (typeOf e) @@ of_string @@ `S s)
          | Const (CWStr ws)                -> `Value (value (typeOf e) @@ of_string @@ `WS ws)
          | Const (CInt64 _ | CEnum _
                  | CChr _ | CReal _ )      -> assert false
          | Lval lv                         -> `Value (value (typeOfLval lv) @@ of_lval lv)
          | SizeOf _
          | SizeOfE _
          | SizeOfStr _
          | AlignOf _
          | AlignOfE _
          | UnOp _                          -> assert false
          | BinOp ((PlusPI | IndexPI
                   | MinusPI), e, _, _)     -> `Value (value (typeOf e) (of_expr e))
          | BinOp ((PlusA _ |MinusA _
                   | MinusPP
                   | Mult _ | Div _
                   | Mod _
                   | Shiftlt _ | Shiftrt
                   | Lt | Gt | Le | Ge
                   | Eq | Ne
                   | BAnd | BXor | BOr
                   | LAnd | LOr ), _, _, _) -> assert false

          | AddrOf lv
          | StartOf lv                      -> `Value (location @@ of_lval lv)
          | Info (e, _)                     -> of_expr e
          | CastE (ty, _, e)                -> cast ty e
    in
    of_expr ?f x

  module H_k = Kernel_function.Hashtbl
  module H_stmt = Stmt.Hashtbl
  module M_kf = Kf.Map
  module H_call =
    Hashtbl.Make
      (struct
        type t = stmt * kernel_function
        let equal (s1, kf1) (s2, kf2) = Stmt.equal s1 s2 && Kf.equal kf1 kf2
        let hash (s, kf) = 105871 * Stmt.hash s + Kf.hash kf
      end)

  let h_params = H_k.create 1024

  let h_maps = H_call.create 1024

  let register_cleanup, cleanup =
    let open! Queue in
    let queue = create () in
    (fun f -> add f queue),
    fun () -> iter ((|>) ()) queue; clear queue

  let param_regions =
    let module Kf = Kernel_function in
    let h_var = H_v.create 512 in
    let maps = H_k.create 512 in
    register_cleanup (fun () -> H_v.clear h_var; H_k.clear maps);
    let take_arrows ci = let arrows = Ci.arrows ci in fun u -> List.map (swap take @@ u) arrows in
    fun kf ->
      let params = Kf.get_formals kf in
      let retvar =
        if isVoidType @@ Kf.get_return_type kf
        then []
        else [retvar @@ Kf.get_vi kf]
      in
      let f = Kf.get_name kf in
      let comp_region vi =
        let ty = Ty.rtyp_if_fun vi.vtype in
        let u, u' =
          let open H_v in
          location @@ of_var ~f vi,
          let e = if is_retvar vi then R.Exp.ret else R.Exp.addr vi in
          memo h_var vi (fun vi -> U.of_repr @@ R.poly f vi.vname e @@ Ty.normalize ty)
        in
        let map = H_k.memo maps kf (fun _ -> H_map.create ()) in
        reflect ~map u ~on:u';
        match unrollType ty with
        | TComp (ci, _, _) ->(let take_arrows = take_arrows ci in
                              let rs = take_arrows u' in
                              List.iter2 unify (take_arrows u) rs;
                              u')
        | ty               -> Console.fatal "Region.Analysis.comp_regions: not a composite param, but %a" pp_typ ty
      in
      List.concat_map
        (fun vi ->
           match of_var ~f vi with
           | `Location _
             when
               isStructOrUnionType @@
               Ty.rtyp_if_fun vi.vtype -> [comp_region vi]
           | `Location (_, get)        ->
             begin match get () with
             | `Value u                -> [u]
             | `None                   -> []
             end
           | `Value u                  -> [u]
           | `None                     -> [])
        (retvar @ params)

  let arg_regions =
    let h_dummies = H_stmt.create 32 in
    register_cleanup (fun () -> H_stmt.clear h_dummies);
    fun s ?f kf lvo exprs ->
      let retr =
        let rtyp = unrollType @@ Kernel_function.get_return_type kf in
        if isVoidType rtyp
        then []
        else
          let memo =
            function
            | `None -> H_stmt.memo h_dummies s @@ fun _ -> value ?f rtyp `None
            | r     -> value ?f rtyp r
          in
          match lvo, rtyp with
          | None,    TPtr _
          | None,    TComp _ -> [memo `None]
          | None,    _       -> []
          | Some lv, TPtr _  -> [memo @@ of_lval ?f lv]
          | Some lv, TComp _ -> [location @@ of_lval ?f lv]
          | Some _,  _       -> []
      in
      retr @
      List.concat_map
        (fun e ->
           match of_expr ?f e with
           | `Value u                    -> [u]
           | `None                       ->
             match unrollType (typeOf e), e.enode with
             | TComp _, Lval lv -> [location @@ of_lval ?f lv]
             | TComp _, _       -> Console.fatal "Unexpected non-lvalue struct expression `%a'" pp_exp e
             | _                -> [])
        exprs

  let initial_deps kf =
    let open List in
    let f, rv, args = Kernel_function.(get_name kf, retvar @@ get_vi kf, get_formals kf) in
    let param_regions, arg_regions =
      (param_regions kf, arg_regions dummyStmt ~f kf (Some (var rv)) (map evar args)) |>
      if isStructOrUnionType @@ Ty.rtyp_if_fun rv.vtype
      then
        function
        | re :: prs, ri :: ars -> ri :: prs, re :: ars
        | [], _ | _, []        -> Console.fatal "Analysis.initial_deps: broken invariant: no composite return region"
      else
        id
    in
    let arg_tys =
      Ty.rtyp_if_fun rv.vtype :: map (fun vi -> vi.vtype) args |>
      filter (fun ty -> isStructOrUnionType ty || isPointerType ty || isArrayType ty)
    in
    let filter (ty, (au, pu)) =
      match unrollType ty with
      | TComp (ci, _, _) -> [Ci.offsets ci, au, pu]
      | _                -> []
    in
    concat_map filter @@ combine arg_tys @@ combine arg_regions param_regions

  let bump us offs = List.iter (ignore % take offs) us

  let bump_ci ci us = List.iter (bump us) (Ci.dots ci)

  let bump_param_regions kf =
    List.iter
      (fun (offs, au, pu) -> List.iter (bump [au; pu] % fst) offs)
      (initial_deps kf)

  let unify_exprs =
    let unify_comps ?f ci lv1 lv2 =
      let u1, u2 = map_pair (location % of_lval ?f) (lv1, lv2) in
      List.iter (fun offs -> uncurry unify @@ map_pair (take offs) (u1, u2)) (Ci.arrows ci);
      bump_ci ci [u1; u2]
    in
    let bump_comp ?f ci e =
      match of_expr ?f e with
      | `Value u -> bump_ci ci [u]
      | `None    -> ()
    in
    fun ?f e1 e2 ->
      let ty = Ty.rtyp_if_fun @@ typeOf e1 in
      match e1.enode, e2.enode, unrollType ty with
      | Lval lv1, Lval lv2, TComp (ci, _, _)    -> unify_comps ?f ci lv1 lv2
      | _                                       ->
        let norm ty =
          match unrollType ty with
          | TPtr _   -> unrollType @@ Ast_info.pointed_type ty
          | TArray _ -> unrollType @@ Ast_info.element_type ty
          | ty       -> ty
        in
        begin match (stripCasts e2).enode, norm ty with
        | Lval (Var vi, NoOffset), TComp (ci, _, _)
          when isVoidPtrType vi.vtype               -> bump_comp ?f ci e1
        | _                                         -> ()
        end;
        match of_expr ?f e1, of_expr ?f e2 with
        | `Value u1, `Value u2                  -> unify u1 u2
        | _                                     -> ()

  let relevant_region ?f u =
    if has_some f then
      match (U.repr u).R.kind with
      | `Global         -> true
      | `Local f'
      | `Poly f'
        when f' = the f -> true
      | `Local _
      | `Poly _
      | `Dummy          -> false
    else
      match (U.repr u).R.kind with
      | `Global         -> true
      | `Local _
      | `Poly _
      | `Dummy          -> false

  let unify_voids =
    let open List in
    let containers_of_void = reify containers_of_void (fun add _ u -> add u) in
    let first_substruct fi = reify dots (fun add fi' u -> if Fieldinfo.equal fi fi' then add u) in
    let derefs = reify derefs (@@) in
    let dot_voids = reify dot_voids (@@) in
    fun f ->
      List.iter
        (fun (n, rs) ->
           let unify u =
             ignore @@
             if n = 0 then
               containers_of_void u >>= fun u' ->
               begin match unrollType (U.repr u').R.typ with
               | TComp ({ cfields = fi :: _; cstruct = true; _ }, _, _)  -> first_substruct fi u'
               | TComp ({ cstruct = false; _ }, _, _)                    -> assert false
               | _                                                       -> []
               end >>=
               dot_voids >>= fun u' ->
               [unify u u']
             else
               dot_voids u >>=                             (* u  :: void *...   *)
               containers_of_void >>= fun u' ->            (* u' :: t    *...   *)
               let ty', n' = Ty.deref (U.repr u').R.typ in
               (if n' = n then [u'] else []) >>=           (* u' :: t    *... ? *)
               derefs >>= fun u' ->                        (* u' :: t     ...   *)
               derefs u >>= fun u ->                       (* u  :: void  ...   *)
               (if isVoidType (U.repr u).R.typ
                then                 containers_of_void u
                else dot_voids u >>= containers_of_void  ) >>= fun u ->  (* u :: t' ... *)
               let ty'', n'' = Ty.deref (U.repr u).R.typ in              (* t == t' ?   *)
               if n'' = n' - 1 && Ty.compatible ty' ty'' then [unify u u'] else []
           in
           List.iter (on (relevant_region ?f) unify % U.of_repr) rs)
        (R.all_void_xs ())

  let safe_param_regions ?f kf =
    switch (Some (Kernel_function.get_name kf));
    let r = param_regions kf in
    switch f;
    r

  let replay_on_call ~same_scc ~stmt ?f kf lvo args =
    let param_regions, arg_regions =
      H_k.memo h_params kf (safe_param_regions ?f), arg_regions stmt ?f kf lvo args
    in
    let param_regions, arg_regions =
      let open! List in
      let pair = param_regions, arg_regions in
      map_pair (take @@ uncurry min @@ map_pair length pair) pair
    in
    let fresh, map =
      let key = stmt, kf in
      match H_call.find_opt h_maps key with
      | Some map  -> false, map
      | None      -> true,  (let map = H_map.create () in
                             H_call.add h_maps key map;
                             map)
    in
    let bump_ret_region ci =
      let bump us = bump_ci ci [List.hd us] in
      bump arg_regions;
      switch (Some (Kernel_function.get_name kf));
      bump param_regions;
      switch f
    in
    begin match unrollType @@ Kernel_function.get_return_type kf with
    | TComp (ci, _, _) -> bump_ret_region ci
    | _                -> ()
    end;
    match C.mode, same_scc, fresh with
    | `Poly_rec, true,  _
    | `Poly_rec, false, true
    | `Mono_rec, false, true  -> constrain ~map ~by:param_regions arg_regions
    | `Mono_rec, true,  _
    | `Global,   _,     true  -> List.iter2 unify param_regions arg_regions
    | _,         _,     false -> ()

  let expr_of_lval =
    let cache = H_l.create 4096 in
    register_cleanup (fun () -> H_l.clear cache);
    fun ~loc lv -> H_l.memo cache lv (fun lv -> new_exp ~loc @@ Lval lv)

  open Visitor

  class virtual skipping_visitor = object(self)
    inherit frama_c_inplace
    method private virtual vexpr_pre : exp -> unit
    method private virtual vexpr_post : exp -> unit
    method! vexpr e =
      self#vexpr_pre e;
      match match_container_of1 e.enode, match_container_of2 e.enode with
      | Some (e', _), _
      | _,           Some (e', _) -> (ignore @@ visitFramacExpr (self :> frama_c_visitor) e';
                                      self#vexpr_post e;                                      SkipChildren)
      | None,        None         ->                                                          DoChildrenPost
                                                                                                (tap self#vexpr_post)
    method private virtual vstmt_post : stmt -> unit
    method! vstmt s =
      let vis = (self :> frama_c_visitor) in
      match s.skind with
      | Instr
          (Call (lv, { enode = Lval (Var f, NoOffset); _ }, args, _))
        when Kf.mem f                                                 ->(may
                                                                           (ignore % visitFramacLval vis)
                                                                           lv;
                                                                         List.iter
                                                                           (ignore % visitFramacExpr vis)
                                                                           args;
                                                                         self#vstmt_post s;                SkipChildren)
      | Instr
          (Local_init (vi, ConsInit (f, args, Plain_func), _))
        when Kf.mem f                                                 ->(ignore @@
                                                                         visitFramacVarDecl vis vi;
                                                                         List.iter
                                                                           (ignore % visitFramacExpr vis)
                                                                           args;
                                                                         self#vstmt_post s;                SkipChildren)
      | Instr (Local_init (_, ConsInit (_, _, Constructor), _))       -> Console.fatal "skipping_visitor: C++ \
                                                                                        constructors are unsupported"
      |_                                                              -> DoChildrenPost (tap self#vstmt_post)
  end

  let init_var ?f vi =
    let rec loop lv =
      function
      | SingleInit e        -> unify_exprs ?f (expr_of_lval ~loc:e.eloc lv) e
      | CompoundInit (_, l) -> List.iter (fun (off, init) -> loop (addOffsetLval off lv) init) l
    in
    loop @@ var vi

  let callee_approx = C.callee_approx

  class unifier scc_map fundec =
    let f = fundec.svar.vname in
    let () = switch (Some f) in
    object(self)
      inherit skipping_visitor

      method! vlval lv = ignore @@ of_lval ~f lv; DoChildren
      method private vexpr_pre = ignore % of_expr ~f
      method private vexpr_post e =
        match e.enode with
        | BinOp ((Eq | Ne),
                 { enode = CastE (ty, _, e1); _ },
                 { enode = CastE (ty', _, e2); _ },
                 _)
          when not (need_cast ty theMachine.upointType || need_cast ty ty') -> unify_exprs ~f e1 e2
        | BinOp ((Eq | Ne), e1, e2, _)                                      -> unify_exprs ~f e1 e2
        | _                                                                 -> ()
      method private vstmt_post stmt =
        let replay_on_call ~stmt ?f kf lvo args =
          replay_on_call ~same_scc:M_kf.(find (the self#current_kf) scc_map = find kf scc_map) ~stmt ?f kf lvo args
        in
        match stmt.skind with
        | Instr (Set (lv, e, loc))                       -> unify_exprs ~f (expr_of_lval ~loc lv) e
        | Instr (Local_init (vi, AssignInit init, _))    -> init_var ~f vi init
        | Instr
            (Call
               (lvo,
                { enode = Lval (Var f', NoOffset); _ },
                args, _))
          when Kf.mem f'                                 -> replay_on_call ~stmt ~f
                                                              (Globals.Functions.get f') lvo args
        | Instr
            (Local_init
               (vi, ConsInit (f', args, Plain_func), _)) -> replay_on_call ~stmt ~f
                                                              (Globals.Functions.get f') (Some (var vi)) args
        | Instr
            (Local_init
               (_, ConsInit (_, _, Constructor), _))     -> Console.fatal "unifier: C++ \
                                                                           constructors are unsupported"
        | Instr (Call (lvo, e, args, _))                 -> List.iter
                                                              (fun kf -> replay_on_call ~stmt ~f kf lvo args)
                                                              (Analyze.callee_approx ?callee_approx e)
        | Return (Some e, loc)                           -> unify_exprs ~f
                                                              (expr_of_lval ~loc @@ var @@ retvar @@ fundec.svar) e
        | _                                              -> ()

      method start = ()
      method finish =
        unify_voids (Some f);
        let kf = Globals.Functions.get fundec.svar in
        H_k.replace h_params kf @@ param_regions kf;
        bump_param_regions kf;
        if C.widen then
          widen @@
          List.concat_map
            (fun v ->
               match of_var ~f v with
               | `Location (u, _) | `Value u -> [u]
               | `None                       -> [])
            Kernel_function.(get_formals kf @ get_locals kf)
    end

  let pp_region_of fmttr pp_e e =
    function
    | `None            -> ()
    | `Location (u, _) -> Format.fprintf fmttr "%a\t@@\t%a;@\n" pp_e e R.pp @@ U.repr u
    | `Value u         -> Format.fprintf fmttr "%a\t\\\t%a;@\n" pp_e e R.pp @@ U.repr u

  let pp =
    let h_lv = H_l.create 1024 in
    let h_exp = H_e.create 1024 in
    register_cleanup (fun () -> H_l.clear h_lv; H_e.clear h_exp);
    fun fmttr fundec ->
      let f = fundec.svar.vname in
      H_l.clear h_lv;
      H_e.clear h_exp;
      let vis = object
        inherit skipping_visitor

        method! vlval _ =
          DoChildrenPost (tap @@ fun lv -> H_l.memo h_lv lv @@ pp_region_of fmttr pp_lval lv % of_lval ~f)
        method private vexpr_pre _ = ()
        method private vexpr_post e = H_e.memo h_exp e @@ pp_region_of fmttr pp_exp e % of_expr ~f
        method private vstmt_post _ = ()
      end in
      ignore @@ visitFramacFunction vis fundec

  let init_globals () = Globals.Vars.iter (fun vi { init } -> may (init_var vi) init)

  let pp_globals fmttr = Globals.Vars.iter (fun vi _ -> pp_region_of fmttr pp_varinfo vi @@ of_var vi)

  let assert_stratification =
    let assert_stratification ?f vi =
      match of_var ?f vi with
      | `Location (u, _) | `Value u -> assert_stratification u
      | `None                       -> ()
    in
    fun () ->
      visitFramacFile
        (object
          inherit frama_c_inplace
          method! vglob_aux =
            function
            | GVar (vi, _, _)
            | GVarDecl (vi,  _) -> assert_stratification vi; SkipChildren
            | _                 ->                           DoChildren
          method! vfunc f =
            List.(iter (iter @@ assert_stratification ~f:f.svar.vname) [f.sformals; f.slocals]);
            SkipChildren
        end)
        (Ast.get ())

  module Fixpoint =
    Fixpoint.Make
      (struct
        module E = struct
          type some = fundec
          let pp = pp
        end

        type t = int M_kf.t

        let get _ _ fundec = fundec
        let flag = R.flag
      end)

  let compute_regions () =
    Console.debug "Started compute_regions...";
    let sccs = Analyze.condensate ?callee_approx () in
    let scc_map, _ =
      List.(fold_left (fun (m, i) kfs -> fold_left (fun m kf -> M_kf.add kf i m) m kfs, i + 1) (M_kf.empty, 0) sccs)
    in
    Console.debug "Proceeding with region analysis...";
    switch None;
    init_globals ();
    Fixpoint.visit_until_convergence ~order:`topological (new unifier) scc_map sccs;
    switch None;
    unify_voids None;
    Console.debug ~level:3 "@[<2>Global result is:@\n%t@]" pp_globals;
    if C.assert_stratification then begin
      Console.debug "Finished compute_regions, will now check stratification invariants...";
      assert_stratification ()
    end

  let dot_voids = dot_voids
  let containers_of_void = containers_of_void

  module H_map = H_map

  let map s kf = H_call.find h_maps (s, kf)

  let maps s =
    match s.skind with
    | Instr
        (Call
           (_, { enode = Lval (Var f, NoOffset); _ },
            _, _)
        | Local_init (_, ConsInit (f, _, Plain_func), _))
      when Kf.mem f                                       ->(let kf = Globals.Functions.get f in
                                                             [kf, H_call.find h_maps (s, kf)])
    | Instr (Call (_, e, _, _))                           -> List.map
                                                               (fun kf -> kf, H_call.find h_maps (s, kf))
                                                               (Analyze.callee_approx ?callee_approx e)
    | _                                                   -> Console.fatal "Can't get region maps from \
                                                                            non-function-call statement"

  let param_regions kf = H_k.memo h_params kf param_regions

  let clear () =
    Separation.clear ();
    H_v.clear h_var;
    H_s.clear h_str;
    H_l.clear h_lval;
    H_e.clear h_expr;
    clear_retvars ();
    H_k.clear h_params;
    H_call.clear h_maps;
    cleanup ()
end
