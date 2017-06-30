(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

[@@@warning "-4-6"]

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

    let choose k1 k2 =
      begin match k1, k2 with
      | (`Poly f1
        | `Local f1),  (`Poly f2
                       | `Local f2)
        when not (String.equal f1 f2) -> Console.fatal
                                           "Representant.Kind.choose: broken invariant: \
                                            should not try unifying regions from diff. functions: %s and %s"
                                           f1 f2
      | `Dummy, `Dummy                ->  Console.fatal
                                            "Representant.Kind.choose: broken invariant: \
                                             dummy regions should be immediately unified with non-dummy ones"
      | (`Global
        | `Poly _
        | `Local _
        | `Dummy),     (`Global
                       | `Poly _
                       | `Local _
                       | `Dummy)      -> ()
      end;
      match k1, k2 with
      | `Global,  `Global                         -> `Any
      | `Global,  (`Poly _ | `Local _ | `Dummy)   -> `First
      | `Poly _,  `Global                         -> `Second
      | `Poly _,  `Poly _                         -> `Any
      | `Poly _,  (`Local _ | `Dummy)             -> `First
      | `Local _, (`Global | `Poly _)             -> `Second
      | `Local _, `Local _                        -> `Any
      | `Local _, `Dummy                          -> `First
      | `Dummy,   (`Global | `Poly _ | `Local _)  -> `Second
      | `Dummy,   `Dummy                          -> `Any

    let pp fmttr =
      let pp fmt = Format.fprintf fmttr fmt in
      function
      | `Global  -> pp "global"
      | `Poly s  -> pp "poly(%s)" s
      | `Local s -> pp "local(%s)" s
      | `Dummy   -> pp "dummy"
  end

  type t =
    {
      name : string;
      typ  : typ;
      kind : Kind.t
    }

  let name r = r.name
  let typ r = r.typ
  let kind r = r.kind

  let equal r1 r2 = String.equal r1.name r2.name
  let hash r = Hashtbl.hash r.name
  let compare r1 r2 = String.compare r1.name r2.name
  let choose r1 r2 = Kind.choose r1.kind r2.kind

  let flag = Flag.create "convergence"

  module H = Hashtbl.Make (struct type nonrec t = t let equal, hash = equal, hash end)

  let h_void_xs = H.create 512

  let mk ~name ~typ ~kind =
    let typ = Ty.normalize typ in
    let r = { name; typ; kind } in
    if kind <> `Dummy then begin
      Flag.report flag;
      let ty, n = Ty.deref typ in
      if isVoidType ty then H.replace h_void_xs r n
    end;
    r

  let report r1 ~is_repr_of:r2 =
    if isVoidType @@ fst @@ Ty.deref r2.typ then H.remove h_void_xs r2;
    if r1.kind = `Dummy then
      Console.fatal "Representant.report: trying to set dummy region as representant: %s of %s" r1.name r2.name;
    if r2.kind <> `Dummy then Flag.report flag

  let all_void_xs () =
    H.fold
      (fun r n ->
         let rec insert r n l =
           let open List in
           function
           | []                           -> rev_append l [n, [r]]
           | (n', rs) :: es when n' = n   -> rev_append l @@ (n', r :: rs) :: es
           | n', _ as e :: es when n' < n -> insert r n (e :: l) es
           | _ :: _ as es                 -> rev_append l @@ (n, [r]) :: es
         in
         insert r n [])
      h_void_xs
      []

  let global name typ = mk ~name ~typ ~kind:`Global
  let poly fname name typ = mk ~name:(fname ^ "::" ^ name) ~typ ~kind:(`Poly fname)
  let local fname name typ = mk ~name:(fname ^ ":::" ^ name) ~typ ~kind:(`Local fname)
  let dummy name typ = mk ~name ~typ ~kind:`Dummy
  let template =
    let counter = ref ~-1 in
    fun { name; typ; kind } ->
      let open Kind in
      match kind with
      | `Poly _                     -> incr counter; dummy ("dummy#" ^ string_of_int !counter) typ
      | `Global | `Local _ | `Dummy -> Console.fatal
                                         "Representant.template: can only templatify polymorphic regions, but %s is %a"
                                         name pp kind

  let check_field f r fi =
    match unrollType r.typ with
    | TComp (ci, _, _)
      when ci.cstruct && Compinfo.equal ci fi.fcomp -> ()
    | ty                                            -> Console.fatal
                                                         "%s: not a struct with field %s.%s: %a"
                                                         f fi.fname fi.fcomp.cname pp_typ ty

  let arrow r fi =
    check_field "Representant.arrow" r fi;
    if not (isPointerType fi.ftype) then
      Console.fatal "Representant.arrow: not a pointer field: %s.%s : %a" fi.fname fi.fcomp.cname pp_typ fi.ftype;
    mk ~name:(r.name ^ "->" ^ fi.fname) ~typ:(Ast_info.pointed_type fi.ftype) ~kind:r.kind

  let deref r =
    if not (isPointerType r.typ) then
      Console.fatal "Representant.deref: not a pointer region: %s : %a" r.name pp_typ r.typ;
    mk ~name:("*(" ^ r.name ^ ")") ~typ:(Ast_info.pointed_type r.typ) ~kind:r.kind

  let check_detached f fi =
    if not (isStructOrUnionType fi.ftype || isArrayType fi.ftype || fi.faddrof) then
      Console.fatal
        "%s: not a struct/union, array or addressed field: %s.%s : %a (&: %B)"
        f fi.fname fi.fcomp.cname pp_typ fi.ftype fi.faddrof

  let dot r fi =
    check_field "Representant.dot" r fi;
    check_detached "Representant.dot" fi;
    let typ = let typ = fi.ftype in if isArrayType typ then Ast_info.element_type typ else typ in
    mk ~name:(r.name ^ "." ^ fi.fname) ~typ ~kind:r.kind

  let container r fi =
    check_detached "Representant.container" fi;
    if Ty.compatible fi.ftype r.typ then
      Console.fatal
        "Representant.container: illegal use of `container_of': %s.%s : %a vs. %s : %a"
        fi.fname fi.fcomp.cname pp_typ fi.ftype r.name pp_typ r.typ;
    if not fi.fcomp.cstruct then
      Console.fatal "Representant.container: container should be a structure: %s" fi.fcomp.cname;
    mk
      ~name:("(" ^ r.name ^ ", " ^ fi.fcomp.cname ^ "." ^ fi.fname ^ ")")
      ~typ:(TComp (fi.fcomp, empty_size_cache (), []))
      ~kind:r.kind

  let dot_void r = mk ~name:(r.name ^ ".void") ~typ:voidType ~kind:r.kind

  let container_of_void r typ =
    let name =
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
                                                name r.name pp_typ ty
    end;
    mk ~name:("(" ^ r.name ^ ", " ^ name ^ ".void)") ~typ ~kind:r.kind

  let pp fmttr r =
    Format.fprintf fmttr "{ %s : %a (%a) }" r.name pp_typ r.typ Kind.pp r.kind
end

module type Representant = sig
  module Kind : sig type t end
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val choose : t -> t -> [> `First | `Second | `Any ]

  val name : t -> string
  val report : t -> is_repr_of:t -> unit

  val flag : Flag.t
end

module type Unifiable = sig
  type t
  type repr
  val of_repr : repr -> t
  val unify : t -> t -> unit
  val repr : t -> repr
end

module Make_unifiable (R : Representant) () : Unifiable with type repr = R.t = struct
  type t = R.t
  type repr = R.t
  let of_repr = id

  module H = Hashtbl.Make (R)

  let reprs = H.create 2048
  let ranks = H.create 2048

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
          else if String.(length @@ R.name r1 < length @@ R.name r2) then `First
          else                                                            `Second
      in
      match choice with
      | `First  -> set r1 ~as_repr_of:r2
      | `Second -> set r2 ~as_repr_of:r1
end

module type Hashmap = sig
  module R : Representant
  module U : Unifiable with type repr = R.t
  type t
  val create : unit -> t
  val add : U.t -> U.t -> t -> unit
  val add' : t -> U.t -> U.t -> unit
  val find : U.t -> t -> U.t
  val find_or_call : create:(R.t -> R.t) -> call:(U.t -> U.t -> unit) -> t -> U.t -> U.t
  val iter : (U.t -> unit) -> U.t -> t -> unit
  val clear : t -> unit
end

module Make_hashmap (R : Representant) (U : Unifiable with type repr = R.t) :
  Hashmap with module R = R and module U = U = struct
  module R = R
  module U = U

  module H = Hashtbl.Make (R)
  type t = U.t H.t
  let create () = H.create 4096
  let add u v h = H.replace h (U.repr u) v
  let add' h u v = add u v h
  let find u h = H.find h (U.repr u)
  let find_or_call ~create ~call h u =
    try
      find u h
    with
    | Not_found ->
      let u' = U.of_repr @@ create (U.repr u) in
      add u u' h;
      call u' u;
      u'
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
  val find_or_call : create:(R.t -> K.t -> R.t) -> call:(U.t -> K.t -> U.t -> unit) -> t -> U.t -> K.t -> U.t
  val iter : (K.t -> U.t -> unit) -> U.t -> t -> unit
  val clear : t -> unit
end

module Make_pair_hashmap (R : Representant) (U : Unifiable with type repr = R.t) (K : Hashtbl.HashedType) :
  Pair_hashmap with module R = R and module U = U and module K = K = struct
  module R = R
  module U = U
  module K = K

  module H =
    Hashtbl.Make
      (struct
        type t = R.t * K.t
        let equal (r1, k1) (r2, k2) = R.equal r1 r2 && K.equal k1 k2
        let hash (r, k) = 199 * R.hash r + K.hash k
      end)
  module H_k = Hashtbl.Make (R)

  type t = U.t H.t * K.t H_k.t
  let create () = H.create 4096, H_k.create 256
  let add u k v (h, ks) =
    let r = U.repr u in
    H.replace h (r, k) v;
    H_k.add ks r k
  let add' h u k v = add u k v h
  let find u k (h, _) = H.find h (U.repr u, k)
  let find_or_call ~create ~call h u k =
    try
      find u k h
    with
    | Not_found ->
      let u' = U.of_repr @@ create (U.repr u) k in
      add u k u' h;
      call u' k u;
      u'
  let iter f u (h, ks) =
    let r = U.repr u in
    List.iter (fun k -> f k @@ H.find h (r, k)) (H_k.find_all ks r)

  let clear (h, ks) = H.clear h; H_k.clear ks
end

module Separation : functor () -> sig
  module R = Representant
  module U : Unifiable with type repr = R.t
  module H' : Hashmap with module R := R and module U = U

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
  val unify : U.t -> U.t -> unit
  val duplicate : map:H'.t -> U.t -> U.t
  val accomodate : map:H'.t -> U.t list -> on:U.t list -> unit
  val replay : map:H'.t -> U.t list -> on:U.t list -> unit
end = functor () -> struct
  module R = Representant
  module U = Make_unifiable (R) ()

  module H_f = Make_pair_hashmap (R) (U) (Fieldinfo)
  module H_t = Make_pair_hashmap (R) (U) (Typ)
  module H' = Make_hashmap (R) (U)

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
      ~call:(fun u u' -> H_t.add u (U.repr u).R.typ u' h_container_of_void)
      h_dot_void
  let container = H_f.find_or_call ~create:R.container ~call:(H_f.add' h_dot) h_container
  let container_of_void u ty =
    let ty = Ty.normalize ty in
    H_t.find_or_call ~create:R.container_of_void ~call:(fun u _ u' -> H'.add u u' h_dot_void) h_container_of_void u ty

  let arrows f u = H_f.iter f u h_arrow
  let derefs f u = H'.iter f u h_deref
  let dots f u = H_f.iter f u h_dot
  let dot_voids f u = H'.iter f u h_dot_void
  let containers f u = H_f.iter f u h_container
  let containers_of_void f u = H_t.iter f u h_container_of_void

  type 'k handler2 = (U.t -> 'k -> U.t) -> U.t -> 'k -> U.t -> unit

  let handle_all ~handle1 ~(handle2:< f : 'k. 'k handler2; ..>) u1 u2 =
    let handle2 f u k u' = handle2#f f u k u' in
    H_f.iter (handle2 arrow u2) u1 h_arrow;
    H'.iter (handle1 deref u2) u1 h_deref;
    H_f.iter (handle2 dot u2) u1 h_dot;
    H'.iter (handle1 dot_void u2) u1 h_dot_void;
    H_f.iter (handle2 container u2) u1 h_container;
    H_t.iter (handle2 container_of_void u2) u1 h_container_of_void

  let unify u1 u2 =
    let module T = Typ.Hashtbl in
    let module H =
      Hashtbl.Make
        (struct
          type t = U.t * U.t
          let equal (u1, u2) (u3, u4) =
            let r1, r2, r3, r4 = U.(repr u1, repr u2, repr u3, repr u4) in
            R.equal r1 r2 && R.equal r3 r4
          let hash (u1, u2) =
            let r1, r2 = U.(repr u1, repr u2) in
            997 * R.hash r1 + R.hash r2
        end)
    in
    let h = H.create 256 in
    let handle1, handle2 =
      let add h u u' = if not (H.mem h (u, u') || H.mem h (u', u)) then H.replace h (u, u') () in
      (fun f u u' -> add h (f u) u'),
      object
        method f : 'k. 'k handler2 = fun f u k u' -> add h (f u k) u'
      end
    in
    let cache = Typ.Hashtbl.create 128 in
    let rec unify ?(max_count=3) ?(retain_cache=Typ.Hashtbl.clear cache) u1 u2 =
      let r1 = U.repr u1 and r2 = U.repr u2 in
      if not (R.equal r1 r2) then
        let t1, t2 = map_pair Ty.normalize (r1.R.typ, r2.R.typ) in
        if Ty.compatible t1 t2 then
          Console.fatal
            "Can't unify regions of different types: %s : %a, %s : %a"
            r1.R.name pp_typ r1.R.typ r2.R.name pp_typ r2.R.typ;
        H.clear h;
        handle_all handle1 handle2 u1 u2;
        handle_all handle1 handle2 u2 u1;
        U.unify u1 u2;
        let u = U.of_repr (U.repr u1) in
        let clone =
          let self count = T.replace cache t1 (u, count + 1); u in
          match T.find cache t1 with
          | _, count when count < max_count -> self count
          | clone, _ -> clone
          | exception Not_found -> self 0
        in
        H.iter (fun (u, u') () -> unify ~max_count ~retain_cache u u') h;
        unify ~max_count ~retain_cache u clone
    in
    unify ~max_count:(Options.Region_depth.get ()) u1 u2

  let rec duplicate ~map ?clone u =
    let handle1 f u u' = ignore @@ duplicate ~map ~clone:(f u) u'
    and handle2 = object
      method f : 'k. 'k handler2 = fun f u k u' -> ignore @@ duplicate ~map ~clone:(f u k) u'
    end in
    if (U.repr u).R.kind = `Global
    then u
    else
      try
        H'.find u map
      with
      | Not_found ->
        let u' = may_map id ~dft:(U.of_repr @@ R.template (U.repr u)) clone in
        H'.add u u' map;
        handle_all ~handle1 ~handle2 u u';
        u'

  let accomodate ~map regs ~on = List.iter2 (fun clone -> ignore % duplicate ~map ~clone) on regs

  let duplicate ~map u = duplicate ~map u

  let replay ~map regs ~on =
    H'.clear map;
    List.iter2 unify on (List.map (duplicate ~map) regs)
end

module type Analysis = sig
  module R = Representant
  module U : Unifiable with type repr = R.t
  module I : module type of Info.Make (R) (U) ()

  val match_container_of1 : exp_node -> (exp * Info.offs) option
  val match_container_of2 : exp_node -> (exp * Info.offs) option
  val match_dot : exp_node -> (exp * Info.offs) option

  type ('a, 'b, 'c) offs = [ `Field of 'a | `Container of 'b | `Container_of_void of 'c ]
  type 'a maybe_region =
    [< `Location of U.t * (unit -> [ `None | `Value of U.t ])
    |  `Value of U.t
    |  `None ] as 'a

  val take : [< (fieldinfo, fieldinfo, typ) offs ] list -> U.t -> U.t
  val inv : [< ('a, 'b, 'c) offs ] list -> [> ('b, 'a, 'c) offs ] list
  val of_var : ?f:string -> varinfo -> [ `Location of _ | `Value of _  | `None ] maybe_region
  val of_string : [ `S of string | `WS of int64 list ] -> [ `Location of _ ] maybe_region
  val of_lval : ?f:string -> lval -> [ `Location of _ | `Value of _  | `None ] maybe_region
  val of_expr : ?f:string -> exp -> [ `Value of _ | `None ] maybe_region
  val location : [ `Location of _ | `Value of _  | `None ] maybe_region -> U.t
  val compute_regions : unit -> unit
  val dot_voids : (U.t -> unit) -> U.t -> unit
  val containers_of_void : (typ -> U.t -> unit) -> U.t -> unit
  module H_call : sig
    type t
    val find : U.t -> t -> U.t
    val iter : (U.t -> unit) -> U.t -> t -> unit
  end
  val map : stmt -> H_call.t
  val arg_regions : ?f:string -> kernel_function -> lval option -> exp list -> U.t list * U.t list
  val param_regions : kernel_function -> U.t list * U.t list
  val relevant_region : ?f:string -> U.t -> bool
end

module Analysis (I' : sig val offs_of_key : Info.offs Info.H_field.t end) () : Analysis = struct
  module Separation = Separation ()

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
      | NoOffset        when acc <> []        -> Some acc
      | NoOffset                              -> None
      | Field (fi, off) when fi.fcomp.cstruct -> match_offset ~acc:(`Field fi :: acc) off
      | Field (fi, off)                       -> match_offset
                                                   ~acc:(`Container_of_void (Ty.normalize fi.ftype) :: acc)
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
        | TComp (ci, _ ,_), TComp (ci', _, _)
          when ci.cstruct && ci'.cstruct && Compinfo.equal ci ci' -> true
        | _ -> false
      ->
      opt_map (fun off -> mptr, off) @@ match_offset off
    | _ -> None

  let match_container_of2 =
    function
    | BinOp ((PlusPI | IndexPI),
             { enode  = CastE (pstr, _, e); _ },
             { enode = Const (CInt64 (c, IULongLong, _)); _ }, _)   ->
      begin match unrollType pstr, unrollType (typeOf e) with
      | TComp (ci, _, _), (TPtr _ | TArray _ as ty) when ci.cstruct ->
        begin try
          Some (e, H_field.find I'.offs_of_key (ci, ty, c))
        with
        | Not_found -> None
        end
      | _ -> None
      end
    | _ -> None

  let match_dot =
    function
    | BinOp ((PlusPI | IndexPI),
             { enode = CastE (chrptr, _, e); _ },
             { enode = Const (CInt64 (c, IULongLong, _)); _ }, _)
      when isCharPtrType chrptr && isPointerType (typeOf e) ->
      let ty = Ast_info.pointed_type (typeOf e) in
      begin match unrollType ty with
      | TComp (ci, _ ,_) ->
        begin try
          Some (e, H_field.find I'.offs_of_key (ci, uintType, c))
        with
        | Not_found -> None
        end
      | _ -> None
      end
    | _ -> None

  (* Notice about handling integers used as pointers: they don't have regions, i.e. it's unsound(!),
     we just create a fresh region each time we cast an integer to a pointer, but this is done
     separately for each case below *)
  let deref u = if isPointerType (U.repr u).R.typ then `Value (deref u) else `None

  let resolve_addressible addrof typ u () =
    if addrof && not @@ isArrayType typ then deref u
    else if isArrayType typ             then `Value u
    else                                     `None

  type ('a, 'b, 'c) offs = [ `Field of 'a | `Container of 'b | `Container_of_void of 'c ]

  let rec take offs u =
    match offs with
    | []                            -> u
    | `Field fi ::             offs -> take offs @@ dot u fi
    | `Container fi ::         offs -> take offs @@ container u fi
    | `Container_of_void ty :: offs -> take offs @@ container_of_void u ty

  let inv offs =
    let rec loop acc =
      function
      | []                            -> acc
      | `Container fi ::         offs -> loop (`Field fi :: acc) offs
      | `Field fi ::             offs -> loop (`Container fi :: acc) offs
      | `Container_of_void ty :: offs -> loop (`Container_of_void ty :: acc) offs
    in
    loop [] offs

  let memoize ~find ~replace h fn ?f x =
    try find h x
    with
    | Not_found ->
      let r = fn ?f x in
      replace h x r;
      r

  type 'a maybe_region =
    [< `Location of U.t * (unit -> [ `None | `Value of U.t ])
    |  `None
    |  `Value of U.t ] as 'a

  (* Also used to retrieve return regions, only use from the inside(!) *)
  let rec of_var ?f x =
    let of_var =
      let open! H_v in
      memoize ~find ~replace h_var @@
      fun ?f v ->
      if not (isStructOrUnionType v.vtype || isArrayType v.vtype || v.vaddrof || isPointerType v.vtype)
      then `None
      else
        let u =
          let typ =
            if (v.vaddrof && not @@ isArrayType v.vtype) || isStructOrUnionType v.vtype
            then Ty.normalize v.vtype
            else Ty.deref_once v.vtype
          in
          U.of_repr @@
          match typ, f with
          | TPtr (TFun (rt, _ ,_ ,_), _) , _
            when not (isStructOrUnionType rt)               -> R.poly ("!" ^ v.vname ^ "!") v.vname typ
          | TPtr (TFun _, _), _                             -> R.local ("!" ^ v.vname ^ "!") v.vname typ
          | _, Some f
            when v.vformal
              && not (isStructOrUnionType typ || v.vaddrof) -> R.poly f v.vname typ
          | _, Some f when v.vformal                        -> R.local f v.vname typ
          | _, _ when v.vglob                               -> R.global v.vname typ
          | _, Some f                                       -> R.local f v.vname typ
          | _                                               -> Console.fatal "Region.of_var: a local or formal \
                                                                              variable should be supplied with \
                                                                              function name: %s"
                                                                 v.vname
        in
        if isStructOrUnionType v.vtype || isArrayType v.vtype || v.vaddrof
        then `Location (u, resolve_addressible v.vaddrof v.vtype u)
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
        U.of_repr @@ R.global ("\"" ^ s' ^ "\"") (match s with `S _ -> charType | `WS _ -> theMachine.wcharType)
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
      | Some f -> R.local f name ty
      | None   -> R.global name ty
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
        let u = container_of_void (location (of_lval lv')) fi.ftype in
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
      if not @@ isPointerType @@ typeOf e
      then `None
      else
        let cast ty e =
          let ty' = typeOf e in
          let r = of_expr e in
          if Ty.compatible ty ty' then r
          else (* Both can't be void */union since they are compatible! *)
            let r = value ty' r in
            match unrollType ty, unrollType ty' with
            | (TVoid _ | TComp ({ cstruct = false; _ }, _, _)), _  -> `Value (dot_void r)
            | ty, (TVoid _ | TComp ({ cstruct = false; _ }, _, _)) -> `Value (container_of_void r @@ Ty.deref_once ty)
            | ty, ty' ->
              match Ci.(match_deep_first_subfield_of ty ty', match_deep_first_subfield_of ty' ty) with
              | Some offs, _                                       -> `Value (take offs r)
              | _,         Some offs                               -> `Value (take (inv offs) r)
              | _                                                  -> `Value (container_of_void
                                                                                (dot_void r)
                                                                                (Ty.deref_once ty))

        in
        match match_container_of1 e.enode, match_container_of2 e.enode, match_dot e.enode with
        | Some (e, offs), _, _
        | _, Some (e, offs), _              -> `Value (take (inv offs) @@ value (typeOf e) @@ of_expr e)
        | _, _, Some (e, offs)              -> `Value (take offs @@ value (typeOf e) @@ of_expr e)
        | None, None, None                  ->
          match e.enode with
          | Const (CStr s)                  -> `Value (value (typeOf e) @@ of_string @@ `S s)
          | Const (CWStr ws)                -> `Value (value (typeOf e) @@ of_string @@ `WS ws)
          | Const (CInt64 _ | CEnum _
                  | CChr _ | CReal _ )      -> assert false
          | Lval lv                         -> `Value (location @@ of_lval lv)
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

  let h_params = H_k.create 1024

  let h_maps = H_stmt.create 1024

  let param_regions =
    let module Kf = Kernel_function in
    let h_var = H_v.create 512 in
    let maps = H_k.create 512 in
    let unify_pointed u' u =
      let h = H'.create () in
      let rec unify_pointed ?(_retain_h=H'.clear h) u' u =
        try
          ignore @@ H'.find u' h
        with
        | Not_found ->
          let open! Separation in
          arrows (fun fi u' -> unify (arrow u fi) u') u';
          derefs (fun u' -> unify (deref u) u') u';
          H'.add u u h;
          dots (fun fi u' -> unify_pointed u' @@ dot u fi) u';
          dot_voids (fun u' -> unify_pointed u' @@ dot_void u) u';
          containers (fun fi u' -> unify_pointed u' @@ container u fi) u';
          containers_of_void (fun ty u' -> unify_pointed u' @@ container_of_void u ty) u'
      in
      unify_pointed u' u
    in
    fun kf ->
      let params = Kf.get_formals kf in
      let retval =
        if isVoidType @@ Kf.get_return_type kf
        then []
        else [Kf.get_vi kf]
      in
      let comp_regions vi =
        let u', u =
          let open H_v in
          let f = Kf.get_name kf in
          location @@ of_var ~f vi,
          memo h_var vi (fun vi -> U.of_repr @@ R.poly f (vi.vname ^ "'") @@ Ty.normalize vi.vtype)
        in
        let map = H_k.memo maps kf (fun _ -> H'.create ()) in
        accomodate ~map [u'] ~on:[u];
        unify_pointed u' u;
        match unrollType vi.vtype with
        | TComp (ci, _, _) -> List.map (swap take @@ u) (Ci.all_regions ci)
        | ty -> Console.fatal "Region.Analysis.comp_regions: not a composite param, but %a" pp_typ ty
      in
      map_pair
        (List.concat_map
           (fun vi ->
              match of_var vi with
              | `Location (_, get)                ->
                begin match get () with
                | `Value u                        -> [u]
                | `None                           -> []
                end
              | `Value u                          -> [u]
              | `None
                when isStructOrUnionType vi.vtype -> comp_regions vi
              | `None                             -> []))
        (retval, params)

  let arg_regions ?f kf lvo exprs =
    let retr =
      let rtyp = Ty.normalize @@ Kernel_function.get_return_type kf in
      if isVoidType rtyp
      then []
      else
        match lvo, rtyp with
        | None,    TPtr _              -> [value ?f rtyp `None]
        | None,    TComp (ci, _, _)    -> List.map (swap take @@ value ?f rtyp `None) (Ci.all_regions ci)
        | None,    _                   -> []
        | Some lv, TPtr _              -> [value ?f rtyp @@ of_lval ?f lv]
        | Some lv, TComp (ci, _, _)    -> List.map (swap take @@ location @@ of_lval ?f lv) (Ci.all_regions ci)
        | Some _,  _                   -> []
    in
    retr,
    List.concat_map
      (fun e ->
         match of_expr ?f e with
         | `Value u                    -> [u]
         | `None                       ->
           match unrollType (typeOf e), e.enode with
           | TComp (ci, _, _), Lval lv -> List.map (swap take @@ location @@ of_lval ?f lv) (Ci.all_regions ci)
           | TComp _,          _       -> Console.fatal "Unexpected non-lvalue struct expression `%a'"
                                            pp_exp e
           | _                         -> [])
      exprs

  let unify_exprs ?f e1 e2 =
    let unify_comps ci lv1 lv2 =
      let u1, u2 = map_pair (location % of_lval ?f) (lv1, lv2) in
      List.iter (fun offs -> uncurry unify @@ map_pair (take offs) (u1, u2)) (Ci.all_regions ci)
    in
    match e1.enode, e2.enode, unrollType (typeOf e1) with
    | Lval lv1, Lval lv2, TComp (ci, _, _)    -> unify_comps ci lv1 lv2
    | _                                       ->
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
    let first_substruct fi = reify arrows (fun add fi' u -> if Fieldinfo.equal fi fi' then add u) in
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
               | TComp ({ cfields = fi :: _; cstruct = true; _ }, _ ,_)  -> first_substruct fi u'
               | TComp ({ cstruct = false; _ }, _ ,_)                    -> assert false
               | _                                                       -> []
               end >>= fun u' ->
               dot_voids u' >>= fun u' ->
               [unify u u']
             else
               containers_of_void u >>= fun u' ->
               let ty', n' = Ty.deref (U.repr u').R.typ in
               (if n' = n then [u'] else []) >>= fun u' ->
               derefs u' >>= fun u' ->
               derefs u >>= fun u ->
               containers_of_void u >>= fun u ->
               let ty'', n'' = Ty.deref (U.repr u).R.typ in
               if n'' = n' - 1 && Ty.compatible ty' ty'' then [unify u u'] else []
           in
           List.iter (on (relevant_region ?f) unify % U.of_repr) rs)
        (R.all_void_xs ())

  let replay_on_call ~stmt ?f kf lvo args =
    let (ret_ext_regions, param_regions), (ret_int_regions, arg_regions) =
      H_k.memo h_params kf param_regions, arg_regions ?f kf lvo args
    in
    let param_regions, arg_regions =
      let open! List in
      let pair = param_regions, arg_regions in
      map_pair (take @@ uncurry min @@ map_pair length pair) pair
    in
    let map = H_stmt.memo h_maps stmt (fun _ -> H'.create ()) in
    replay ~map ret_ext_regions ~on:ret_int_regions;
    replay ~map param_regions ~on:arg_regions

  let expr_of_lval =
    let cache = H_l.create 4096 in
    fun ~loc lv -> H_l.memo cache lv (fun lv -> new_exp ~loc @@ Lval lv)

  open Visitor

  class one_function_visitor fundec = object
    inherit frama_c_inplace
    method! vfunc fd =
      if may_map (fun fd' -> Fundec.equal fd fd') ~dft:false fundec
      then DoChildren
      else SkipChildren
  end

  class unifier () fundec =
    let f = opt_map (fun fd -> fd.svar.vname) fundec in
    object
      inherit frama_c_inplace
      inherit! one_function_visitor fundec

      method! vlval lv = ignore @@ of_lval ?f lv; DoChildren
      method! vexpr e =
        ignore @@ of_expr ?f e;
        DoChildrenPost
          (tap @@ fun e ->
           match e.enode with
           | BinOp ((Eq | Ne), e1, e2, _) -> unify_exprs ?f e1 e2
           | _                            -> ())
      method! vstmt _ =
        DoChildrenPost
          (tap @@ fun stmt ->
             match stmt.skind with
             | Instr (Set (lv, e, loc))                       -> unify_exprs ?f (expr_of_lval ~loc lv) e
             | Instr
                 (Call
                    (lvo,
                     { enode = Lval (Var vi, NoOffset); _  },
                     args, _))
               when Kf.mem vi                                 -> replay_on_call ~stmt ?f (Globals.Functions.get vi)
                                                                   lvo args
             | Instr (Call (lvo, _, args, _))                 -> List.iter
                                                                   (fun kf -> replay_on_call ~stmt ?f kf lvo args)
                                                                   (Analyze.filter_matching_kfs lvo args)
             | Return (Some e, loc) when has_some fundec      -> unify_exprs ?f
                                                                   (expr_of_lval ~loc (var (the fundec).svar)) e
             | _                                              -> ())

      method start = ()
      method finish =
        unify_voids f;
        may
          (fun fd ->
             let kf = Globals.Functions.get fd.svar in
             H_k.replace h_params kf @@ param_regions kf)
          fundec
    end

  let pp =
    let h_lv = H_l.create 1024 in
    let h_exp = H_e.create 1024 in
    let pp_region_of fmttr pp_e e =
      function
      | `None            -> ()
      | `Location (u, _) -> Format.fprintf fmttr "%a@@%a;@ " pp_e e R.pp @@ U.repr u
      | `Value u         -> Format.fprintf fmttr "%a\\%a;@ " pp_e e R.pp @@ U.repr u
    in
    fun fmttr fundec ->
      let f = opt_map (fun f -> f.svar.vname) fundec in
      H_l.clear h_lv;
      H_e.clear h_exp;
      let vis = object
        inherit frama_c_inplace
        inherit! one_function_visitor fundec

        method! vlval _ =
          DoChildrenPost (tap @@ fun lv -> H_l.memo h_lv lv @@ pp_region_of fmttr pp_lval lv % of_lval ?f)
        method! vexpr _ =
          DoChildrenPost (tap @@ fun e -> H_e.memo h_exp e @@ pp_region_of fmttr pp_exp e % of_expr ?f)
      end in
      match fundec with
      | Some fundec -> ignore @@ visitFramacFunction vis fundec
      | None        -> visitFramacFile vis (Ast.get ())

  module Fixpoint =
    Fixpoint.Make
      (struct
        module E = struct
          type t = fundec
          let pp fmttr fundec = pp fmttr (Some fundec)
        end

        type t = unit

        let get _ _ fundec = fundec
        let flag = R.flag
      end)

  let compute_regions () =
    let sccs = Analyze.condensate () in
    visitFramacFile (new unifier () None :> frama_c_visitor) @@ Ast.get ();
    Fixpoint.visit_until_convergence ~order:`topological (fun () f -> new unifier () @@ Some f) () sccs;
    unify_voids None

  let dot_voids = dot_voids
  let containers_of_void = containers_of_void

  module H_call = struct
    type t = H'.t
    let find = H'.find
    let iter = H'.iter
  end

  let map = H_stmt.find h_maps

  let param_regions kf = H_k.memo h_params kf param_regions
end


