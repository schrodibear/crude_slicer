(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Cil
open Cil_types
open Cil_printer
open Cil_datatype

open Extlib
open Common

module Representant = struct
  module Kind = struct
    type t = [ `Global | `Poly of string  | `Local of string | `Dummy ]

    let equal k1 k2 =
      match k1, k2 with
      | `Global,   `Global                       -> true
      | `Poly f1,  `Poly f2
      | `Local f1, `Local f2
        when String.equal f1 f2                  -> true
      | `Dummy,    `Dummy                        -> true
      | (`Global
        | `Poly _
        | `Local _
        | `Dummy), (`Global
                   | `Poly _
                   | `Local _
                   | `Dummy)                     -> false

    let choose k1 k2 =
      begin match k1, k2 with
      | (`Poly f1
        | `Local f1),  (`Poly f2
                       | `Local f2)
        when not (String.equal f1 f2)            -> Console.fatal
                                                      "Representant.Kind.choose: broken invariant: \
                                                       should not try unifying regions from diff. functions: %s and %s"
                                                      f1 f2
      | `Dummy, `Dummy                           ->  Console.fatal
                                                       "Representant.Kind.choose: broken invariant: \
                                                        dummy regions should be immediately unified with non-dummy ones"
      | (`Global
        | `Poly _
        | `Local _
        | `Dummy),     (`Global
                       | `Poly _
                       | `Local _
                       | `Dummy)                 -> ()
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

  let global name typ = Flag.report flag; { name; typ; kind = `Global }
  let poly fname name typ = Flag.report flag; { name = fname ^ "::" ^ name; typ; kind = `Poly fname }
  let local fname name typ = Flag.report flag; { name = fname ^ ":::" ^ name; typ; kind = `Local fname }
  let dummy name typ = { name; typ; kind = `Dummy }
  let template =
    let counter = ref ~-1 in
    fun { name; typ; kind } ->
      let open Kind in
      match kind with
      | `Poly _                     -> incr counter; dummy ("dummy" ^ string_of_int !counter) typ
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
    Flag.report flag;
    { name = r.name ^ "->" ^ fi.fname; typ = Ast_info.pointed_type fi.ftype; kind = r.kind }

  let deref r =
    if not (isPointerType r.typ) then
      Console.fatal "Representant.deref: not a pointer region: %s : %a" r.name pp_typ r.typ;
    Flag.report flag;
    { name = "*(" ^ r.name ^ ")"; typ = Ast_info.pointed_type r.typ; kind = r.kind }

  let check_detached f fi =
    if not (isStructOrUnionType fi.ftype || isArrayType fi.ftype || fi.faddrof) then
      Console.fatal
        "%s: not a struct/union, array or addressed field: %s.%s : %a (&: %B)"
        f fi.fname fi.fcomp.cname pp_typ fi.ftype fi.faddrof

  let dot r fi =
    check_field "Representant.dot" r fi;
    check_detached "Representant.dot" fi;
    Flag.report flag;
    { name = r.name ^ "." ^ fi.fname; typ = fi.ftype; kind = r.kind }

  let container r fi =
    check_detached "Representant.container" fi;
    if not (Typ.equal fi.ftype r.typ) then
      Console.fatal
        "Representant.container: illegal use of `container_of': %s.%s : %a vs. %s : %a"
        fi.fname fi.fcomp.cname pp_typ fi.ftype r.name pp_typ r.typ;
    if not fi.fcomp.cstruct then
      Console.fatal "Representant.container: container should be a structure: %s" fi.fcomp.cname;
    Flag.report flag;
    { name = "(" ^ r.name ^ ", " ^ fi.fcomp.cname ^ "." ^ fi.fname ^ ")";
      typ = TComp (fi.fcomp, empty_size_cache (), []);
      kind = r.kind }

  let dot_void r = Flag.report flag; { name = r.name ^ ".void"; typ = voidType; kind = r.kind }

  let container_of_void r typ =
    let name =
      match unrollType typ with
      | TComp (ci, _, _) when ci.cstruct -> ci.cname
      | TComp (ci, _, _)                 -> Console.fatal
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
    Flag.report flag;
    { name = "(" ^ r.name ^ ", " ^ name ^ ".void)"; typ; kind = r.kind }

  let pp fmttr r =
    Format.fprintf fmttr "{ %s : %a (%a) }" r.name pp_typ r.typ Kind.pp r.kind
end

module type Representant = sig
  module Kind : sig type t end
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val choose : t -> t -> [> `First | `Second | `Any ]
end

module type Unifiable = sig
  type t
  type repr
  val of_repr : repr -> t
  val unify : t -> t -> unit
  val repr : t -> repr
end

module Make_unifiable (R : Representant) : Unifiable with type repr = R.t = struct
  type t = R.t
  type repr = R.t
  let of_repr = id

  module H = Hashtbl.Make (R)

  let reprs = H.create 2048
  let ranks = H.create 2048

  let rec repr r =
    match repr (H.find reprs r) with
    | r' ->
      H.replace reprs r r';
      r'
    | exception Not_found -> r

  let rank r = try H.find ranks r with Not_found -> 0

  let unify r1 r2 =
    let r1, r2 = repr r1, repr r2 in
    if R.equal r1 r2 then ()
    else
      let k1, k2 = rank r1, rank r2 in
      match R.choose r1 r2 with
      | `First ->
        H.replace reprs r2 r1;
        if k1 <= k2 then H.replace ranks r1 (k2 + 1)
      | `Second ->
        H.replace reprs r1 r2;
        if k2 <= k1 then H.replace ranks r2 (k1 + 1)
      | `Any when k1 < k2 ->
        H.replace reprs r1 r2
      | `Any when k2 < k1 ->
        H.replace reprs r2 r1
      | `Any ->
        H.replace reprs r1 r2;
        H.replace ranks r2 (k1 + 1)
end

module Make_hashmap (R : Representant) (U : Unifiable with type repr = R.t) : sig
  type t
  val create : unit -> t
  val add : U.t -> U.t -> t -> unit
  val add' : t -> U.t -> U.t -> unit
  val find : U.t -> t -> U.t
  val find_or_call : create:(R.t -> R.t) -> call:(U.t -> U.t -> unit) -> t -> U.t -> U.t
  val iter : (U.t -> unit) -> U.t -> t -> unit
  val clear : t -> unit
end = struct
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

module Make_pair_hashmap (R : Representant) (U : Unifiable with type repr = R.t) (K : Hashtbl.HashedType) : sig
  type t
  val create : unit -> t
  val add : U.t -> K.t -> U.t -> t -> unit
  val add' : t -> U.t -> K.t -> U.t -> unit
  val find : U.t -> K.t -> t -> U.t
  val find_or_call : create:(R.t -> K.t -> R.t) -> call:(U.t -> K.t -> U.t -> unit) -> t -> U.t -> K.t -> U.t
  val iter : (K.t -> U.t -> unit) -> U.t -> t -> unit
  val clear : t -> unit
end = struct
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

module Unifiable = Make_unifiable (Representant)

module H_f = Make_pair_hashmap (Representant) (Unifiable) (Fieldinfo)
module H_t = Make_pair_hashmap (Representant) (Unifiable) (Typ)
module H' = Make_hashmap (Representant) (Unifiable)

module R = Representant
module U = Unifiable

let global = R.global
let poly = R.poly
let local = R.local

module Separation : sig
  val arrow : U.t -> fieldinfo -> U.t
  val deref : U.t -> U.t
  val dot : U.t -> fieldinfo -> U.t
  val dot_void : U.t -> U.t
  val container : U.t -> fieldinfo -> U.t
  val container_of_void : U.t -> typ -> U.t
  val unify : U.t -> U.t -> unit
  val duplicate : map:H'.t -> ?clone:U.t -> U.t -> Unifiable.t
  val replay : map:H'.t -> U.t list -> on:U.t list -> unit
end = struct
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
  let container_of_void =
    H_t.find_or_call ~create:R.container_of_void ~call:(fun u _ u' -> H'.add u u' h_dot_void) h_container_of_void

  type 'k handler2 = (U.t -> 'k -> U.t) -> U.t -> 'k -> U.t -> unit

  let handle_all ~handle1 ~(handle2:< f : 'k. 'k handler2; ..>) u1 u2 =
    let handle2 f u k u' = handle2#f f u k u' in
    H_f.iter (handle2 arrow u2) u1 h_arrow;
    H'.iter (handle1 deref u2) u1 h_deref;
    H_f.iter (handle2 dot u2) u1 h_dot;
    H'.iter (handle1 dot_void u2) u1 h_dot_void;
    H_f.iter (handle2 container u2) u1 h_container;
    H_t.iter (handle2 container_of_void u2) u1 h_container_of_void

  let rec unify =
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
    fun ?(max_count=3) ?(retain_cache=Typ.Hashtbl.clear cache) u1 u2 ->
      let r1 = U.repr u1 and r2 = U.repr u2 in
      if not (R.equal r1 r2) then
        let t1 = unrollType r1.R.typ and t2 = unrollType r2.R.typ in
        if need_cast t1 t2 then
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

  let unify = unify ~max_count:(Options.Region_depth.get ()) ?retain_cache:None

  let rec duplicate ~map ?clone u =
    let handle1 f u u' = ignore @@ duplicate ~map ~clone:(f u) u'
    and handle2 = object
      method f : 'k. 'k handler2 = fun f u k u' -> ignore @@ duplicate ~map ~clone:(f u k) u'
    end in
    try
      H'.find u map
    with
    | Not_found ->
      let u' = may_map id ~dft:(U.of_repr @@ R.template (U.repr u)) clone in
      H'.add u u' map;
      handle_all ~handle1 ~handle2 u u';
      u'

  let replay ~map regs ~on =
    H'.clear map;
    List.iter2 unify on (List.map (duplicate ~map) regs)
end

module Info = Info.Make (R) (U) ()

module H_field = Info.H_field

module Analysis (I : sig val fields_of_key : fieldinfo list H_field.t end) : sig
end = struct
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

  open Separation

  let rec of_var ?f v =
    let resolve u =
      if isStructOrUnionType v.vtype || isArrayType v.vtype || v.vaddrof then
        `Location (u, if v.vaddrof then fun () -> deref u else fun () -> u)
      else
        `Value u
    in
    try
      resolve @@ H_v.find h_var v
    with
    | Not_found ->
      if not (isStructOrUnionType v.vtype || isArrayType v.vtype || v.vaddrof || isPointerType v.vtype) then
        `None
      else
        let u =
          let typ =
            if v.vaddrof || isStructOrUnionType v.vtype then v.vtype
            else Ast_info.pointed_type v.vtype
          in
          U.of_repr @@
          match unrollType v.vtype, f with
          | TFun (rt, _ ,_ ,_), _ when not (isStructOrUnionType rt) -> R.poly v.vname v.vname typ
          | TFun _, _ -> R.local v.vname v.vname typ
          | _, Some f when v.vformal && not (isStructOrUnionType v.vtype) -> R.poly f v.vname typ
          | _, Some f when v.vformal -> R.local f v.vname typ
          | _, _ when v.vglob -> R.global v.vname typ
          | _, Some f -> R.local f v.vname typ
          | _ ->
            Console.fatal "Region.of_var: a local o formal variable should be supplied with function name: %s" v.vname
        in
        H_v.replace h_var v u;
        resolve u
  and of_string s =
    let resolve u = `Location (u, fun () -> deref u)
    try
      resolve @@ H_s.find h_str s
    with
    | Not_found ->
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
      H_s.replace h_str s u;
      resolve u
  and value =
    function
    | `Location (_, get) -> get ()
    | `Value u -> u
    | `None -> Console.fatal "Region.value: broken invariant: can't evaluate region"
  and of_lval ?f lv =
    let of_lval = of_lval ?f in
    let lv', off = removeOffsetLval lv in
    match off with
    | NoOffset ->
      begin match fst lv' with
      | Var v -> of_var v
      | Mem e ->
        let u = value (of_expr ?f e) in
        `Location (u, fun () -> deref u)
      end
    | Field (fi, NoOffset) when fi.fcomp.cstruct ->
      let u = value (of_lval lv') in
      if fi.faddrof || isStructOrUnionType fi.ftype || isArrayType fi.ftype then
        let u = dot u fi in
        `Location (u, if fi.faddrof then fun () -> deref u else fun () -> u)
      else
        `Location (u, fun () -> arrow u fi)
    | Field (fi, NoOffset) ->
      let u = container_of_void (value (of_lval lv')) (typeDeepDropAllAttributes @@ unrollType fi.ftype) in
      `Location (u, if isStructOrUnionType fi.ftype || isArrayType fi.ftype then fun () -> u else fun () -> deref u)
    | Index (_, NoOffset) ->
      let u = of_lval lv' in
      if isArrayType (typeOfLval lv) then u
      else
        let v = value u in
        `Location (v, fun () -> deref v)
    | _ -> Console.fatal "Region.of_lval: broken invariant: remaining offset after removeOffsetLval"
  and of_expr =
    let match_container_of1 =
      let rec match_offset ?(acc=[]) =
        function
        | NoOffset when acc <> [] -> Some acc
        | NoOffset -> None
        | Field (fi, off) -> match_offset ~acc:(fi :: acc) off
        | Index _ -> None
      in
      function
      | CastE (pstr,
               { enode = BinOp (MinusPI,
                                { enode = CastE (chrptr, mptr) },
                                { enode =
                                    CastE (size_t,
                                           { enode = AddrOf (Mem { enode = CastE (pstr', zero) }, off) }) },
                                _) })
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
    in
    let match_container_of2 =
      function
      | BinOp ((PlusPI | IndexPI), { enode  = CastE (pstr, e) }, { enode = Const (CInt64 (c, IULongLong, _)) }, _) ->
        begin match unrollType pstr, unrollType (typeOf e) with
        | TComp (ci, _, _), (TPtr _ | TArray _ as ty) when ci.cstruct ->
          begin try
            Some (e, H_field.find I.fields_of_key (ci, ty, c))
          with
          | Not_found -> None
          end
        | _ -> None
        end
      | _ -> None
    in
    fun ?f e ->
      let of_lval = of_lval ?f in
      let of_expr = of_expr ?f in
      match match_container_of1 e.enode, match_container_of2 e.enode with
      | Some (e, fis), _
      | _, Some (e, fis) ->
        let u = List.fold_left container (value (of_expr e)) fis in
        `Location (u, fun () -> u)
      | None, None ->
        match e.enode with
        | Const (CStr s) -> of_string (`S s)
        | Const (CWStr ws) -> of_string (`WS ws)
        | Lval lv -> of_lval lv
        | 
end


