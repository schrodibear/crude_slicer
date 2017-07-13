(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Format
open Pretty_utils
open Common
open Extlib

module type Reporting_bithashset = sig
  type elt
  type t
  val create : Flag.t -> t
  val clear : t -> unit
  val copy : Flag.t -> t -> t
  val add : elt -> t -> unit
  val import : from:t -> t -> unit
  val remove : elt -> t -> unit
  val sub : t -> from:t -> unit
  val mem : elt -> t -> bool
  val intersects : t -> t -> bool
  val iter : (elt -> unit) -> t -> unit
  val filter_inplace : (elt -> bool) -> t -> unit
  val fold : (elt -> 'b -> 'b) -> t -> 'b -> 'b
  val length : t -> int
  val is_empty : t -> bool
  val flag : t -> Flag.t
  val stats : unit -> Hashtbl.statistics
  val pp : Format.formatter -> t -> unit
end

module Make_reporting_bithashset (M : Hashed_printable) () : Reporting_bithashset with type elt = M.t =
struct
  type elt = M.t
  module H = Hashtbl.Make (M)
  module H' = Hashtbl.Make (struct type t = int let hash = id let equal : int -> _ -> _ = (=) end)

  let size = 5000

  let index, elem, stats =
    let h = H.create size and h' = H'.create size in
    let i = ref ~-1 in
    (fun e ->
       try
         H.find h e
       with
       | Not_found ->
         incr i;
         H.replace h e !i;
         H'.replace h' !i e;
         !i),
    (fun i ->
       try
         H'.find h' i
       with
       | Not_found -> failwith "Reporting_bithashset.elem: Can't find element"),
    fun () -> H.stats h

  type nonrec t = Bv.t * Flag.t
  let create f = Bv.create ~size false, f
  let clear (v, f) =
    if Bv.is_empty v then Flag.report f;
    Bv.clear v
  let copy f (v, _) = Bv.copy v, f
  let add e (v, f) =
    let i = index e in
    if not (Bv.get v i) then Flag.report f;
    Bv.set v i
  let import ~from:(from, _) (v, f) =
    if not (Bv.subset from v) then Flag.report f;
    Bv.union_into ~into:v from
  let remove e (v, f) =
    let i = index e in
    if Bv.get v i then Flag.report f;
    Bv.reset v i
  let sub (s, _) ~from:(from, f) =
    if Bv.inters from s then Flag.report f;
    Bv.sub_from ~from s
  let mem e (v, _) = Bv.get v (index e)
  let intersects (v1, _) (v2, _) = Bv.inters v1 v2
  let iter f (v, _) = Bv.iter_true v (fun i -> f (elem i))
  let filter_inplace f (v, fl) = Bv.filter v (fun i -> if not @@ f (elem i) then (Flag.report fl; false) else true)
  let fold f (v, _) x =
    let r = ref x in
    Bv.iter_true v (fun i -> r := f (elem i) !r);
    !r
  let length (v, _) = Bv.cardinal v
  let is_empty (v, _) = Bv.is_empty v
  let flag (_, f) = f
  let pp fmt = fprintf fmt "{%a}" (pp_iter ~sep:",@ " iter M.pp)
end

module type Set = sig
  type t
  type some
  type 'a kind
  val create : Flag.t -> t
  val add : 'a kind -> 'a -> t -> unit
  val add_some : some -> t -> unit
  val import : from:t -> t -> unit
  val flag : t -> Flag.t
  val copy : Flag.t -> t -> t
  val pp : Format.formatter -> t -> unit
end

type ('k, 's, _) hashmap = ..

module type Reporting_hashmap = sig
  module S : Set
  type key
  type t
  type ('k, 's, _) hashmap += W : (key, S.t, t) hashmap
  val create : Flag.t -> t
  val clear : t -> unit
  val copy : Flag.t -> t -> t
  val shallow_copy : Flag.t -> t -> t
  val add : key -> 'a S.kind -> 'a -> t -> unit
  val add_some : key -> S.some -> t -> unit
  val import : from:t -> t -> unit
  val import_values : key -> S.t -> t -> unit
  val remove : key -> t -> unit
  val mem : key -> t -> bool
  val iter : (key -> S.t -> unit) -> t -> unit
  exception Different_flag
  val filter_map_inplace : ?check:bool -> (key -> S.t -> S.t option) -> t -> unit
  val find : key -> t -> S.t
  val fold : (key -> S.t -> 'b -> 'b) -> t -> 'b -> 'b
  val length : t -> int
  val flag : t -> Flag.t
  val stats : t -> Hashtbl.statistics
  val pp : Format.formatter -> t -> unit
end

module Make_reporting_hashmap (K : Hashed_printable) (S : Set) :
  Reporting_hashmap with type key = K.t and module S = S = struct
  type key = K.t
  module S = S
  module H = Hashtbl.Make (K)
  type t = S.t H.t * Flag.t
  type ('k, 's, _) hashmap += W : (key, S.t, t) hashmap
  let create f =
    H.create 32, f
  let clear (h, f) =
    if H.length h > 0 then Flag.report f;
    H.clear h
  let copy f (h, _) =
    let r = H.copy h in
    H.filter_map_inplace (fun _ r -> Some (S.copy f r)) r;
    r, f
  let shallow_copy f (h, _) = H.copy h, f
  let add k kind e (h, f) =
    if not (H.mem h k) then (Flag.report f; H.replace h k (S.create f));
    S.add kind e (H.find h k)
  let add_some k e (h, f) =
    if not (H.mem h k) then (Flag.report f; H.replace h k (S.create f));
    S.add_some e (H.find h k)
  let import ~from:(from, _) (h, f) =
    H.iter
      (fun k from ->
         if not (H.mem h k) then (Flag.report f; H.replace h k (S.create f));
         S.import ~from (H.find h k))
      from
  let import_values k from (h, f) =
    if not (H.mem h k) then (Flag.report f; H.replace h k (S.create f));
    S.import ~from (H.find h k)
  let remove k (h, f) =
    if H.mem h k then Flag.report f;
    H.remove h k
  let mem k (h, _) = H.mem h k
  let iter f (h, _) =
    H.iter f h
  let find k (h, f) =
    try
      H.find h k
    with
    | Not_found ->
      let r = S.create f in
      Flag.report f;
      H.replace h k r;
      r
  exception Different_flag
  let filter_map_inplace ?(check=true) f (h, fl) =
    H.filter_map_inplace
      (fun e set ->
         let r = f e set in
         match r with
         | None   -> Flag.report fl; None
         | Some s -> if check && S.flag s != fl then raise Different_flag else (if s != set then Flag.report fl; r))
      h
  let fold f (h, _) x =
    H.fold f h x
  let length (h, _) = H.length h
  let flag (_, f) = f
  let stats (h, _) = H.stats h
  let pp fmt =
    fst %> fprintf fmt "{%a}" (pp_iter2 ~pre:"@[<2>" ~sep:";@]@\n@[<2>" ~suf:"@]" ~between:" <-@\n" H.iter K.pp S.pp)
end
