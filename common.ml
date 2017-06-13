(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Format

module type Hashed = Hashtbl.HashedType

module type Ordered = Map.OrderedType

module type Printable = sig
  type t
  val pp : formatter -> t -> unit
end

module type Hashed_ordered = sig
  include Hashed
  include Ordered with type t := t
end

module type Hashed_printable = sig
  include Hashed
  include Printable with type t := t
end

module type Ordered_printable = sig
  include Ordered
  include Printable with type t := t
end

module type Hashed_ordered_printable = sig
  include Hashed
  include Ordered with type t := t
  include Printable with type t := t
end

module Console = Options

let (%) f g x = f (g x)
let (%%) f g x y = f (g x y)
let (%>) f g x = g (f x)
let const f _x = f
let const' f x _y = f x
let curry f a b = f (a, b)

let map_fst f (a, b) = f a, b
let map_snd f (a, b) = a, f b
let map_pair f (a, b) = f a, f b

module List = struct
  include List

  let take n l =
    let rec loop n dst =
      function
      | h :: t when n > 0 -> loop (n - 1) (h :: dst) t
      | _                 -> List.rev dst
    in
    loop n [] l

  let rec find_map f =
    function
    | []              -> None
    | x :: xs         ->
      match f x with
      | Some _ as res -> res
      | None          -> find_map f xs

  let group_by same =
    fold_left
      (fun acc x ->
         match acc with
         | []                         -> [[x]]
         | g :: tl when same (hd g) x -> (x :: g) :: tl
         | g :: tl                    -> [x] :: g :: tl)
      [] %>
    rev_map rev

  let concat_map f =
    let rec aux acc =
      function
      | []       -> rev acc
      | hd :: tl -> aux (rev_append (f hd) acc) tl
    in
    aux []
end

module String = struct
  include String

  let explode s =
    let rec next acc i =
      if i >= 0 then next (s.[i] :: acc) (i - 1)
      else           acc
    in
    next [] (String.length s - 1)

  let implode ls =
    let s = Bytes.create (List.length ls) in
    List.iteri (Bytes.set s) ls;
    Bytes.to_string s
end

open Cil_types
open Cil

open Extlib

module Ty = struct
  let is_union ty =
    match[@warning "-4"] unrollType ty with
    | TComp ({ cstruct = false; _ }, _, _) -> true
    | _                                    -> false

  let rec normalize ty =
    let open Ast_info in
    match typeDeepDropAllAttributes @@ unrollTypeDeep ty with
    | TVoid []
    | TInt (_, [])
    | TFloat (_, []) as ty                 -> ty
    | TPtr (TArray _ as ty, [])            -> TPtr (normalize @@ element_type ty, [])
    | TPtr (ty, [])                        -> TPtr (normalize ty, [])
    | TComp ({ cstruct = false; _ }, _, _) -> TVoid []
    | TArray (_, _, _, []) as ty           -> TPtr (normalize @@ element_type ty, [])
    | TFun (ty, argso, vararg, [])         -> TPtr (TFun (normalize ty,
                                                          opt_map
                                                            (List.map
                                                               (fun (n, ty, _) -> n, normalize ty, []))
                                                            argso,
                                                          vararg,
                                                          []),
                                                    [])
    | TComp ({ cstruct = true; _ } as ci,
             cache, [])                    -> TComp (ci, cache, [])
    | TEnum (ei, [])                       -> TInt (ei.ekind, [])
    | TBuiltin_va_list []                  -> TPtr (TVoid [], [])
    | TVoid            (_ :: _)
    | TInt (_,          _ :: _)
    | TFloat (_,        _ :: _)
    | TPtr (_,          _ :: _)
    | TArray (_, _, _,  _ :: _)
    | TFun (_, _, _,    _ :: _)
    | TComp (_, _,      _ :: _)
    | TEnum (_,         _ :: _)
    | TBuiltin_va_list (_ :: _)
    | TNamed _                             -> assert false

  let deref_once ty =
    let open Ast_info in
    match unrollType ty with
    | TPtr _ as ty             -> normalize @@ pointed_type ty
    | TArray _                 -> normalize @@ element_type ty
    | TVoid _
    | TInt _
    | TFloat _
    | TFun _
    | TComp _
    | TEnum _
    | TBuiltin_va_list _ as ty -> normalize ty
    | TNamed _                 -> assert false


  let deref =
    let rec aux n ty =
      let open Ast_info in
      match unrollType ty with
      | TVoid _
      | TInt _
      | TFloat _
      | TFun _
      | TComp _
      | TEnum _
      | TBuiltin_va_list _ as ty  -> normalize ty, n
      | TNamed _                  -> assert false
      | TPtr _ as ty              -> aux (n + 1) (normalize @@ pointed_type ty)
      | TArray _ as ty when n = 0 -> aux 1 (normalize @@ element_type ty)
      | TArray _ as ty            -> aux n (normalize @@ element_type ty)
    in
    aux 0

  let compatible ty1 ty2 = Cil_datatype.Typ.equal (normalize ty1) (normalize ty2)

  let rec ref ty n =
    if n <= 0 then ty
    else           ref (TPtr (ty, [])) (n - 1)
end

module Ci = struct
  let match_deep_first_subfield_of typ' =
    let rec loop acc typ =
      if Ty.compatible typ typ' then Some (List.rev acc)
      else
        let union fields = List.find_map (fun fi -> loop (`Container_of_void fi.ftype :: acc) fi.ftype) fields in
        match[@warning "-4"] unrollType typ with
        | TComp ({ cstruct = true; cfields = fi :: _; _ }, _, _) -> loop (`Field fi :: acc) fi.ftype
        | TComp ({ cstruct = true; cfields = []; _ }, _, _)      -> None
        | TComp ({ cstruct = false; cfields; _ }, _, _)          -> union cfields
        | _                                                      -> None
    in
    loop [] %>
    opt_map
      List.(group_by
              (curry @@
               function `Field _, `Field _ | `Container_of_void _, `Container_of_void _ -> true | _ -> false) %>
            concat_map
              (function `Field _ :: _ as l -> l | `Container_of_void _ as e :: _ -> [e] | [] -> assert false) %>
            rev)

  let all_offsets ci =
    let open List in
    let rec do_struct path ci =
      concat_map
        (fun fi ->
           match[@warning "-4"] unrollType fi.ftype with
           | TComp (ci, _, _)  -> do_ci (`Field fi :: path) ci
           | _ when fi.faddrof -> [`Field fi :: path, None]
           | _                 -> [path, Some fi])
        ci.cfields
    and do_union path ci =
      concat_map
        (fun fi ->
           let container_of_void ty = `Container_of_void ty in
           match[@warning "-4"] unrollType fi.ftype with
           | TComp (ci, _, _) as ty -> do_ci (container_of_void ty :: path) ci
           | ty                     -> [container_of_void ty :: path, None])
        ci.cfields
    and do_ci path = (if ci.cstruct then do_struct else do_union) path in
    map (map_fst rev) @@ do_ci [] ci

  let all_regions ci =
    let open Cil_datatype in
    let open List in
    all_offsets ci |>
    group_by
      (fun (path1, _) (path2, _) ->
         for_all2
           (curry @@
            function
            | `Field fi1,             `Field fi2             -> Fieldinfo.equal fi1 fi2
            | `Container_of_void ty1, `Container_of_void ty2 -> Typ.equal ty1 ty2
            | _                                              -> false)
           path1 path2) |>
    map (fst % hd)
end

module Kf = struct
  let mem vi =
    try
      ignore @@ Globals.Functions.get vi; true
    with Not_found ->                     false
end
