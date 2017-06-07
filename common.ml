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
  let rec no_cast ty1 ty2 =
    not (need_cast ty1 ty2) ||
    match unrollType ty1, unrollType ty2 with
    | (TPtr _ as tptr1), (TPtr _  as tptr2)
      when Ast_info.(no_cast (pointed_type tptr1) (pointed_type tptr2)) -> true
    | (TArray _ as tarr1), (TArray _ as tarr2)
      when Ast_info.(no_cast (element_type tarr1) (element_type tarr2)) -> true
    | (TArray _ as tarr), (TPtr _ as tptr)
    | (TPtr _ as tptr), (TArray _ as tarr)
      when Ast_info.(no_cast (element_type tarr) (pointed_type tptr))   -> true
    | _                                                                 -> false
end

module Ci = struct
  let match_deep_first_subfield_of typ' =
    let rec loop acc typ =
      if Ty.no_cast typ typ' then Some (List.rev acc)
      else
        let union fields = List.find_map (fun fi -> loop (`Container_of_void fi.ftype :: acc) fi.ftype) fields in
        match unrollType typ with
        | TComp ({ cstruct = true; cfields = fi :: _ }, _, _) -> loop (`Field fi :: acc) fi.ftype
        | TComp ({ cstruct = true; cfields = [] }, _, _)      -> None
        | TComp ({ cstruct = false; cfields }, _, _)          -> union cfields
        | _                                                   -> None
    in
    loop [] %>
    opt_map
      List.(group_by
              (curry @@
               function `Field _, `Field _ | `Container_of_void _, `Container_of_void _ -> true | _ -> false) %>
            concat_map
              (function `Field _ :: _ as l -> l | `Container_of_void _ as e :: _ -> [e] | [] -> assert false) %>
            rev)
end
