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

module type With_containers = sig
  include Hashed_ordered_printable
  module H : FCHashtbl.S with type key := t
  module M : FCMap.S with type key := t
  module S : FCSet.S with type elt := t
end

module Console = Options

let (%) f g x = f (g x)
let (%%) f g x y = f (g x y)
let (%%%) f g x y z = f (g x y z)
let (%%%%) f g x y z t = f (g x y z t)
let (%>) f g x = g (f x)
let (!!) = Lazy.force
let const f _x = f
let const' f x _y = f x
let const2 c _ _ = c
let const3 c _ _ _ = c
let const4 c _ _ _ _ = c
let ignore2 _ _ = ()
let ignore3 _ _ _ = ()
let ignore4 _ _ _ _  = ()

let curry f a b = f (a, b)
let on cond f x = if cond x then f x else ()
let tap f e = f e; e

let map_fst f (a, b) = f a, b
let map_snd f (a, b) = a, f b
let map_pair f (a, b) = f a, f b

let some x = Some x

type (_, _) eq =
  | Refl : ('a, 'a) eq

module List = struct
  include List

  let cons' xs x = x :: xs

  let fold_left' f l acc = fold_left f acc l

  let take n l =
    let rec loop n dst =
      function
      | h :: t when n > 0 -> loop (n - 1) (h :: dst) t
      | _                 -> List.rev dst
    in
    loop n [] l

  let rec drop n =
    function
    | []           -> []
    | l when n = 0 -> l
    | _ :: es      -> drop (n - 1) es

  let split n l = take n l, drop n l

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

  let (>>=) l f = concat_map f l

  let reify iter f u =
    let r = ref [] in
    iter (f @@ fun u -> r := u :: !r) u;
    !r

  let singleton x = [x]
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
open Cil_datatype
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
    | TPtr (TFun (_, _, _, []) as ty, _)
    | (TFun (_, _, _, []) as ty)           -> TPtr (ty, [])
    | TPtr (TArray _ as ty, [])            -> TPtr (normalize @@ element_type ty, [])
    | TPtr (ty, [])                        -> TPtr (normalize ty, [])
    | TComp ({ cstruct = false; _ }, _, _) -> TVoid []
    | TArray (_, _, _, []) as ty           -> TPtr (normalize @@ element_type ty, [])
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

  let unbracket ty = if isArrayType ty then Ast_info.element_type ty else ty

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
      | TPtr (TFun _ as ty, _)    -> normalize ty, n + 1
      | TPtr _ as ty              -> aux (n + 1) (normalize @@ pointed_type ty)
      | TArray _ as ty when n = 0 -> aux 1 (normalize @@ element_type ty)
      | TArray _ as ty            -> aux n (normalize @@ element_type ty)
    in
    aux 0

  let compatible ty1 ty2 = Typ.equal (normalize ty1) (normalize ty2)

  let rec ref ty n =
    if n <= 0 then ty
    else           ref (TPtr (ty, [])) (n - 1)

  let rtyp_if_fun ty =
    match[@warning "-4"] unrollType ty with
    | TFun (rt, _, _, _) -> rt
    | _                  -> ty
end

module Ci = struct
  let match_deep_first_subfield_of typ' =
    let rec loop acc typ =
      if Ty.compatible typ typ' then Some (List.rev acc)
      else
        let union fields =
          List.find_map (fun fi -> let ty = Ty.unbracket fi.ftype in loop (`Container_of_void ty :: acc) ty) fields
        in
        match[@warning "-4"] unrollType typ with
        | TComp ({ cstruct = true; cfields = fi :: _; _ }, _, _) -> loop (`Field fi :: acc) (Ty.unbracket fi.ftype)
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
              (function `Field _ :: _ as l -> l | `Container_of_void _ :: _ as l -> [last l] | [] -> assert false))

  let goffsets ci =
    let open List in
    let rec do_struct path ci =
      concat_map
        (fun fi ->
           match[@warning "-4"] unrollType @@ Ty.unbracket fi.ftype with
           | TComp (ci, _, _)            -> do_ci (`Field fi :: path) ci
           | _ when fi.faddrof ||
                    isArrayType fi.ftype -> [`Field fi :: path, None]
           | _                           -> [path, Some fi])
        ci.cfields
    and do_union path ci =
      concat_map
        (fun fi ->
           let container_of_void ty = `Container_of_void (fi, ty) in
           match[@warning "-4"] unrollType @@ Ty.unbracket fi.ftype with
           | TComp ({ cstruct = false; _ } as ci, _, _)       -> do_union path ci
           | TComp ({ cstruct = true;  _ } as ci, _, _) as ty -> do_struct (container_of_void ty :: path) ci
           | ty                                               -> [container_of_void ty :: path, None])
        ci.cfields
    and do_ci path ci = (if ci.cstruct then do_struct else do_union) path ci in
    map (map_fst rev) @@ do_ci [] ci

  let norm_offset = List.map @@ function `Container_of_void (_, ty) -> `Container_of_void ty | `Field _ as o -> o

  let offsets ci =
    goffsets ci |>
    List.map @@ map_fst norm_offset

  let dots ci =
    let open List in
    offsets ci |>
    group_by
      (fun (path1, _) (path2, _) ->
         length path1 = length path2 &&
         for_all2
           (curry @@
            function
            | `Field fi1,             `Field fi2             -> Fieldinfo.equal fi1 fi2
            | `Container_of_void ty1, `Container_of_void ty2 -> Typ.equal ty1 ty2
            | _                                              -> false)
           path1 path2) |>
    map (fst % hd)

  let arrows ci =
    let open List in
    offsets ci |>
    concat_map
      (fun (path, fio) ->
         let is_pointer_type = isPointerType % Ty.normalize in
         match rev path, fio with
         | path,                       Some fi when is_pointer_type fi.ftype -> [rev @@ `Arrow fi :: path]
         | `Field fi :: _,             None    when is_pointer_type fi.ftype -> [path]
         | `Container_of_void ty :: _, None    when is_pointer_type ty       -> [path]
         | _                                                                 -> [])
end

module Offset = struct
  include Offset
  let rec of_offs =
    function
    | []                                             -> NoOffset
    | (`Field fi | `Container_of_void (fi, _)) :: os -> Field (fi, of_offs os)
end

module Exp = struct
  include Exp
  let underef_mem e =
    match[@warning "-4"] e.enode with
    | Lval (Mem e, NoOffset) -> e
    | _                      -> e
  module List_hashtbl = struct
    include Hashtbl
    let find_all h k = try find h k with Not_found -> []
  end

  let container_of =
    let mkCast newt e = mkCast ~overflow:Check ~force:true ~e ~newt in
    fun ~loc offs e ->
      let oty =
        TPtr
          ((let `Field fi | `Container_of_void (fi, _) = List.hd offs in TComp (fi.fcomp, empty_size_cache (), [])), [])
      in
      mkCast oty @@
      new_exp ~loc @@
      BinOp
        (MinusPI,
         mkCast charPtrType e,
         mkCast
           theMachine.typeOfSizeOf @@ mkAddrOf ~loc (Mem (mkCast oty @@ zero ~loc), Offset.of_offs offs),
         charPtrType)
end

module Stmt = struct
  include Stmt
  let lnum s = (fst @@ loc s).Lexing.pos_lnum
end

module Kf = struct
  include Kf

  let mem vi =
    try
      ignore @@ Globals.Functions.get vi; true
    with Not_found ->                     false

  let mem_definition vi =
    try
      Kernel_function.is_definition @@ Globals.Functions.get vi
    with
    | Not_found ->
      false

  let ensure_proto rtyp name argtys vararg =
    try
      ignore @@ Globals.Functions.find_by_name name
    with
    | Not_found ->
      let file = Ast.get () in
      let fs = empty_funspec () in
      let params = List.mapi (fun i ty -> "arg" ^ string_of_int i, ty, []) argtys in
      let vi = makeGlobalVar ~source:false name @@ TFun (rtyp, Some params, vararg, []) in
      let loc = Location.unknown in
      file.globals <- GFunDecl (fs, vi, loc) :: file.globals;
      Globals.Functions.add @@ Declaration (fs, vi, Some (List.map makeFormalsVarDecl params), loc)

  let retvar kf =
    match[@warning "-4"] (Kernel_function.find_return kf).skind with
    | Return (None, _)                                          -> None
    | Return (Some ({ enode = Lval (Var vi, NoOffset); _ }), _) -> Some vi
    | _                                                         -> Console.fatal "Kf.retvar: \
                                                                                  unexpected return statement"

  let stub_attr = "stub"
end
