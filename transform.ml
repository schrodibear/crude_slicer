(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

[@@@warning "-48-44"]

open Cil
open Cil_types
open Visitor

open Extlib
open! Common
open Region

let rec to_offset =
  function
  | []                         -> NoOffset
  | `Field fi :: os            -> Field (fi, to_offset os)
  | `Container_of_void _ :: os -> to_offset os

let cache_offsets =
  let open List in
  let negate off = Integer.(rem (neg off) @@ add (max_unsigned_number @@ theMachine.theMachine.sizeof_ptr lsl 3) one) in
  let iter_rev_prefixes f =
    let rec loop acc =
      function
      | []      -> f acc
      | x :: xs -> f acc; loop (x :: acc) xs
    in
    loop []
  in
  fun ~path_of_key ci ->
    Ci.all_offsets ci |>
    map (fun (path, fo) -> path @ may_map (fun fi -> [`Field fi]) ~dft:[] fo) |>
    iter
      (iter_rev_prefixes @@
       fun rev_path ->
       let path = rev rev_path in
       match rev_path with
       | []                                            -> ()
       | (`Container_of_void _ | `Field _ as off) :: _ ->
         let ty =
           match off with
           | `Container_of_void ty -> Ty.normalize ty
           | `Field fi             -> Ty.normalize fi.ftype
         in
         let off = Integer.of_int @@ fst (bitsOffset (TComp (ci, empty_size_cache (), [])) (to_offset path)) lsr 3 in
         H_field.replace path_of_key (ci, ty, off) path;
         H_field.replace path_of_key (ci, ty, negate off) path)

let container_of =
  let mkCast = mkCast ~overflow:Check ~force:true in
  fun ~loc offs e ->
    let newt =
      TPtr
        ((match List.hd offs with
           | `Field fi             -> TComp (fi.fcomp, empty_size_cache (), [])
           | `Container_of_void ty -> Ty.normalize ty),
         [])
    in
    mkCast ~newt ~e:(new_exp ~loc @@ BinOp (MinusPI,
                                            mkCast ~newt:charPtrType ~e,
                                            mkCast
                                              ~newt:theMachine.typeOfSizeOf
                                              ~e:(mkAddrOf ~loc (Mem (mkCast ~newt ~e:(zero ~loc)), to_offset offs)),
                                            charPtrType))

let dot ~loc offs e = mkAddrOf ~loc (Mem e, to_offset offs)

let rec mark =
  function
  | []                         -> ()
  | `Field fi :: os            -> fi.faddrof <- true; mark os
  | `Container_of_void _ :: os -> mark os

module Make (I : sig val offs_of_key : Info.offs H_field.t end) = struct
  module Analysis = Analysis (I)

  open Analysis

  class rewriter = object(self)
    inherit frama_c_inplace

    method! vexpr e =
      let loc = e.eloc in
      let visit = visitFramacExpr (self :> frama_c_visitor) in
      let cast ty e =
        let ty' = typeOf e in
        if not (Ty.compatible ty ty') then
          match
            Ci.(match_deep_first_subfield_of ty ty',
                match_deep_first_subfield_of ty' ty)
          with
          | Some offs, _
          | _,         Some offs                               -> mark offs
          | _                                                  -> ()
      in
      match match_container_of2 e.enode, match_dot e.enode with
      | Some (e, offs), _                       -> let e = visit e in mark offs; ChangeTo (container_of ~loc offs e)
      | _,              Some (e, offs)          -> let e = visit e in mark offs; ChangeTo (dot ~loc offs e)
      | _                                       ->
        match e.enode with
        | CastE (ty, _, e)                      -> cast ty e; DoChildren
        | BinOp
            ((Eq | Ne as op),
             { enode = CastE (ty, _, e1); _ },
             { enode = CastE (ty', _, e2); _ },
             _)
          when
            not (need_cast
                   ty
                   theMachine.ptrdiffType) &&
            not (need_cast ty ty')              -> ChangeDoChildrenPost (mkBinOp ~loc op e1 e2, id)
        | _                                     -> DoChildren
  end
end
