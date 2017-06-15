(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

[@@@warning "-48"]

open Cil
open Cil_types
open Visitor

open Extlib
open Common

let get_addressed_kfs =
  let module H = Kernel_function.Hashtbl in
  let cache = ref None in
  fun () ->
    let fill () =
      let o =
        object(self)
          val mutable result = H.create 16
          method private add kf = H.replace result kf ()
          method get = H.fold (const' List.cons) result []

          inherit frama_c_inplace
          method! vinst =
            let avoid_direct_call lv args =
              may (ignore % visitFramacLval (self :> frama_c_visitor)) lv;
              List.iter (ignore % visitFramacExpr (self :> frama_c_visitor)) args;
              SkipChildren
            in
            function[@warning "-4"]
            | Call (lv, { enode = Lval (Var vi, NoOffset); _ }, args, _)
              when Kf.mem vi                                             -> avoid_direct_call lv args
            | Call _ | Set _ | Asm _ | Skip _ | Code_annot _             -> DoChildren
          method! vvrbl vi =
            begin match Globals.Functions.get vi with
            | kf                  -> self#add kf
            | exception Not_found -> ()
            end;
            SkipChildren
        end
      in
      Visitor.visitFramacFileSameGlobals (o :> frama_c_visitor) @@ Ast.get ();
      o#get
    in
    match !cache with
    | None ->
      let r = fill () in
      cache := Some r;
      r
    | Some r -> r

let filter_matching_kfs lvo params =
  let ltyp = may_map typeOfLval ~dft:voidType lvo in
  let open Kernel_function in
  let open List in
  get_addressed_kfs () |>
  filter
    (fun kf ->
       let rt, tformals = get_return_type kf, map (fun vi -> vi.vtype) @@ get_formals kf in
       if is_definition kf && length tformals = length params
       then for_all2 (not %% need_cast) (rt :: tformals) (ltyp :: map typeOf params)
       else false)

let condensate () =
  let module Cg = Callgraph.Cg in
  Console.debug "...computing callgraph...";
  let cg = Cg.get () in
  Console.debug "..syntactic slicing...";
  let module H = Kernel_function.Hashtbl in
  let module Traverse = Graph.Traverse.Bfs (Cg.G) in
  let h = H.create 512 in
  let main = Globals.Functions.find_by_name @@ Kernel.MainFunction.get () in
  Traverse.iter_component (fun v -> H.replace h v ()) cg main;
  let module G = Graph.Imperative.Digraph.Concrete (Kernel_function) in
  let module Components = Graph.Components.Make (G) in
  let g = G.create ~size:(H.length h) () in
  Cg.G.iter_edges (fun f t -> if H.mem h f && H.mem h t then G.add_edge g f t) cg;
  Console.debug "...sccs...";
  let r = Components.scc_list g in
  Console.debug "...finished sccs...";
  r
