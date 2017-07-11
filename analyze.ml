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
open Cil_datatype
open Cil_printer
open Visitor
open Pretty_utils

open Extlib
open Format
open! Common

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
  Console.debug "Started callgraph condensation...";
  let module Cg = Callgraph.Cg in
  Console.debug ~level:2 "Computing callgraph...";
  let cg = Cg.get () in
  Console.debug ~level:2 "Syntactic slicing...";
  let module H = Kernel_function.Hashtbl in
  let module Traverse = Graph.Traverse.Bfs (Cg.G) in
  let h = H.create 512 in
  let main = Globals.Functions.find_by_name @@ Kernel.MainFunction.get () in
  Traverse.iter_component (fun v -> H.replace h v ()) cg main;
  let module G = Graph.Imperative.Digraph.Concrete (Kernel_function) in
  let module Components = Graph.Components.Make (G) in
  let g = G.create ~size:(H.length h) () in
  Cg.G.iter_edges (fun f t -> if H.mem h f && H.mem h t then G.add_edge g f t) cg;
  Console.debug ~level:2 "Sccs...";
  let r = Components.scc_list g in
  Console.debug ~level:3 "Finished condensation...";
  r

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
  fun ~offs_of_key ci ->
    Console.debug ~level:2 "Collecting offsets from compinfo %s..." (compFullName ci);
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
         Info.H_field.replace offs_of_key (ci, ty, off) path;
         Info.H_field.replace offs_of_key (ci, ty, negate off) path)

let pp_off fmttr =
  let pp fmt = fprintf fmttr fmt in
  function
  | `Container_of_void ty -> pp "@@(%a)" pp_typ ty
  | `Field fi             -> pp ".%a" pp_field fi

let cache_offsets =
  let conv n =
    let open Integer in
    let mx = add (max_unsigned_number @@ theMachine.theMachine.sizeof_ptr lsl 3) one in
    let mxpos = div mx @@ of_int 2 in
    if gt n mxpos then sub n mx else n
  in
  fun ~offs_of_key ->
    Console.debug "Started cache_offsets...";
    Info.H_field.clear offs_of_key;
    visitFramacFile
      (object
        inherit frama_c_inplace
        method! vglob_aux =
          function[@warning "-4"]
                | GCompTag (ci, _)
                | GCompTagDecl (ci, _) -> cache_offsets ~offs_of_key ci; SkipChildren
                | _                    ->                                SkipChildren
      end)
      (Ast.get ());
    Console.debug ~level:3 "Finished cache_offsets.@\n@[<2>Result is:@\n%a@]"
      (pp_iter2 ~sep:";@]@\n" ~between:" -> " Info.H_field.iter
         Integer.(fun fmt (ci, ty, off) ->
           fprintf fmt "@[<2>@[%s, %a, %s (0x%LXh)@]" (compFullName ci) pp_typ ty (to_string off) (to_int64 @@ conv off))
         (pp_list ~sep:"" pp_off))
      offs_of_key

module Goto_handling = struct
  module H = Stmt.Hashtbl

  module M = struct
    let all_paths ?s' s =
      let open Stmt in
      let open List in
      let rec all_paths path =
        let cs = hd path in
        match[@warning "-4"] cs.skind with
        | Return _ -> [path]
        | _        ->
          may_map (fun s' -> if equal cs s then [s'] else []) ~dft:[] s' @ cs.succs |>
          filter
            (fun s' ->
               let rec mem_succ =
                 function
                 | [] | [_]            -> false
                 | x :: (y :: _ as xs) -> equal s x && equal s' y || mem_succ xs
               in
               not @@ mem_succ path) |>
          concat_map (all_paths % cons' path)
      in
      all_paths [s]

    let add_closure h =
      let open List in
      let rec add_closure s =
        H.add h s ();
        s.succs |>
        filter (not % H.mem h) |>
        iter add_closure
      in
      add_closure

    let dependant_stmts =
      let open List in
      let r = H.create 64 in
      let separators = H.create 8 in
      let cache = H.create 64 in
      let independant = H.create 64 in
      fun s s' ->
        let all_paths = all_paths ~s' s in
        H.clear separators;
        begin match all_paths with
        | []      -> ()
        | p :: ps ->
          iter (fun s -> H.replace separators s ()) p;
          iter
            (fun p ->
               H.clear cache;
               iter (fun s -> H.replace cache s ()) p;
               H.filter_map_inplace (fun s () -> if H.mem cache s then Some () else None) separators)
            ps
        end;
        H.remove separators s;
        H.iter (const' @@ add_closure independant) separators;
        H.clear r;
        add_closure r s;
        add_closure r s';
        H.iter (const' @@ H.remove r) independant;
        H.fold (const' cons) r []

    class goto_visitor ~goto_vars ~stmt_vars kf =
      object(self)
        inherit frama_c_inplace

        val mutable next = Kernel_function.find_return kf

        method! vblock =
          let visit s n =
            next <- n;
            ignore @@ visitFramacStmt (self :> frama_c_visitor) s
          in
          let rec loop =
            function
            | []                  -> ()
            | [s]                 -> visit s next
            | s :: (n :: _ as ss) -> visit s n; loop ss
          in
          fun b ->
            loop b.bstmts;
            SkipChildren

        method! vstmt s =
          match s.skind with
          | Instr _
          | Return _
          | If _ | Switch _ | Loop _
          | Block _
          | UnspecifiedSequence _
          | Throw _ | TryCatch _
          | TryFinally _ | TryExcept _ -> DoChildren

          | AsmGoto _
          | Goto _
          | Break _
          | Continue _                 ->
            let deps = dependant_stmts s next in
            let vi =
              makeTempVar
                ~insert:false
                ~name:("goto_at_L" ^ string_of_int (fst @@ Stmt.loc s).Lexing.pos_lnum)
                (Kernel_function.get_definition kf)
                (TVoid [])
            in
            H.replace goto_vars s vi;
            List.iter (fun s -> H.add stmt_vars s vi) deps;
            SkipChildren
      end
  end
end

include Goto_handling.M

let fill_goto_tables ~goto_vars ~stmt_vars =
  let open Info in
  Console.debug "Started fill_goto_tables...";
  H_stmt.clear goto_vars;
  H_stmt.clear stmt_vars;
  Globals.Functions.iter
    (fun kf ->
       match Kernel_function.get_definition kf with
       | exception Kernel_function.No_Definition -> ()
       | fundec                                  ->
         Console.debug ~level:2 "Filling goto tables in function %s..." fundec.svar.vname;
         (* Cfg.cfgFun fundec; *) (* Already computed by default in current Frama-C *)
         ignore @@ visitFramacFunction (new goto_visitor ~goto_vars ~stmt_vars kf) fundec);
  Console.debug ~level:3 "Finished filling goto tables. \
                          Result is:@\n@[<2>Goto vars:@\n%a@]@\n@[<2>Stmt vars:@\n%a@]"
    (pp_iter2 ~sep:";@\n" ~between:"@ ->@ " H_stmt.iter
       (fun fmt s -> fprintf fmt "s%d@@L%d" s.sid (fst @@ Stmt.loc s).Lexing.pos_lnum)
       pp_varinfo)
    goto_vars
    (pp_iter2 ~sep:";@\n" ~between:"@ ->@ " H_stmt_conds.iter_all pp_stmt @@
     pp_list ~pre:"[@[" ~suf:"]@]" ~sep:",@ " ~empty:"[]" pp_varinfo)
    stmt_vars
