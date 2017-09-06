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

let memo f =
  let cache = ref None in
  fun () ->
    match !cache with
    | None ->
      let r = f () in
      cache := Some r;
      r
    | Some r -> r

let get_addressed_kfs =
  let module H = Kernel_function.Hashtbl in
  memo @@
  fun () ->
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
        function
          [@warning "-4"]
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

let callee_approx e =
  let open List in
  get_addressed_kfs () |>
  let ty = typeOf e in
  filter (fun kf -> not @@ need_cast (Kernel_function.get_vi kf).vtype ty)

module Cg = Graph.Imperative.Digraph.Concrete (Kernel_function)

let get_cg =
  memo @@
  fun () ->
  let g = Cg.create () in
  let main = Globals.Functions.find_by_name @@ Kernel.MainFunction.get () in
  Cg.add_vertex g main;
  visitFramacFile
    (object(self)
      inherit frama_c_inplace
      method! vinst i =
        let kf = the self#current_kf in
        begin match[@ warning "-4"] i with
        | Call (_, { enode = Lval (Var vi, NoOffset); _ }, _, _)
          when Kf.mem vi                                            -> Cg.add_edge g kf (Globals.Functions.get vi)
        | Call (_, e, _, _)                                         -> List.iter (Cg.add_edge g kf) (callee_approx e)
        | _                                                         -> ()
        end;
        SkipChildren
    end)
  (Ast.get ());
  g, main

let condensate =
  memo @@
  fun () ->
  Console.debug "Started callgraph condensation...";
  Console.debug ~level:2 "Computing callgraph...";
  let cg, main = get_cg () in
  Console.debug ~level:2 "Syntactic slicing...";
  let module H = Kernel_function.Hashtbl in
  let module Traverse = Graph.Traverse.Bfs (Cg) in
  let h = H.create 512 in
  Traverse.iter_component (fun v -> H.replace h v ()) cg main;
  let module Components = Graph.Components.Make (Cg) in
  let g = Cg.create ~size:(H.length h) () in
  Cg.iter_edges (fun f t -> if H.mem h f && H.mem h t then Cg.add_edge g f t) cg;
  Console.debug ~level:2 "Sccs...";
  let r = Components.scc_list g in
  Console.debug ~level:3 "Finished condensation...";
  r

let rec to_offset =
  function
  | []                                             -> NoOffset
  | (`Field fi | `Container_of_void (fi, _)) :: os -> Field (fi, to_offset os)

let cache_offsets =
  let open List in
  let module H = Hashtbl.Make
      (struct
        type t = (fieldinfo * typ) Info.offs
        let rec hash =
          function
          | []                               -> 1
          | `Field fi :: os                  -> 13 * hash os + 7 * Fieldinfo.hash fi + 5
          | `Container_of_void (_, ty) :: os -> 13 * hash os + 7 * Typ.hash ty       + 3
        let rec equal p1 p2 =
          match p1, p2 with
          | [],                                 []                                 -> true
          | `Field fi1                  :: os1, `Field fi2                  :: os2
            when Fieldinfo.equal fi1 fi2                                           -> equal os1 os2
          | `Container_of_void (_, ty1) :: os1, `Container_of_void (_, ty2) :: os2
            when Typ.equal ty1 ty2                                                 -> equal os1 os2
          | _                                                                      -> false
      end)
  in
  let h = H.create 4096 in
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
    H.clear h;
    Ci.goffsets ci |>
    map (fun (path, fo) -> path @ may_map (fun fi -> [`Field fi]) ~dft:[] fo) |>
    iter
      (iter_rev_prefixes @@
       fun rev_path ->
       if not (H.mem h rev_path) then
         let path = rev rev_path in
         H.replace h rev_path ();
         match rev_path with
         | []                                            -> ()
         | (`Container_of_void _ | `Field _ as off) :: _ ->
           let ty =
             match off with
             | `Container_of_void (_, ty) -> Ty.normalize ty
             | `Field fi                  -> Ty.normalize fi.ftype
           in
           let off = Integer.of_int @@ fst (bitsOffset (TComp (ci, empty_size_cache (), [])) (to_offset path)) lsr 3 in
           Info.H_field.replace offs_of_key (ci, ty, off) path;
           Info.H_field.replace offs_of_key (ci, ty, negate off) path)

let pp_off fmttr =
  let pp fmt = fprintf fmttr fmt in
  function
  | `Container_of_void (_, ty) -> pp "@@(%a)" pp_typ ty
  | `Field fi                  -> pp ".%a" pp_field fi

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
          function
            [@warning "-4"]
          | GCompTag (ci, _)
          | GCompTagDecl (ci, _) -> cache_offsets ~offs_of_key ci; SkipChildren
          | _                    ->                                SkipChildren
      end)
      (Ast.get ());
    Console.debug ~level:3 "Finished cache_offsets.@\n@[<2>Result is:@\n%a@]"
      (pp_iter2 ~sep:";@]@\n" ~between:" -> " Info.H_field.iter
         Integer.(fun fmt (ci, ty, off) ->
           fprintf fmt "@[<2>@[%s, %a, %s (0x%LXh)@]"
             (compFullName ci) pp_typ ty (to_string off) (to_int64 @@ conv off))
         (pp_list ~sep:"" pp_off))
      offs_of_key

module Goto_handling = struct
  module H = Stmt.Hashtbl

  module M = struct
    let add_closure h =
      let rec add_closure s =
        if not (H.mem h s) then begin
          H.replace h s ();
          List.iter add_closure s.succs
        end
      in
      add_closure

    let separate =
      let module Q = Queue in
      let d = H.create 64 in
      let q = Q.create () in
      let h = H.create 64 in
      let exception Found of stmt in
      fun r ?s' s ->
        Q.add s q;
        H.add d s 0;
        while not (Q.is_empty q) do
          let cs = Q.pop q in
          may_map (fun s' -> if Stmt.equal cs s then [s'] else []) ~dft:[] s' @ cs.succs |>
          List.iter (fun s -> if not (H.mem d s) then begin H.(add d s @@ find d cs + 1); Q.add s q end)
        done;
        H.remove d s;
        match
          H.iter_sorted_by_entry
            ~cmp:(fun (s1, d1) (s2, d2) ->
              if      d1 < d2 then -1
              else if d1 > d2 then 1
              else                 Stmt.compare s1 s2)
            (fun cs _ ->
               H.replace h cs ();
               add_closure h s;
               may (add_closure h) s';
               if not (H.mem h r) || Stmt.equal cs r then begin
                 H.remove h cs;
                 H.remove h s;
                 raise (Found cs)
               end;
               H.clear h)
            d
        with
        | exception Found s ->(let r = s, H.fold (const' List.cons) h [] in
                               H.clear d;
                               H.clear h;
                               r)
        | ()                -> Console.fatal "Analysis.Goto_handling.separate: broken invariant: no separators"

    class goto_visitor ~goto_vars ~stmt_vars kf =
      let return = Kernel_function.find_return kf in
      object(self)
        inherit frama_c_inplace

        val mutable next = return

        method! vblock =
          let visit s n =
            next <- n;
            ignore @@ visitFramacStmt (self :> frama_c_visitor) s
          in
          let rec loop =
            let next = next in
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
            let sep, deps = separate return ~s':next s in
            Console.debug ~level:4 "Found separator for statement %a@@L%d : %a@@L%d"
              pp_stmt s (Stmt.lnum s) pp_stmt sep (Stmt.lnum sep);
            let vi =
              makeTempVar
                ~insert:false
                ~name:("goto_at_L" ^ string_of_int @@ Stmt.lnum s)
                (Kernel_function.get_definition kf)
                (TInt (IInt, []))
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
         ignore @@ visitFramacFunction (new goto_visitor ~goto_vars ~stmt_vars kf) fundec);
  Console.debug ~level:3 "Finished filling goto tables. \
                          Result is:@\n@[<2>Goto vars:@\n%a@]@\n@[<2>Stmt vars:@\n%a@]"
    (pp_iter2 ~sep:";@\n" ~between:"@ ->@ " H_stmt.iter
       (fun fmt s -> fprintf fmt "s%d@@L%d" s.sid @@ Stmt.lnum s)
       pp_varinfo)
    goto_vars
    (pp_iter2 ~sep:";@\n" ~between:"@ ->@ " H_stmt_conds.iter_all pp_stmt @@
     pp_list ~pre:"[@[" ~suf:"]@]" ~sep:",@ " ~empty:"[]" pp_varinfo)
    stmt_vars
