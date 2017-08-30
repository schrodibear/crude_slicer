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
          | `Field fi :: os                  -> 7 * hash os + Fieldinfo.hash fi
          | `Container_of_void (_, ty) :: os -> 13 * hash os + Typ.hash ty
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
            (fun cs' ->
               let rec mem_succ =
                 function
                 | [] | [_]            -> false
                 | x :: (y :: _ as xs) -> equal cs y && equal cs' x || mem_succ xs
               in
               not @@ mem_succ path) |>
          concat_map (all_paths % cons' path)
      in
      all_paths [s]

    let add_closure h =
      let open List in
      let rec add_closure s =
        H.replace h s ();
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
        H.clear r;
        H.iter (H.add r) separators;
        add_closure r s;
        add_closure r s';
        H.iter (const' @@ H.remove r) separators;
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
            let deps = dependant_stmts s next in
            let vi =
              makeTempVar
                ~insert:false
                ~name:("goto_at_L" ^ string_of_int (fst @@ Stmt.loc s).Lexing.pos_lnum)
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

let hack_cfg =
  let has_jumps s =
    let vis = object
      inherit frama_c_inplace

      method! vstmt s =
        begin match[@warning "-4"] s.skind with
        | AsmGoto _
        | Goto _
        | Break _
        | Continue _  -> raise Exit
        | _           -> ()
        end;
        DoChildren
    end in
    try ignore @@ visitFramacStmt vis s; false
    with Exit ->                         true
  in
  ignore %
  visitFramacFunction
    (object
      inherit frama_c_inplace

      method! vstmt s =
        match[@warning "-4"] s.skind with
        | If (_, ({ bstmts = s1 :: _; _ } as b1), b2, _) when not (has_jumps s) ->
          (last b1.bstmts).succs <-
            (match b2.bstmts with
             | s :: _ -> [s]
             | []     -> List.filter (not % Stmt.equal s1) s.succs);
          s.succs <- [s1];
          DoChildren
        | _ -> DoChildren
    end)

let switch_count fundec =
  let count = ref 1 in
  ignore @@
  visitFramacFunction
    (object
      inherit frama_c_inplace
      method! vstmt s =
        match[@warning "-4"] s.skind with
        | Switch (_, _, ss, _) -> let l = List.length ss in if l > 0 then count := !count * l; DoChildren
        | _                    ->                                                              DoChildren
    end)
    fundec;
  !count

let[@warning "-4"] rewrite_switches =
  let open List in
  let rewrite_switch =
    let module H = Stmt.Hashtbl in
    let h = H.create 32 in
    fun e b ss ->
      iter
        (ignore %
         visitFramacStmt
           (object
             inherit frama_c_inplace
             method! vstmt s = H.replace h s (); DoChildren
           end))
        b.bstmts;
      let get_one_target ss =
        let rec targets s =
          if not (H.mem h s)
          then [s]
          else concat_map targets s.succs
        in
        let targets = map targets ss in
        if for_all ((=) 1 % length) targets
        then
          match group_by Stmt.equal @@ map hd targets with
          | [s :: _] -> Some s
          | _        -> None
        else
          None
      in
      let bodies target b =
        let is_case_label = function Case _ | Default _ -> true | Label _ -> false in
        let bs = group_by (fun _ s2 -> not @@ exists is_case_label s2.labels) b.bstmts in
        let conds =
          map hd bs |>
          map (fun s -> filter is_case_label s.labels)
        in
        let bs =
          map
            (fun ss ->
               match rev ss with
               | { skind = Goto _ | Break _ | Continue _; succs = [s]; _ } :: ss when Stmt.equal s target -> rev ss
               | _                                                                                        -> ss)
            bs |>
          tap (iter @@ iter @@ fun s -> s.labels <- filter (not % is_case_label) s.labels)
        in
        let r = combine conds bs in
        match partition (function Default _ :: _, _  -> true | _ -> false) r with
        | [_, dss], ss -> Some (dss, ss)
        | _            -> None
      in
      let (>>=) x f = opt_bind f x in
      get_one_target ss >>= fun target ->
      bodies target b >>= fun (dss, cases) ->
      let loc = Stmt.loc target in
      let ifs =
        let cond cs =
          let eqs =
            map
              (function
                | Case (e', loc) -> mkBinOp ~loc Eq e e'
                | _              -> assert false)
              cs
          in
          fold_left (fun e -> mkBinOp ~loc:e.eloc BOr e) (hd eqs) (tl eqs)
        in
        fold_right (fun (cs, ss) b -> mkBlock [mkStmt @@ If (cond cs, mkBlock ss, b, loc)]) cases (mkBlock dss)
      in
      H.clear h;
      Some (mkStmt @@ Block (mkBlock [hd ifs.bstmts; mkStmt @@ Goto (ref target, Stmt.loc target)]))
  in
  ignore %
  visitFramacFunction
    (object
      inherit frama_c_inplace
      method! vstmt s =
        match s.skind with
        | Switch (e, b, ss, _) ->
          begin match rewrite_switch e b ss with
          | Some s -> ChangeDoChildrenPost (s, id)
          | None   -> DoChildren
          end
        | _ -> DoChildren
    end)

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
         if switch_count fundec > Options.Switch_count.get () then begin
           rewrite_switches fundec;
           Cfg.clearCFGinfo ~clear_id:false fundec;
           Cfg.cfgFun fundec
         end;
         hack_cfg fundec;
         ignore @@ visitFramacFunction (new goto_visitor ~goto_vars ~stmt_vars kf) fundec;
         Cfg.clearCFGinfo ~clear_id:false fundec;
         Cfg.cfgFun fundec);
  Console.debug ~level:3 "Finished filling goto tables. \
                          Result is:@\n@[<2>Goto vars:@\n%a@]@\n@[<2>Stmt vars:@\n%a@]"
    (pp_iter2 ~sep:";@\n" ~between:"@ ->@ " H_stmt.iter
       (fun fmt s -> fprintf fmt "s%d@@L%d" s.sid (fst @@ Stmt.loc s).Lexing.pos_lnum)
       pp_varinfo)
    goto_vars
    (pp_iter2 ~sep:";@\n" ~between:"@ ->@ " H_stmt_conds.iter_all pp_stmt @@
     pp_list ~pre:"[@[" ~suf:"]@]" ~sep:",@ " ~empty:"[]" pp_varinfo)
    stmt_vars
