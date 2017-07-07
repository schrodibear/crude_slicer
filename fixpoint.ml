(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Cil_types
open Visitor

open Format
open Common

module type Info = sig
  module E : sig
    type some

    val pp : formatter -> some -> unit
  end

  type t

  val get : t -> Flag.t -> fundec -> E.some
  val flag : Flag.t
end

module Make (I : Info) = struct

  let rec until_convergence f fi scc =
    Flag.clear I.flag;
    f fi scc;
    if not (Flag.reported I.flag) then ()
    else until_convergence f fi scc

  class type ['a] frama_c_collector = object inherit frama_c_inplace method start : unit method finish : 'a end

  let visit_until_convergence ~order (v : _ -> _ -> _ #frama_c_collector) fi sccs =
    let iter =
      match order with
      | `topological -> List.iter
      | `reversed -> fun f l -> List.(iter f (rev l))
    in
    iter
      (fun scc ->
         let scc = List.(Kernel_function.(scc |> filter is_definition |> map get_definition)) in
         until_convergence
           (fun fi ->
              iter
                (fun d ->
                   Console.debug "Analysing function %s..." d.svar.vname;
                   let v = v fi d in
                   v#start;
                   ignore @@ visitFramacFunction (v :> frama_c_visitor) d;
                   v#finish;
                   Console.debug ~level:3 "@[<2>Result is:@\n%a@]" I.E.pp @@ I.get fi I.flag d))
           fi
           scc)
      sccs
end
