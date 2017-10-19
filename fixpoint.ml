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

  let timeout = float_of_int @@ Options.Timeout.get ()

  let start_time = !Options.start_time

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
                   if timeout > 0. && Unix.gettimeofday () -. start_time > timeout then
                     raise Options.Timeout;
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
