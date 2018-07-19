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

module Console = Options

let () =
  Cmdline.run_after_configuring_stage
    (fun () ->
       if Options.Analysis.get () then begin
         Kernel.Machdep.set "gcc_x86_64";
         Kernel.Constfold.off ();
         Kernel.LogicalOperators.on ();
         Kernel.DoCollapseCallCast.off ()
       end)

let run () =
  Cil_printer.state.Printer_api.line_directive_style <- Some Printer_api.Line_preprocessor_output;
  Console.debug ~level:2 "Crude slicer enabled!";
  Console.feedback "Running slicer";
  try
    Slice.slice ();
    Console.feedback "Slicer finished"
  with
  | Options.Timeout ->
    Console.feedback "Slicer timed out of %d seconds" (Options.Timeout.get ())

let main () = if Options.Analysis.get () then run ()
let () = Db.Main.extend main
