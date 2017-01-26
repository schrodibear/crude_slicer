(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

module Console = Options

let () = if Options.Analysis.get () then Kernel.Constfold.off ()

let run () =
  Cil_printer.state.Printer_api.line_directive_style <- Some Printer_api.Line_preprocessor_output;
  Console.debug ~level:2 "Crude slicer enabled!";
  Console.feedback "Running slicer";
  Slice.slice ();
  Console.feedback "Slicer finished"

let main () = if Options.Analysis.get () then run ()
let () = Db.Main.extend main
