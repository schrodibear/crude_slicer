(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016                                                    *)
(*                                                                        *)
(**************************************************************************)

let run () =
  Cil_printer.state.Printer_api.line_directive_style <- Some Printer_api.Line_preprocessor_output;
  Kernel.debug ~level:2 "Crude slicer enabled!";
  Kernel.feedback "Running slicer";
  Slice.slice ();
  Kernel.feedback "Slicer finished"

let main () = if Options.Analysis.get () then run ()
let () = Db.Main.extend main
