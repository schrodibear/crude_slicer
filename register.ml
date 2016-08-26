(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016                                                    *)
(*                                                                        *)
(**************************************************************************)

let run () =
  Kernel.debug ~level:2 "Crude slicer enabled!"

let main () = if Options.Analysis.get () then run ()
let () = Db.Main.extend main
