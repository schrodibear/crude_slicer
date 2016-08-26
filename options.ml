(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016                                                    *)
(*                                                                        *)
(**************************************************************************)

include
  Plugin.Register
    (struct
       let name = "Crude_slicer"
       let shortname = "Crude_slicer"
       let help = "Crude slicer for preprocessing reachability verification tasks"
     end)

module Analysis =
  False
    (struct
      let option_name = "-crude_slicer"
      let help = "perform crude slicing as preprocessing of a reachability verification task"
    end)

module Target_functions =
  Filled_string_set
    (struct
      let option_name = "-target_functions"
      let help = "Specify target (error) function name for reachability analysis"
      let arg_name = ""
      let default = Datatype.String.Set.of_list ["__VERIFIER_error"; "ldv_assume"]
    end)
