(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
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

module Use_ghosts =
  False
    (struct
      let option_name = "-use_ghosts"
      let help = "make sliced out statements ghost instead of removing them"
    end)

module Target_functions =
  Filled_string_set
    (struct
      let option_name = "-target_functions"
      let help = "Specify target (error) function name for reachability analysis"
      let arg_name = ""
      let default = Datatype.String.Set.of_list ["__VERIFIER_error"; "ldv_assume"; "ldv_stop"]
    end)

module Alloc_functions =
  Filled_string_set
    (struct
      let option_name = "-alloc_functions"
      let help = "Specify names of memory allocating functions"
      let arg_name = ""
      let default =
        Datatype.String.Set.of_list ["malloc"; "calloc"; "kmalloc"; "kzalloc";
                                     "ldv_malloc"; "ldv_zalloc"; "ldv_init_zalloc"]
    end)

module Assume_functions =
  Filled_string_set
    (struct
      let option_name = "-assume_functions"
      let help = "Specify names of functions allowing to restrict the values of some variables"
      let arg_name = ""
      let default = Datatype.String.Set.of_list ["__VERIFIER_assume"]
    end)

module Region_depth =
  Int
    (struct
      let option_name = "-region_depth"
      let help = "Specify how many regions of the same type can should be retained if a region cycle is detected"
      let arg_name = ""
      let default = 3
    end)

module Builtin_expect_regexp =
  String
    (struct
      let option_name = "-builtin_expect"
      let help = "Specify regexp to recognize and remove __builtin_expect wrapper function"
      let arg_name = ""
      let default = ".*__builtin_expect"
    end)
