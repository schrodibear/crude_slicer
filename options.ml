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
      let default = Datatype.String.Set.of_list ["__VERIFIER_error"; "ldv_error"]
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

module Required_bodies =
  Filled_string_set
    (struct
      let option_name = "-required_bodies"
      let help = "Special functions (allocation, error, assume...), which nontheless require implementations"
      let arg_name = ""
      let default =
        Datatype.String.Set.of_list ["ldv_error"; "ldv_malloc"; "ldv_zalloc"; "ldv_init_zalloc"]
    end)

module Assume_functions =
  Filled_string_set
    (struct
      let option_name = "-assume_functions"
      let help = "Specify names of functions allowing to restrict the values of some variables"
      let arg_name = ""
      let default = Datatype.String.Set.of_list ["__VERIFIER_assume"; "ldv_assume"]
    end)

module Path_assume_functions =
  Filled_string_set
    (struct
      let option_name = "-path_assume_functions"
      let help = "Specify names of functions allowing to specify assumed unreachability of statements"
      let arg_name = ""
      let default = Datatype.String.Set.of_list ["ldv_stop"]
    end)

module Nondet_int_function =
  String
    (struct
      let option_name = "-nondet_int_function"
      let help = "May specify an alternative name for __VERIFIER_nondet_int"
      let arg_name = ""
      let default = "__VERIFIER_nondet_int"
    end)

module Havoc_function =
  String
    (struct
      let option_name = "-havoc_function"
      let help = "May specify an alternative name for __VERIFIER_havoc_region"
      let arg_name = ""
      let default = "__VERIFIER_havoc_region"
    end)

module Choice_function =
  String
    (struct
      let option_name = "-choice_function"
      let help = "May specify an alternative name for __VERIFIER_choose"
      let arg_name = ""
      let default = "__VERIFIER_choose"
    end)

module Region_length =
  Int
    (struct
      let option_name = "-region_length"
      let help = "Specify how many regions of the same kind and type should be retained on a region graph path \
                  before producing a loop during instantiation of polymorphic regions"
      let arg_name = ""
      let default = 3
    end)

module Region_depth =
  Int
    (struct
      let option_name = "-region_depth"
      let help = "Specify bound on graph depth for unification"
      let arg_name = ""
      let default = 3
    end)

module Region_count =
  Int
    (struct
      let option_name = "-region_count"
      let help = "Specify how many regions of the same kind and type should be retained in the entire region \
                  subgraph (before producing a loop) during unification"
      let arg_name = ""
      let default = 9
    end)

module Builtin_expect_regexp =
  String
    (struct
      let option_name = "-builtin_expect"
      let help = "Specify regexp to recognize and remove __builtin_expect wrapper function"
      let arg_name = ""
      let default = ".*__builtin_expect"
    end)
