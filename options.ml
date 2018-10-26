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

include
  Plugin.Register
    (struct
      let name = "Crude_slicer"
      let shortname = "Crude_slicer"
      let help = "Crude slicer for preprocessing reachability verification tasks. Commit " ^ Version.commit ^
                 " compiled on " ^ Version.date
    end)

module Analysis =
  False
    (struct
      let option_name = "-crude_slicer"
      let help = "Perform crude slicing as preprocessing of a reachability verification task"
    end)

module Use_ghosts =
  False
    (struct
      let option_name = "-use_ghosts"
      let help = "Make sliced out statements ghost instead of removing them"
    end)

module Target_functions =
  Filled_string_set
    (struct
      let option_name = "-target_functions"
      let help = "Specify target (error) function name for reachability analysis"
      let arg_name = "names"
      let default = Datatype.String.Set.of_list ["__VERIFIER_error"; "ldv_error"]
    end)

module Alloc_functions =
  Filled_string_set
    (struct
      let option_name = "-alloc_functions"
      let help = "Specify names of memory allocating functions"
      let arg_name = "names"
      let default =
        Datatype.String.Set.of_list ["malloc"; "calloc"; "kmalloc"; "kzalloc";
                                     "ldv_malloc"; "ldv_zalloc"; "ldv_init_zalloc"]
    end)

module Alloca_function =
  String
    (struct
      let option_name = "-alloca"
      let help = "Specify an alternative name for alloca"
      let arg_name = "name"
      let default = "alloca"
    end)

module Required_bodies =
  Filled_string_set
    (struct
      let option_name = "-required_bodies"
      let help = "Special functions (allocation, error, assume...), which nontheless require implementations"
      let arg_name = "names"
      let default =
        Datatype.String.Set.of_list ["ldv_error"; "kmalloc"; "kzalloc";
                                     "ldv_assume"; "ldv_malloc"; "ldv_zalloc"; "ldv_init_zalloc"]
    end)

module Error_function =
  String
    (struct
      let option_name = "-error_function"
      let help = "May specify an alternative name for __VERIFIER_error"
      let arg_name = "name"
      let default = "__VERIFIER_error"
    end)

module Assume_functions =
  Filled_string_set
    (struct
      let option_name = "-assume_functions"
      let help = "Specify names of functions allowing to restrict the values of some variables"
      let arg_name = "names"
      let default = Datatype.String.Set.of_list ["__VERIFIER_assume"; "ldv_assume"]
    end)

module Path_assume_functions =
  Filled_string_set
    (struct
      let option_name = "-path_assume_functions"
      let help = "Specify names of functions allowing to specify assumed unreachability of statements"
      let arg_name = "names"
      let default = Datatype.String.Set.of_list ["ldv_stop"]
    end)

module Assume_function =
  String
    (struct
      let option_name = "-assume_function"
      let help = "May specify an alternative name for __VERIFIER_assume"
      let arg_name = "name"
      let default = "__VERIFIER_assume"
    end)

module Nondet_int_function =
  String
    (struct
      let option_name = "-nondet_int_function"
      let help = "May specify an alternative name for __VERIFIER_nondet_int"
      let arg_name = "name"
      let default = "__VERIFIER_nondet_int"
    end)

module Havoc_function =
  String
    (struct
      let option_name = "-havoc_function"
      let help = "May specify an alternative name for __VERIFIER_havoc"
      let arg_name = "name"
      let default = "__VERIFIER_havoc"
    end)

module Choice_function =
  String
    (struct
      let option_name = "-choice_function"
      let help = "May specify an alternative name for __VERIFIER_choose"
      let arg_name = "name"
      let default = "__VERIFIER_choose"
    end)

module Memory_function =
  String
    (struct
      let option_name = "-memory_function"
      let help = "May specify an alternative name for __VERIFIER_memory"
      let arg_name = "name"
      let default = "__VERIFIER_memory"
    end)

module Select_function =
  String
    (struct
      let option_name = "-select_function"
      let help = "May specify an alternative name for __VERIFIER_select"
      let arg_name = "name"
      let default = "__VERIFIER_select"
    end)

module Update_function =
  String
    (struct
      let option_name = "-update_function"
      let help = "May specify an alternative name for __VERIFIER_update"
      let arg_name = "name"
      let default = "__VERIFIER_update"
    end)

module Const_function =
  String
    (struct
      let option_name = "-const_function"
      let help = "May specify an alternative name for __VERIFIER_const"
      let arg_name = "name"
      let default = "__VERIFIER_const"
    end)

module Assign_function =
  String
    (struct
      let option_name = "-assign_function"
      let help = "May specify an alternative name for __VERIFIER_assign"
      let arg_name = "name"
      let default = "__VERIFIER_assign"
    end)

module Stub_postfix =
  String
    (struct
      let option_name = "-stub_postfix"
      let help = "May specify an alternative postfix for function stubs"
      let arg_name = "postfix"
      let default = "___stub"
    end)

module Region_length =
  Int
    (struct
      let option_name = "-region_length"
      let help = "Specify how many regions of the same kind and type should be retained on a region graph path \
                  before producing a loop during instantiation of polymorphic regions"
      let arg_name = "n"
      let default = 3
    end)

module Region_depth =
  Int
    (struct
      let option_name = "-region_depth"
      let help = "Specify bound on graph depth for unification"
      let arg_name = "n"
      let default = 3
    end)

module Region_count =
  Int
    (struct
      let option_name = "-region_count"
      let help = "Specify how many regions of the same kind and type should be retained in the entire region \
                  subgraph (before producing a loop) during unification"
      let arg_name = "n"
      let default = 9
    end)

module Deps_limit =
  Int
    (struct
      let option_name = "-deps_limit"
      let help = "Specify how many arguments can be passed to dependency summary functions, too large calls will \
                  contain only the lval/havoced region and the dummy argument (char *)0"
      let arg_name = "n"
      let default = 25
    end)

module Recognize_wrecked_container_of =
  Bool
    (struct
      let option_name = "-recognize_wrecked_container_of"
      let help = "Recognize an utterly wrong code pattern emitted by CIF in place of \
                  container_of macro expansion as normal container_of (the heuristic is generally unsound!)"
      let default = true
    end)

module Widening_threshold =
  Int
    (struct
      let option_name = "-widening_threshold"
      let help = "Use widening in region analysis if at least this number of functions is present \
                  in the input file"
      let arg_name = "n"
      let default = 2000
    end)

module Summaries =
  True
    (struct
      let option_name = "-summaries"
      let help = "Switch summaries generation"
    end)

module Rewrite_indirect_calls =
  True
    (struct
      let option_name = "-rewrite_indirect_calls"
      let help = "Switch rewriting of function pointer calls"
    end)

module Builtin_expect_regexp =
  String
    (struct
      let option_name = "-builtin_expect"
      let help = "Specify regexp to recognize and remove __builtin_expect wrapper function"
      let arg_name = "regexp"
      let default = ".*__builtin_expect"
    end)

module Oslice =
  Empty_string
    (struct
      let option_name = "-oslice"
      let arg_name = "file"
      let help = "Print line numbers of all sliced-out statements to file `file'"
    end)

module Assert_stratification =
  True
    (struct
      let option_name = "-assert_stratification"
      let help = "Perform stratification checks after region analysis"
    end)

let start_time = ref (Unix.gettimeofday ())

exception Timeout

module Timeout =
  Int
    (struct
      let option_name = "-timeout"
      let help = "Run with timeout specified in seconds"
      let arg_name = "n"
      let default = 400
    end)
