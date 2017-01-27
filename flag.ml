(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Format

type t = bool ref * string

let create name = ref false, name
let report (f, _) = f := true
let reported (f, _) = !f
let clear (f, _) = f := false
let pp fmt (_, name) = fprintf fmt "%s" name

