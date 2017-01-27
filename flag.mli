(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Format

type t

val create : string -> t
val report : t -> unit
val reported : t -> bool
val clear : t -> unit
val pp : formatter -> t -> unit
