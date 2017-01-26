(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

module Console = Options

let (%) f g x = f (g x)
let (%%) f g x y = f (g x y)
let (%>) f g x = g (f x)
let const f _x = f
let const' f x _y = f x
