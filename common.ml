(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Format

module type Hashed = Hashtbl.HashedType

module type Ordered = Map.OrderedType

module type Printable = sig
  type t
  val pp : formatter -> t -> unit
end

module type Hashed_ordered = sig
  include Hashed
  include Ordered with type t := t
end

module type Hashed_printable = sig
  include Hashed
  include Printable with type t := t
end

module type Ordered_printable = sig
  include Ordered
  include Printable with type t := t
end

module type Hashed_ordered_printable = sig
  include Hashed
  include Ordered with type t := t
  include Printable with type t := t
end

module Console = Options

let (%) f g x = f (g x)
let (%%) f g x y = f (g x y)
let (%>) f g x = g (f x)
let const f _x = f
let const' f x _y = f x
