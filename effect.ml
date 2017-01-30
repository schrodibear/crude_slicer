(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Cil
open Cil_types
open Cil_printer
open Cil_datatype

open Format
open Extlib
open Common
open Data

module type Criterion = sig
  type t
  val is_ok : t -> bool
end

module Make_var (C : Criterion with type t := varinfo) : sig
  type t = private varinfo

  include Criterion with type t := t
  val of_varinfo : varinfo -> t option
  val of_varinfo_exn : varinfo -> t
  include Hashed_ordered_printable with type t := t
end = struct
  type t = varinfo

  include C

  let of_varinfo vi = if C.is_ok vi then Some vi else None

  let of_varinfo_exn vi =
    if C.is_ok vi then vi
    else invalid_arg "Formal_var.of_varinfo_exn"

  include (Varinfo : Hashed_ordered with type t := t)
  let pp = pp_varinfo
end

module Global_var = Make_var (struct let is_ok vi = isArithmeticOrPointerType vi.vtype && vi.vglob end)

module Formal_var = Make_var (struct let is_ok vi = isArithmeticOrPointerType vi.vtype && vi.vformal end)

module Local_var =
  Make_var (struct let is_ok vi = isArithmeticOrPointerType vi.vtype && not vi.vglob && not vi.vformal end)

module H_global_var = Make_reporting_bithashset (Global_var) ()
module H_formal_var = Make_reporting_bithashset (Formal_var)
module H_local_var = Make_reporting_bithashset (Local_var)

module Memory_field : sig
  type t = private fieldinfo

  include Criterion with type t := t
  val of_fieldinfo : fieldinfo -> t option
  val of_fieldinfo_exn : fieldinfo -> t
  include Hashed_ordered_printable with type t := t
end = struct
  type t = fieldinfo

  let is_ok fi = fi.fcomp.cstruct && isArithmeticOrPointerType fi.ftype

  let of_fieldinfo fi = if is_ok fi then Some fi else None

  let of_fieldinfo_exn fi =
    if is_ok fi then fi
    else
      Console.fatal
        "Memory_field.of_fieldinfo_exn: not ok: %s.%s : %a"
        (compFullName fi.fcomp) fi.fname pp_typ fi.ftype

  include (Fieldinfo : Hashed_ordered with type t := t)
  let pp fmt fi = fprintf fmt "%s" fi.fname
end

module type Representant = sig
  module Kind : sig
    type t = private [> `Global | `Poly of string | `Local of string]

    include Printable with type t := t
  end

  type t

  val name : t -> string
  val typ  : t -> typ
  val kind : t -> Kind.t

  include Hashed_ordered_printable with type t := t
end

module type Unifiable = sig
  type t
  type repr
  val repr : t -> repr
end

module type Memory = sig
  type t
  type u
  val mk : ?fi: fieldinfo -> u -> t
  include Hashed_ordered_printable with type t := t
end

module Make_memory (R : Representant) (U : Unifiable with type repr = R.t) (C : Criterion with type t := R.t)
  : Memory with type u = U.t = struct
  type t = R.t * Memory_field.t option
  type u = U.t

  let mk ?fi u =
    let r = U.repr u in
    if C.is_ok r then
      Console.fatal "Memory.mk: wrong region (not OK): %s : %a vs. %a" (R.name r) pp_typ (R.typ r) R.Kind.pp (R.kind r);
    if isArithmeticOrPointerType (R.typ r) then
      match fi with
      | None -> r, None
      | Some fi ->
        Console.fatal
          "Memory.mk: fields can't be specified for primitive regions: %s.%s for %s"
          fi.fcomp.cname fi.fname (R.name @@ U.repr u)
    else
      match unrollTypeDeep (R.typ r), fi with
      | TComp (ci, _ ,_), Some fi when Compinfo.equal ci fi.fcomp ->
        r, Some (Memory_field.of_fieldinfo_exn fi)
      | _, None ->
        Console.fatal "Memory.mk: improper region (with no field): %s : %a" (R.name r) pp_typ (R.typ r)
      | _, Some fi ->
        Console.fatal
          "Memory.mk: improper combination of region and field: %s : %a and %s.%s : %a"
          (R.name r) pp_typ (R.typ r) (compFullName fi.fcomp) fi.fname pp_typ fi.ftype

  let equal (r1, fo1) (r2, fo2) = R.equal r1 r2 && opt_equal Memory_field.equal fo1 fo2

  let hash (r, fo) = 997 * R.hash r + opt_hash Memory_field.hash fo

  let compare (r1, fo1) (r2, fo2) =
    let r = R.compare r1 r2 in
    if r <> 0 then r else opt_compare Memory_field.compare fo1 fo2

  let pp fmttr =
    let pp fmt = fprintf fmttr fmt in
    function
    | r, Some fi -> pp "%a->%a" R.pp r Memory_field.pp fi
    | r, None    -> pp "*%a" R.pp r
end

module type Memories = sig
  type u
  module Global_mem : Memory with type u := u
  module Poly_mem : Memory with type u := u
  module Local_mem : Memory with type u := u
  module H_global_mem : Reporting_bithashset with type elt := Global_mem.t
  module H_poly_mem : functor () -> Reporting_bithashset with type elt := Poly_mem.t
  module H_local_mem : functor () -> Reporting_bithashset with type elt := Local_mem.t
end

module Make_memories (R : Representant) (U : Unifiable with type repr = R.t) () = struct
  type u = U.t
  module Global_mem = Make_memory (R) (U) (struct let is_ok r = R.kind r = `Global end)
  module Poly_mem =
    Make_memory (R) (U) (struct let is_ok r = match R.kind r with `Poly _ -> true | _ -> false end)
  module Local_mem =
    Make_memory (R) (U) (struct let is_ok r = match R.kind r with `Local _ -> true | _ -> false end)
  module H_global_mem = Make_reporting_bithashset (Global_mem) ()
  module H_poly_mem = Make_reporting_bithashset (Poly_mem)
  module H_local_mem = Make_reporting_bithashset (Local_mem)
end

module type Writes = sig
  module Memories : Memories

  open Memories
  type t =
    | Global_var of Global_var.t
    | Poly_var of Formal_var.t
    | Local_var of Local_var.t
    | Global_mem of Global_mem.t
    | Poly_mem of Poly_mem.t
    | Local_mem of Local_mem.t
    | Result

  include Hashed_ordered_printable with type t := t
end

module Make_writes (M : Memories) : Writes with module Memories = M = struct
  module Memories = M

  open M

  type t =
    | Global_var of Global_var.t
    | Poly_var of Formal_var.t
    | Local_var of Local_var.t
    | Global_mem of Global_mem.t
    | Poly_mem of Poly_mem.t
    | Local_mem of Local_mem.t
    | Result

  let compare w1 w2 =
    match w1, w2 with
    | Global_var v1, Global_var v2 -> Global_var.compare v1 v2
    | Global_var _, _ -> -1
    | Poly_var _, Global_var _ -> 1
    | Poly_var v1, Poly_var v2 -> Formal_var.compare v1 v2
    | Poly_var _, _ -> -1
    | Local_var _, (Global_var _ | Poly_var _) -> 1
    | Local_var v1, Local_var v2 -> Local_var.compare v1 v2
    | Local_var _, _ -> -1
    | Global_mem _, (Global_var _ | Poly_var _ | Local_var _) -> 1
    | Global_mem m1, Global_mem m2 -> Global_mem.compare m1 m2
    | Global_mem _, _ -> -1
    | Poly_mem _, (Global_var _ | Poly_var _ | Local_var _ | Global_mem _) -> 1
    | Poly_mem m1, Poly_mem m2 -> Poly_mem.compare m1 m2
    | Poly_mem _, _ -> -1
    | Local_mem _, (Global_var _ | Poly_var _ | Local_var _ | Global_mem _ | Poly_mem _) -> 1
    | Local_mem m1, Local_mem m2 -> Local_mem.compare m1 m2
    | Local_mem _, _ -> -1
    | Result, Result -> 0
    | Result, _ -> 1

  let equal w1 w2 =
    match w1, w2 with
    | Global_var v1, Global_var v2 -> Global_var.equal v1 v2
    | Poly_var v1, Poly_var v2 -> Formal_var.equal v1 v2
    | Local_var v1, Local_var v2 -> Local_var.equal v1 v2
    | Global_mem m1, Global_mem m2 -> Global_mem.equal m1 m2
    | Poly_mem m1, Poly_mem m2 -> Poly_mem.equal m1 m2
    | Local_mem m1, Local_mem m2 -> Local_mem.equal m1 m2
    | Result, Result -> true
    | _ -> false

  let hash =
    function
    | Global_var v -> 7 * Global_var.hash v
    | Poly_var v -> 7 * Formal_var.hash v + 1
    | Local_var v -> 7 * Local_var.hash v + 2
    | Global_mem m -> 7 * Global_mem.hash m + 3
    | Poly_mem m -> 7 * Poly_mem.hash m + 4
    | Local_mem m -> 7 * Local_mem.hash m + 5
    | Result -> 6

  let pp fmttr =
    let pp fmt = fprintf fmttr fmt in
    function
    | Global_var v -> pp "%a" Global_var.pp v
    | Poly_var v -> pp "'%a" Formal_var.pp v
    | Local_var v -> pp "~%a" Local_var.pp v
    | Global_mem m -> pp "%a" Global_mem.pp m
    | Poly_mem m -> pp "'%a" Poly_mem.pp m
    | Local_mem m -> pp "~%a" Local_mem.pp m
    | Result -> pp "!R!"
end

module type Reads_kind = sig
  module W : Writes

  open W.Memories

  type _ t =
    | Global_var : Global_var.t t
    | Poly_var : Formal_var.t t
    | Local_var : Local_var.t t
    | Global_mem : Global_mem.t t
    | Poly_mem : Poly_mem.t t
    | Local_mem : Local_mem.t t
end

module Make_reads_kind (W : Writes) : Reads_kind with module W = W = struct
  module rec M : Reads_kind with module W = W = M
  include M
end

module type Reads = sig
  module W : Writes

  open W.Memories

  module K : Reads_kind with module W = W

  type t

  type 'a kind = 'a K.t

  type some = Some : 'a K.t * 'a -> some

  val of_writes : W.t -> some option

  val create : Flag.t -> t
  val clear : t -> unit
  val import : from:t -> t -> unit
  val add_global_var : Global_var.t -> t -> unit
  val add_poly_var : Formal_var.t -> t -> unit
  val add_local_mem : Local_var.t -> t -> unit
  val add_global_mem : Global_mem.t -> t -> unit
  val add_poly_mem : Poly_mem.t -> t -> unit
  val add_local_mem : Local_mem.t -> t -> unit
  val add : 'a K.t -> 'a -> t -> unit
  val sub : t -> from:t -> unit
  val mem : 'a K.t -> 'a -> t -> bool
  val intersects : t -> t -> bool
  val flag : t -> Flag.t
  val copy : Flag.t -> t -> t

  val iter_global_vars : (Global_var.t -> unit) -> t -> unit
  val iter_poly_vars : (Formal_var.t -> unit) -> t -> unit
  val iter_local_vars : (Local_var.t -> unit) -> t -> unit
  val iter_global_mems : (Global_mem.t -> unit) -> t -> unit
  val iter_poly_mems : (Poly_mem.t -> unit) -> t -> unit
  val iter_local_mems : (Local_mem.t -> unit) -> t -> unit
  val is_empty : t -> bool
  val is_singleton : t -> bool
  val length : t -> int

  val pp : formatter -> t -> unit
end

module Make_reads (W : Writes) (K : Reads_kind with module W = W) () :
  Reads with module W = W and module K = K = struct
  module W = W

  open W.Memories

  module H_formal_var = H_formal_var ()
  module H_local_var = H_local_var ()
  module H_poly_mem = H_poly_mem ()
  module H_local_mem = H_local_mem ()

  module K = K

  type 'a kind = 'a K.t

  type some = Some : 'a K.t * 'a -> some

  open K

  type t =
    {
      global_vars : H_global_var.t;
      poly_vars   : H_formal_var.t;
      local_vars  : H_local_var.t;
      global_mems : H_global_mem.t;
      poly_mems   : H_poly_mem.t;
      local_mems  : H_local_mem.t
    }

  let of_writes : _ -> some option =
    function
    | W.Global_var v -> Some (Some (Global_var, v))
    | W.Local_var v -> Some (Some (Local_var, v))
    | W.Poly_var v -> Some (Some (Poly_var, v))
    | W.Global_mem m -> Some (Some (Global_mem, m))
    | W.Local_mem m -> Some (Some (Local_mem, m))
    | W.Poly_mem m -> Some (Some (Poly_mem, m))
    | W.Result -> None

  let create f =
    { global_vars = H_global_var.create f;
      poly_vars = H_formal_var.create f;
      local_vars = H_local_var.create f;
      global_mems = H_global_mem.create f;
      poly_mems = H_poly_mem.create f;
      local_mems = H_local_mem.create f }

  let clear r =
    H_global_var.clear r.global_vars;
    H_formal_var.clear r.poly_vars;
    H_local_var.clear r.local_vars;
    H_global_mem.clear r.global_mems;
    H_poly_mem.clear r.poly_mems;
    H_local_mem.clear r.local_mems

  let import ~from r =
    H_global_var.import ~from:from.global_vars r.global_vars;
    H_formal_var.import ~from:from.poly_vars r.poly_vars;
    H_local_var.import ~from:from.local_vars r.local_vars;
    H_global_mem.import ~from:from.global_mems r.global_mems;
    H_poly_mem.import ~from:from.poly_mems r.poly_mems;
    H_local_mem.import ~from:from.local_mems r.local_mems

  let add_global_var v r = H_global_var.add v r.global_vars
  let add_poly_var v r = H_formal_var.add v r.poly_vars
  let add_local_var v r = H_local_var.add v r.local_vars
  let add_global_mem m r = H_global_mem.add m r.global_mems
  let add_poly_mem m r = H_poly_mem.add m r.poly_mems
  let add_local_mem m r = H_local_mem.add m r.local_mems

  let add : type a. a K.t -> a -> _ = fun k x r ->
    match k with
    | Global_var -> H_global_var.add x r.global_vars
    | Poly_var -> H_formal_var.add x r.poly_vars
    | Local_var -> H_local_var.add x r.local_vars
    | Global_mem -> H_global_mem.add x r.global_mems
    | Poly_mem -> H_poly_mem.add x r.poly_mems
    | Local_mem -> H_local_mem.add x r.local_mems

  let sub r ~from =
    H_global_var.sub r.global_vars ~from:from.global_vars;
    H_formal_var.sub r.poly_vars ~from:from.poly_vars;
    H_local_var.sub r.local_vars ~from:from.local_vars;
    H_global_mem.sub r.global_mems ~from:from.global_mems;
    H_poly_mem.sub r.poly_mems ~from:from.poly_mems;
    H_local_mem.sub r.local_mems ~from:from.local_mems

  let mem : type a. a K.t -> a -> _ = fun k x r ->
    match k with
    | Global_var -> H_global_var.mem x r.global_vars
    | Poly_var -> H_formal_var.mem x r.poly_vars
    | Local_var -> H_local_var.mem x r.local_vars
    | Global_mem -> H_global_mem.mem x r.global_mems
    | Poly_mem -> H_poly_mem.mem x r.poly_mems
    | Local_mem -> H_local_mem.mem x r.local_mems

  let intersects r1 r2 =
    H_global_var.intersects r1.global_vars r2.global_vars ||
    H_formal_var.intersects r1.poly_vars r2.poly_vars ||
    H_local_var.intersects r1.local_vars r2.local_vars ||
    H_global_mem.intersects r1.global_mems r2.global_mems ||
    H_poly_mem.intersects r1.poly_mems r2.poly_mems ||
    H_local_mem.intersects r1.local_mems r2.local_mems

  let flag r = H_global_var.flag r.global_vars

  let copy f r =
    { global_vars = H_global_var.copy f r.global_vars;
      poly_vars = H_formal_var.copy f r.poly_vars;
      local_vars = H_local_var.copy f r.local_vars;
      global_mems = H_global_mem.copy f r.global_mems;
      poly_mems = H_poly_mem.copy f r.poly_mems;
      local_mems = H_local_mem.copy f r.local_mems }

  let iter_global_vars f r = H_global_var.iter f r.global_vars
  let iter_poly_vars f r = H_formal_var.iter f r.poly_vars
  let iter_local_vars f r = H_local_var.iter f r.local_vars
  let iter_global_mems f r = H_global_mem.iter f r.global_mems
  let iter_poly_mems f r = H_poly_mem.iter f r.poly_mems
  let iter_local_mems f r = H_local_mem.iter f r.local_mems

  let is_empty r =
    H_global_var.is_empty r.global_vars &&
    H_formal_var.is_empty r.poly_vars &&
    H_local_var.is_empty r.local_vars &&
    H_global_mem.is_empty r.global_mems &&
    H_poly_mem.is_empty r.poly_mems &&
    H_local_mem.is_empty r.local_mems

  let length r =
    List.fold_left
      (+)
      0
      [H_global_var.length r.global_vars;
       H_formal_var.length r.poly_vars;
       H_local_var.length r.local_vars;
       H_global_mem.length r.global_mems;
       H_poly_mem.length r.poly_mems;
       H_local_mem.length r.local_mems]

  let is_singleton r = length r = 1

  let pp fmt r =
    fprintf fmt "  @[gv:%a,@ @,pv:%a,@ @,lv:%a,@ @,gm:%a,@ @,pm:%a,@ @,lm:%a@]"
      H_global_var.pp r.global_vars
      H_formal_var.pp r.poly_vars
      H_local_var.pp r.local_vars
      H_global_mem.pp r.global_mems
      H_poly_mem.pp r.poly_mems
      H_local_mem.pp r.local_mems
end

module Fundec = struct include Fundec let pp = pretty end
module Stmt = struct include Stmt let pp = pretty end

module H_fundec = Make_reporting_bithashset (Fundec) ()
module H_stmt = Make_reporting_bithashset (Stmt) ()

module Requires : sig
  type t

  val create : Flag.t -> t
  val import : from:t -> t -> unit
  val add_body : fundec -> t -> unit
  val add_stmt : stmt -> t -> unit
  val copy : Flag.t -> t -> t

  val iter_bodies : (fundec -> unit) -> t -> unit
  val iter_stmts : (stmt -> unit) -> t -> unit
  val has_body : fundec -> t -> bool
  val has_stmt : stmt -> t -> bool
end = struct
  type t =
    {
      bodies : H_fundec.t;
      stmts  : H_stmt.t
    }

  let create f = { bodies = H_fundec.create f; stmts = H_stmt.create f }
  let import ~from r =
    H_fundec.import ~from:from.bodies r.bodies;
    H_stmt.import ~from:from.stmts r.stmts
  let add_body f r = H_fundec.add f r.bodies
  let add_stmt s r = H_stmt.add s r.stmts
  let copy f r = { bodies = H_fundec.copy f r.bodies; stmts = H_stmt.copy f r.stmts }

  let iter_bodies f r = H_fundec.iter f r.bodies
  let iter_stmts f r = H_stmt.iter f r.stmts
  let has_body f r = H_fundec.mem f r.bodies
  let has_stmt s r = H_stmt.mem s r.stmts
end

module Void_ptr_var = Make_var (struct let is_ok vi = isVoidPtrType vi.vtype end)

module H_void_ptr_var = Make_reporting_bithashset (Void_ptr_var) ()

module Make_effect (W : Writes) : sig
  type ('a, 'r) t
  module K : Reads_kind with module W = W
  module type Reads = Reads with module W = W and module K = K
  module type Assigns = Reporting_hashmap with type key = W.t and type 'a kind = 'a K.t
  type some =
    | Some :
        { reads : (module Reads with type t = 'r);
          assigns : (module Assigns with type set = 'r and type t = 'a);
          eff : ('a, 'r) t } -> some
  val create : Flag.t -> some
  val assigns : ('a, 'r) t -> 'a
  val depends : ('a, 'r) t -> 'r
  val add_result_dep : (_, _) t -> unit
  val add_requires : Requires.t -> (_, _) t -> unit
  val add_body_req : fundec -> (_, _) t -> unit
  val add_stmt_req : stmt -> (_, _) t -> unit
  val set_is_target : (_, _) t -> unit
  val add_tracking_var : Void_ptr_var.t -> (_, _) t -> unit
  val copy : Flag.t -> some -> some

  val is_target : (_, _) t -> bool
  val is_tracking_var : Void_ptr_var.t -> (_, _) t -> bool
  val has_result_dep : (_, _) t -> bool
  val iter_body_reqs : (fundec -> unit) -> (_, _) t -> unit
  val iter_stmt_reqs : (stmt -> unit) -> (_, _) t -> unit
  val has_body_req : fundec -> (_, _) t -> bool
  val has_stmt_req : stmt -> (_, _) t -> bool
  val flag : (_, _) t -> Flag.t

  val pp : formatter -> some -> unit
end = struct

  module K = Make_reads_kind (W)
  module Reads = Make_reads (W) (K)
  module Assigns = Make_reporting_hashmap (W)

  type ('a, 'r) t =
    {
              assigns    : 'a;
              tracking   : H_void_ptr_var.t;
      mutable is_target  : bool;
              depends    : 'r;
      mutable result_dep : bool;
              requires   : Requires.t;
              flag       : Flag.t;
    }

  module type Reads = Reads with module W = W and module K = K
  module type Assigns = Reporting_hashmap with type key = W.t and type 'a kind = 'a K.t
  type some =
    | Some :
        { reads : (module Reads with type t = 'r);
          assigns : (module Assigns with type set = 'r and type t = 'a);
          eff : ('a, 'r) t } -> some
  let create f =
    let module R = Reads () in
    let module A = Assigns (R) in
    Some {
      reads = (module R);
      assigns = (module A);
      eff = {
        assigns = A.create f;
        tracking = H_void_ptr_var.create f;
        is_target = false;
        depends = R.create f;
        result_dep = false;
        requires = Requires.create f;
        flag = f
      }}

  let assigns e = e.assigns
  let depends e = e.depends
  let add_result_dep e = if not e.result_dep then Flag.report e.flag; e.result_dep <- true
  let add_requires d e = Requires.import ~from:d e.requires
  let set_is_target e = if not e.is_target then Flag.report e.flag; e.is_target <- true

  let add_body_req f e = Requires.add_body f e.requires
  let add_stmt_req s e = Requires.add_stmt s e.requires
  let has_body_req f e = Requires.has_body f e.requires
  let has_stmt_req s e = Requires.has_stmt s e.requires
  let add_tracking_var v e = H_void_ptr_var.add v e.tracking
  let copy f (Some { reads = (module R) as reads; assigns = (module A) as assigns; eff = e }) =
    Some {
      reads;
      assigns;
      eff = {
        assigns = A.copy f e.assigns;
        tracking = H_void_ptr_var.copy f e.tracking;
        is_target = e.is_target;
        depends = R.copy f e.depends;
        result_dep = e.result_dep;
        requires = Requires.copy f e.requires;
        flag = f }}

  let is_target e = e.is_target
  let has_result_dep e = e.result_dep
  let is_tracking_var v e = H_void_ptr_var.mem v e.tracking
  let iter_body_reqs f e = Requires.iter_bodies f e.requires
  let iter_stmt_reqs f e = Requires.iter_stmts f e.requires
  let flag e = e.flag

  let pp fmt (Some { reads = (module R); assigns = (module A); eff = e }) =
    fprintf fmt "@[w:@;@[%a@];@.track:%a;@.tar:%B;@.deps:@;%a;@.RD:%B@]"
      A.pp e.assigns H_void_ptr_var.pp e.tracking e.is_target R.pp e.depends e.result_dep
end

module Make (R : Representant) (U : Unifiable with type repr = R.t) () = struct
  module M = Make_memories (R) (U) ()
  module W = Make_writes (M)
  module E = Make_effect (W)

  module F = struct
    module H_fundec = Fundec.Hashtbl
    module H_stmt = Stmt.Hashtbl
    module H_stmt_conds = struct
      include Stmt.Hashtbl

      let find_or_empty h k = try find h k with Not_found -> []
    end
    module Field_key =
      Datatype.Triple_with_collections (Compinfo) (Typ) (Datatype.Integer) (struct let module_name = "field key" end)
    module H_field = Field_key.Hashtbl
    type t =
      {
        block_id_of_stmt : int H_stmt.t;
        conds_of_loop    : exp list H_stmt_conds.t;
        fields_of_key    : fieldinfo list H_field.t;
        effects          : E.some H_fundec.t
      }

    let create () =
      {
        block_id_of_stmt = H_stmt.create 128;
        conds_of_loop = H_stmt_conds.create 32;
        fields_of_key = H_field.create 64;
        effects = H_fundec.create 1024
      }
    let get fi fl f =
      try
        H_fundec.find fi.effects f
      with
      | Not_found ->
        let r = E.create fl in
        H_fundec.replace fi.effects f r;
        r
  end
end
