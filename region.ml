(**************************************************************************)
(*                                                                        *)
(*  Crude slicer for preprocessing reachability verification tasks        *)
(*                                                                        *)
(*  Copyright (C) 2016-2017 Mikhail Mandrykin, ISP RAS                    *)
(*                                                                        *)
(**************************************************************************)

open Cil
open Cil_types
open Cil_datatype

module Console = Options

module Representant = struct
  module Kind = struct
    type t =
      | Global
      | Poly of string
      | Local of string
      | Dummy

    let equal k1 k2 =
      match k1, k2 with
      | Global,  Global                      -> true
      | Poly f1, Poly f2
      | Local f1, Local f2
        when String.equal f1 f2              -> true
      | Dummy, Dummy                         -> true
      | (Global | Poly _ | Local _ | Dummy),
        (Global | Poly _ | Local _ | Dummy)  -> false

    let choose k1 k2 =
      begin match k1, k2 with
      | (Poly f1 | Local f1),
        (Poly f2 | Local f2)
        when not (String.equal f1 f2)        ->
        Console.fatal
          "Representant.Kind.choose: broken invariant: should not try unifying regions from diff. functions: %s and %s"
          f1 f2
      | Dummy, Dummy                         ->
        Console.fatal
          "Representant.Kind.choose: broken invariant: dummy regions should be immediately unified with non-dummy ones"
      | (Global | Poly _ | Local _ | Dummy),
        (Global | Poly _ | Local _ | Dummy)  -> ()
      end;
      match k1, k2 with
      | Global, Global                       -> `Any
      | Global, (Poly _ | Local _ | Dummy)   -> `First
      | Poly _, Global                       -> `Second
      | Poly _, Poly _                       -> `Any
      | Poly _, (Local _ | Dummy)            -> `First
      | Local _, (Global | Poly _)           -> `Second
      | Local _, Local _                     -> `Any
      | Local _, Dummy                       -> `First
      | Dummy, (Global | Poly _ | Local _)   -> `Second
      | Dummy, Dummy                         -> `Any

    let pp fmttr =
      let pp fmt = Format.fprintf fmttr fmt in
      function
      | Global -> pp "global"
      | Poly s -> pp "poly(%s)" s
      | Local s -> pp "local(%s)" s
      | Dummy -> pp "dummy"
  end

  type t =
    {
      name : string;
      typ  : typ;
      kind : Kind.t
    }

  let equal r1 r2 = String.equal r1.name r2.name
  let hash r = Hashtbl.hash r.name
  let choose r1 r2 = Kind.choose r1.kind r2.kind

  let global name typ = { name; typ; kind = Kind.Global }
  let poly fname name typ = { name = fname ^ "::" ^ name; typ; kind = Kind.Poly fname }
  let local fname name typ = { name = fname ^ ":::" ^ name; typ; kind = Kind.Local fname }
  let dummy name typ = { name; typ; kind = Kind.Dummy }
  let template { name; typ; kind } =
    let open Kind in
    match kind with
    | Poly _ -> { name; typ; kind = Dummy }
    | Global | Local _ | Dummy ->
      Console.fatal "Representant.template: can only templatify polymorphic regions, but %s is %a" name pp kind

  let check_field f r fi =
    match unrollType r.typ with
    | TComp (ci, _, _)
      when ci.cstruct && Compinfo.equal ci fi.fcomp -> ()
    | ty ->
      Console.fatal "%s: not a struct with field %s.%s: %a" f fi.fname fi.fcomp.cname Typ.pretty ty

  let arrow r fi =
    check_field "Representant.arrow" r fi;
    if not (isPointerType fi.ftype) then
      Console.fatal "Representant.arrow: not a pointer field: %s.%s : %a" fi.fname fi.fcomp.cname Typ.pretty fi.ftype;
    { name = r.name ^ "->" ^ fi.fname; typ = typeOf_pointed fi.ftype; kind = r.kind }

  let check_detached f fi =
    if not (isStructOrUnionType fi.ftype || isArrayType fi.ftype || fi.faddrof) then
      Console.fatal
        "%s: not a struct/union, array or addressed field: %s.%s : %a (&: %B)"
        f fi.fname fi.fcomp.cname Typ.pretty fi.ftype fi.faddrof

  let dot r fi =
    check_field "Representant.dot" r fi;
    check_detached "Representant.dot" fi;
    { name = r.name ^ "." ^ fi.fname; typ = fi.ftype; kind = r.kind }

  let container r fi =
    check_detached "Representant.container" fi;
    if not (Typ.equal fi.ftype r.typ) then
      Console.fatal
        "Representant.container: illegal use of `container_of': %s.%s : %a vs. %s : %a"
        fi.fname fi.fcomp.cname Typ.pretty fi.ftype r.name Typ.pretty r.typ;
    if not fi.fcomp.cstruct then
      Console.fatal "Representant.container: container should be a structure: %s" fi.fcomp.cname;
    { name = "(" ^ r.name ^ ", " ^ fi.fcomp.cname ^ "." ^ fi.fname ^ ")";
      typ = TComp (fi.fcomp, empty_size_cache (), []);
      kind = r.kind }

  let dot_void r =
    { name = r.name ^ ".void"; typ = voidType; kind = r.kind }

  let container_of_void r typ =
    let name =
      match unrollType typ with
      | TComp (ci, _, _) when ci.cstruct -> ci.cname
      | TComp (ci, _, _) -> Console.fatal "Representant: container_of_void: shouldn't be union: %a" Typ.pretty typ
      | TVoid _ -> Console.fatal "Representant: container_of_void: shouldn't be void: %a" Typ.pretty typ
      | ty -> Format.asprintf "`%a'" Typ.pretty ty
    in
    begin match unrollType r.typ with
    | TVoid _ -> ()
    | TComp (ci, _, _) when not ci.cstruct -> ()
    | ty ->
      Console.fatal
        "Representant.container_of_void: can only take (_, %s.void) from void or union region: %s : %a"
        name r.name Typ.pretty ty
    end;
    { name = "(" ^ r.name ^ ", " ^ name ^ ".void)"; typ; kind = r.kind }

  let pp fmttr r =
    Format.fprintf fmttr "{%s : %a (%a)}" r.name Typ.pretty r.typ Kind.pp r.kind
end
