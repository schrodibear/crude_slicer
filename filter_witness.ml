let filter decide ic oc =
  let i = Xmlm.make_input           (`Channel ic) in
  let o = Xmlm.make_output ~nl:true (`Channel oc) in
  let input,                   output,   peek,               copy =
    Xmlm.((fun () -> input i), output o, (fun () -> peek i), fun () -> output o (input i))
  in
  let rec process d =
    let rec skip ?subst () =
      let rec loop d =
        match input () with
        | `El_start _ as s when d = 0 && subst <> None -> output s;               loop (d + 1)
        | `El_start _                                  ->                         loop (d + 1)
        | `El_end          when d = 1                  ->
          begin match subst with
          | None                                       ->                         ()
          | Some subst                                 ->(List.iter output subst;
                                                          output `El_end)
          end
        | `El_end                                      -> loop (d - 1)
        | _                                            -> loop d
      in
      loop 0
    in
    match peek () with
    | `El_start tag      ->
      begin match decide tag with
      | `Copy            -> copy ();        process (d + 1)
      | `Skip            -> skip ();        process d
      | `Subst subst     -> skip ~subst (); process d
      end;
    | `El_end when d > 0 -> copy ();        process (d - 1)
    | `El_end when d = 0 -> copy ()
    | `El_end            -> assert false
    | `Data _            -> copy ();        process d
    | `Dtd _             -> assert false
  in
  copy (); (* `Dtd *)
  copy (); (* root start *)
  process 0

let handle ?(default=`Copy) actions tag =
  let matches =
    let matches (key, value') ((_uri, local), value) = String.(equal local key && equal value value') in
    fun (name, attrs') ((_uri, local), attrs) ->
      String.equal local name && List.(for_all (fun attr -> exists (matches attr) attrs) attrs')
  in
  List.fold_left (fun acc (trigger, action) -> if matches trigger tag then action else acc) default actions

let actions filename =
  let basename = Filename.basename filename in
  let sha1 = Sha1.(to_hex @@ file filename) in
  [("key", ["attr.name", "originFileName"]), `Subst [`El_start (("", "default"), []); `Data basename; `El_end];
   ("data", ["key", "programfile"]),         `Subst [`Data filename];
   ("data", ["key", "programhash"]),         `Subst [`Data sha1];
   ("data", ["key", "startoffset"]),         `Skip;
   ("data", ["key", "endoffset"]),           `Skip]

let () =
  let iwitnessfile = ref "" in
  let owitnessfile = ref "" in
  let programfile = ref "" in
  Arg.parse
    ["-progfile", Arg.String ((:=) programfile),  "Original program file";
     "-o",        Arg.String ((:=) owitnessfile), "Output witness file"]
    ((:=) iwitnessfile)
    "Restores original file hash and name in the witness";
  let ic = open_in !iwitnessfile in
  let oc = open_out !owitnessfile in
  filter (handle (actions !programfile)) ic oc;
  close_out oc
