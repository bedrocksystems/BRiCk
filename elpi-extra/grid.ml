#!/usr/bin/env ocaml

#directory "+unix";; #load "unix.cma";;
#directory "+str";; #load "str.cma";;

let print = Format.printf
let eprint = Format.eprintf
let fprint = Format.fprintf
type 'a pp = Format.formatter -> 'a -> unit
let pp_string : string pp = Format.pp_print_string
let rec pp_list (sep : string) : 'a pp -> 'a list pp = fun f buf xs ->
  match xs with
  | [] -> ()
  | [x] -> f buf x
  | x :: xs -> (f buf x; pp_string buf sep; pp_list sep f buf xs)

let argv0 : string =
  if Array.length Sys.argv > 0
  then Sys.argv.(0)
  else "grid"

module Nature =
struct
  type t = Program | Tactic | Command | TacticCommand

  let to_int : t -> int = function | Program -> 0 | Tactic -> 1 | Command -> 2
    | TacticCommand -> 3
  let compare (x : t) (y : t) : int = Int.compare (to_int x) (to_int y)
  let size : int = to_int TacticCommand + 1
  let of_string : string -> t = function
    | "Program" -> Program | "Tactic" -> Tactic | "Command" -> Command
    | "TacticCommand" -> TacticCommand
    | s -> begin eprint "%s: bad nature: %s\n" argv0 s; exit 1 end
  let to_string : t -> string = function
    | Program -> "Program" | Command -> "Command" | Tactic -> "Tactic"
    | TacticCommand -> "TacticCommand"
  let pp : t pp = fun buf n -> pp_string buf (to_string n)
  let fold (f : t -> 'a -> 'a) (acc : 'a) : 'a =
    let acc = f Program acc in
    let acc = f Tactic acc in
    let acc = f Command acc in
    let acc = f TacticCommand acc in
    acc
end

module Phase =
struct
  type t = Both | Synterp | Interp

  let to_int : t -> int = function | Both -> 0 | Synterp -> 1 | Interp -> 2
  let compare (x : t) (y : t) : int = Int.compare (to_int x) (to_int y)
  let size : int = to_int Interp + 1
  let of_string : string -> t = function
    | "both" -> Both | "synterp" -> Synterp | "interp" -> Interp
    | s -> begin eprint "%s: bad phase: %s\n" argv0 s; exit 1 end
  let to_string : t -> string = function
    | Both -> "both" | Synterp -> "synterp" | Interp -> "interp"
  let pp : t pp = fun buf n -> pp_string buf (to_string n)
  let fold (f : t -> 'a -> 'a) (acc : 'a) : 'a =
    let acc = f Both acc in
    let acc = f Synterp acc in
    let acc = f Interp acc in
    acc
end

module Row =
struct
  type 'a t = Row of 'a option array

  let mk () : 'a t = Row (Array.make Nature.size None)
  let set : 'a t -> Nature.t -> 'a -> unit = fun (Row r) n v ->
    let n = Nature.to_int n in
    match r.(n) with
    | None -> r.(n) <- Some v
    | Some _ -> invalid_arg "Row.set"
  let fold : 'a t -> (Nature.t -> 'a -> 'b -> 'b) -> 'b -> 'b = fun (Row r) f acc ->
    let folder n acc =
      match r.(Nature.to_int n) with
      | None -> acc
      | Some v -> f n v acc
    in
    Nature.fold folder acc
end

module Tbl =
struct
  type 'a t = Tbl of 'a Row.t array

  let mk () : 'a t = Tbl (Array.init Phase.size (fun _ -> Row.mk()))
  let set : 'a t -> Phase.t -> Nature.t -> 'a -> unit = fun (Tbl t) p n v ->
    Row.set t.(Phase.to_int p) n v
  let fold : 'a t -> (Phase.t -> Nature.t -> 'a -> 'b -> 'b) -> 'b -> 'b = fun (Tbl t) f acc ->
    let folder p acc = Row.fold t.(Phase.to_int p) (f p) acc in
    Phase.fold folder acc
end

module Names =
struct
  module M = Map.Make(String)

  type 'a t = 'a Tbl.t M.t

  let empty : 'a t = M.empty
  let add : string -> Phase.t -> Nature.t -> 'a -> 'a t -> 'a t = fun ns p n v ->
    M.update ns @@ fun t ->
    let t = match t with None -> Tbl.mk() | Some t -> t in
    Tbl.set t p n v;
    Some t
  let iter : (string -> 'a Tbl.t -> unit) -> 'a t -> unit = M.iter
  let fold : 'a t -> (string -> Phase.t -> Nature.t -> 'a -> 'b -> 'b) -> 'b -> 'b = fun m f acc ->
    let folder name tbl acc = Tbl.fold tbl (f name) acc in
    M.fold folder m acc
end

let with_open_process_args_in (prog : string) (args : string array) (f : in_channel -> 'a) : 'a =
  let c = Unix.open_process_args_in prog args in
  let close () : unit =
    let fail () = eprint "%s: %s failed\n" argv0 prog; exit 2 in
    try
      match Unix.close_process_in c with
      | Unix.WEXITED 0 -> ()
      | _ -> fail()
    with _ -> fail()
  in
  try let r = f c in close(); r
  with e -> (close(); raise e)

let scan (dir : string) : int * string Names.t =
  let rSlash = Str.regexp "/" in
  let rDot = Str.regexp "\\." in
  let input_line_opt (c : in_channel) : string option =
    try Some (input_line c)
    with End_of_file -> None
  in
  let rec read_all (c : in_channel) (skipped : int) (ns : string Names.t) : int * string Names.t =
    match input_line_opt c with
    | None -> skipped, ns
    | Some path ->
      let skip () = eprint "%s: %s\n" argv0 path; skipped+1, ns in
      let (skipped, ns) =
        (* dir/NATURE/PHASE/BASE.elpi *)
        match Str.split rSlash path with
        | [d; nature; phase; file] when d = dir -> begin
          match Str.split rDot file with
          | [base; "elpi"] ->
            let n = Nature.of_string nature in
            let p = Phase.of_string phase in
            let ns = Names.add base p n path ns in
            skipped, ns
          | _ -> skip()
        end
        | _ -> skip()
      in
      read_all c skipped ns
  in
  with_open_process_args_in "/usr/bin/find" [| "find"; dir; "-name"; "*.elpi" |] @@ fun c ->
  read_all c 0 Names.empty

let pp_prelude : 'a Tbl.t pp = fun buf tbl ->
  let module Set = Set.Make(Nature) in
  let all = Nature.fold Set.add Set.empty in
  let folder _ n _ acc =
    match n with
    | Nature.Program -> all
    | Nature.TacticCommand ->
      Set.add Nature.Command @@ Set.add Nature.Tactic acc
    | _ -> Set.add n acc
  in
  let used : Set.t = Tbl.fold tbl folder Set.empty in
  let size = Set.cardinal used in
  if size = Nature.size then
    fprint buf "any prelude"
  else if size = 1 then
    fprint buf "%a only" Nature.pp (Set.min_elt used)
  else
    fprint buf "%a" (pp_list " and " Nature.pp) (Set.elements used)

let pp_phase : 'a Tbl.t pp = fun buf tbl ->
  let module Set = Set.Make(Phase) in
  let all = Phase.fold Set.add Set.empty in
  let folder p _ _ acc =
    match p with
    | Phase.Both -> all
    | _ -> Set.add p acc
  in
  let used : Set.t = Tbl.fold tbl folder Set.empty in
  let size = Set.cardinal used in
  if size = Phase.size then
    fprint buf "both phases"
  else begin
    assert (size = 1);
    fprint buf "%a only" Phase.pp (Set.min_elt used)
  end

let pp_code : 'a Tbl.t pp = fun buf tbl ->
  let folder phase nature path (_ : unit) : unit =
    fprint buf "[%a/%a](%s), " Nature.pp nature Phase.pp phase path
  in
  Tbl.fold tbl folder ()

let pp_names : string Names.t pp = fun buf ns ->
  let print (name : string) (t : string Tbl.t) : unit =
    fprint buf "* `%s`, %a, %a: %a\n" name pp_prelude t pp_phase t pp_code t
  in
  Names.iter print ns

let usage () : 'a =
  eprint "usage: %s dir\n" argv0;
  exit 1

let () = begin
  let dir : string =
    if Array.length Sys.argv == 2
    then Sys.argv.(1)
    else usage()
  in
  let (skipped, ns) = scan dir in
  print "<!-- BEGIN generated by `%s %s` -->\n%a<!-- END generated -->\n"
    argv0 dir pp_names ns;
  exit @@ Int.min skipped 1
end
