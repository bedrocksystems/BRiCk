open Swipl

let _ =
  Embedding.initialise [|Sys.argv.(0); "-q"|]

let pp_list name l =
  let pp_sep ff () = Format.fprintf ff ", " in
  let pp_list = Format.pp_print_list ~pp_sep Format.pp_print_int in
  Format.printf "%s = [%a]\n%!" name pp_list l

let _ =
  let t = Term.make_list_pair (Term.make_integer 42) (Term.make_nil ()) in
  let l = Term.extract_list Term.get_integer t in
  pp_list "l" l

let _ =
  let t = Term.Ref.make () in
  let hd = Term.Ref.make () in
  let tl = Term.Ref.make () in
  Term.put_integer hd 73;
  Term.put_nil tl;
  Term.put_list_pair t hd tl;
  let l = Term.extract_list Term.get_integer t in
  pp_list "l" l

let test l1 =
  pp_list "l1" l1;
  let t = Term.Ref.make () in
  Term.inject_list_map t Term.put_integer l1;
  let l2 = Term.extract_list Term.get_integer t in
  pp_list "l2" l2;
  l1 = l2

let _ =
  if not (test []) then assert false;
  if not (test [0]) then assert false;
  if not (test [1; 2; 3]) then assert false
