(*
 * Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

open Swipl

(* Initialisation. *)
let _ =
  Embedding.initialise [|Sys.argv.(0); "-q"|];
  Query.load Dnet_v1_static.contents

module Pattern = struct
  type t = string

  let encode : t -> Term.t = fun s ->
    Term.make_atom (Atom.make s)
end

let prem2 : Functor.t =
  Functor.make (Atom.make "prem") 2

let add_prem : int -> Pattern.t -> unit = fun index pat ->
  let index = Term.make_integer index in
  let pat = Pattern.encode pat in
  Query.assertz (Term.make_app prem2 [|index; pat|])

let cncl2 : Functor.t =
  Functor.make (Atom.make "cncl") 2

let add_cncl : int -> Pattern.t -> unit = fun index pat ->
  let index = Term.make_integer index in
  let pat = Pattern.encode pat in
  Query.assertz (Term.make_app cncl2 [|index; pat|])

let match_any4 : Functor.t =
  Functor.make (Atom.make "match_any") 4

let cancel3 : Functor.t =
  Functor.make (Atom.make "cancel") 3

let add_id_cancel : unit -> unit = fun _ ->
  let x = Term.make_list_pair (Term.Ref.make ()) (Term.make_nil ()) in
  Query.assertz (Term.make_app cancel3 [|Term.make_integer 0; x; x|])

let cleanup : unit -> unit = fun _ ->
  Query.call (Term.make_atom (Atom.make "cleanup"))

let test solution =
  Frame.with_discarded_frame @@ fun _ ->
  (* Adding premises and conclusions. *)
  for i = 1 to 150 do
    add_prem i (Printf.sprintf "p%i" i);
    add_cncl i (Printf.sprintf "c%i" i);
  done;
  for i = 1 to 3 do
    add_prem (150+i) (Printf.sprintf "cc%i" i);
    add_cncl (150+i) (Printf.sprintf "cc%i" i)
  done;
  (* Addind cancel hints (including identity cancellation). *)
  add_id_cancel ();
  for i = 1 to 1000 do
    let ps =
      let a = Atom.make (Printf.sprintf "cancelp%i" i) in
      let a = Term.make_atom a in
      Term.make_list_pair a (Term.make_nil ())
    in
    let cs =
      let a = Atom.make (Printf.sprintf "cancelc%i" i) in
      let a = Term.make_atom a in
      Term.make_list_pair a (Term.make_nil ())
    in
    Query.assertz (Term.make_app cancel3 [|Term.make_integer i; ps; cs|])
  done;
  (* Preparing the query. *)
  let args = Term.Refs.make 4 in
  let h_kind = Term.Refs.get args 0 in
  let h_id = Term.Refs.get args 1 in
  let h_pids = Term.Refs.get args 2 in
  let h_cids = Term.Refs.get args 3 in
  let handle ss =
    let open Query in
    let pp_solution () =
      let kind = Atom.to_string (Term.get_atom h_kind) in
      let index = Term.get_integer h_id in
      let pids = Term.extract_list Term.get_integer h_pids in
      let cids = Term.extract_list Term.get_integer h_cids in
      solution kind index pids cids
    in
    match ss with
    | True      -> pp_solution (); Continue
    | Last      -> pp_solution (); Close
    | False     -> Close
    | Exception -> Printf.printf "Exception\n%!"; Close
  in
  (* Running the query. *)
  Query.run_query handle (Pred.make match_any4) args

let _ =
  let solution kind index pids cids =
    let pids =
      String.concat ", " (List.map string_of_int pids)
    in
    let cids =
      String.concat ", " (List.map string_of_int cids)
    in
    Printf.printf "Solution: kind=%s, index=%i, pids=[%s], cids=[%s]\n%!"
      kind index pids cids
  in
  for i = 1 to 10 do
    Printf.printf "RUN NUMBER %i\n%!" i;
    test solution; cleanup ()
  done
