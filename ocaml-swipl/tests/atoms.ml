open Swipl

let atom = "my_atom"

let _ =
  Embedding.initialise [|Sys.argv.(0); "-q"|];
  let atom1 = Atom.make atom in
  let atom2 = Atom.make atom in
  let node1 = Term.Ref.make () in
  let node2 = Term.Ref.make () in
  Term.put_atom node1 atom1;
  Term.put_atom node2 atom2;
  Printf.printf "Compare: %i\n%!" (Term.compare node1 node2);
  Printf.printf "Equal: %b\n%!" (Term.equal node1 node2);
  Printf.printf "Unifiable: %b\n%!" (Term.unify node1 node2)
