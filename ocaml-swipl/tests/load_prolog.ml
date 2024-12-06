open Swipl

let _ =
  Embedding.initialise [|Sys.argv.(0); "-q"|];
  Query.load "test(X) :- X = 1.";
  let p = Pred.make (Functor.make (Atom.make "test") 1) in
  let args = Term.Refs.make 1 in
  Term.put_integer (Term.Refs.get args 0) 1;
  Query.call_predicate p args
