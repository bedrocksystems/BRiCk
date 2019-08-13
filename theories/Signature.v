Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Cpp.Ast Cpp.Sem.

Record specification : Type := { s_name : obj_name ; s_spec : Rep }.

Definition signature : Type := mpred.

Definition make_signature (ss : list specification) : signature :=
  sepSPs (List.map (fun s => _at (_global s.(s_name)) s.(s_spec)) ss).

Fixpoint find_spec (s : obj_name) (ss : list specification) : option Rep :=
  match ss with
  | nil => None
  | x :: xs => if decide (s = x.(s_name)) then Some x.(s_spec) else find_spec s xs
  end.

Fixpoint drop_spec (s : obj_name) (ss : list specification) : list specification :=
  match ss with
  | nil => nil
  | x :: xs => if decide (s = x.(s_name)) then xs else x :: drop_spec s xs
  end.

Lemma make_signature_nil : make_signature nil -|- empSP.
Proof. reflexivity. Qed.

Hint Rewrite -> make_signature_nil : done_proof.