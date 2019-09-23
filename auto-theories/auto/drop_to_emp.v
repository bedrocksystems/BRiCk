Require Import Cpp.Auto.

Lemma forget_later_ticptr : forall a b P,
    P |-- empSP ->
    (|> _at (_global a) (ticptr b)) ** P |-- empSP.
Proof. Admitted.
Lemma forget_ticptr : forall a b P,
    P |-- empSP ->
    (_at (_global a) (ticptr b)) ** P |-- empSP.
Proof. Admitted.
Lemma later_over_sep : forall P Q R X,
    (|> P) ** (|> Q) ** R |-- X ->
    (|> (P ** Q)) ** R |-- X.
Proof.
  intros; rewrite illater_sepSP. rewrite <- H.
  rewrite sepSPA. reflexivity.
Qed.

Ltac drop_to_emp :=
  repeat perm_left ltac:(idtac;
                          lazymatch goal with
                          | |- (|> ?X) ** _ |-- _ =>
                            first [ simple eapply later_over_sep
                                  | eapply forget_later_ticptr ]
                          | |- ?X ** _ |-- _ =>
                            eapply forget_ticptr
                          end).
