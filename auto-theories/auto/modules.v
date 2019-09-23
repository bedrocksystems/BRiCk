Require Import Cpp.Sem.
Require Import Cpp.Ast.
Require Import Cpp.Auto.Linking.Lemmas.
Require Import Cpp.Auto.sep.

Ltac use_module pf :=
  match type of pf with
  | denoteModule ?SUB |-- ?SPEC =>
    match goal with
    | |- context [ denoteModule ?ALL ] =>
      match eval vm_compute in (module_le SUB ALL) with
      | true =>
        erewrite (@use_module ALL SUB SPEC (@eq_refl bool true <: module_le SUB ALL = true) pf)
      | _ => fail "module is not a subset"
      end
    end
  end.

Lemma module_emp : forall P Q R,
    P ** Q |-- R ->
    module empSP P ** Q |-- R.
Proof.
  intros. unfold module. rewrite <- H. work.
  rewrite later_empSP. work.
Qed.

Lemma Duplicable_global_ticptr : forall nm s, Duplicable (_at (_global nm) (ticptr s)).
Proof. Admitted.



Lemma module_cut_duplicable : forall X Q R F T S, Duplicable X ->
    T |-- X ** F ->
    module Q R ** X ** F |-- S ->
    module (X ** Q) R ** T |-- S.
Proof. Admitted.
Lemma module_cut_non_dup : forall X Q R T S F,
    T |-- X ** F ->
    module Q R ** F |-- S ->
    module (X ** Q) R ** T |-- S.
Proof. Admitted.

Lemma module_last_duplicable : forall X R T S F, Duplicable X ->
    T |-- X ** F ->
    R ** X ** F |-- S ->
    module (X) R ** T |-- S.
Proof. Admitted.
Lemma module_last_non_dup : forall X R T S F,
    T |-- X ** F ->
    R ** X ** F |-- S ->
    module X R ** T |-- S.
Proof. Admitted.

Ltac module_cancel :=
  repeat perm_left ltac:(idtac;
                         lazymatch goal with
                         | |- module (?X ** _) _ ** _ |-- _ =>
                           first [ eapply module_cut_duplicable;
                                   [ solve [ eauto with typeclass_instances | fail 2 ]
                                   | solve [ sep.work ]
                                   | ]
                                 | eapply module_cut_non_dup;
                                   [ solve [ sep.work ]
                                   | ]
                                 ]
                         | |- module empSP _ ** _ |-- _ => eapply module_emp
                         | |- module ?X _ ** _ |-- _ =>
                           first [ eapply module_last_duplicable;
                                   [ solve [ eauto with typeclass_instances | fail 2 ]
                                   | solve [ sep.work ]
                                   | ]
                                 | eapply module_last_non_dup;
                                   [ solve [ sep.work ]
                                   | ]
                                 ]
                         end).
