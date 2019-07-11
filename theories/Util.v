(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

(* note(gmm): this file should be eliminated in favor of definitions defined elsewhere, e.g. in ExtLib *)

Section find_in_list.
  Context {T U : Type}.
  Variable f : T -> option U.

  Fixpoint find_in_list (ls : list T) : option U :=
    match ls with
    | nil => None
    | l :: ls =>
      match f l with
      | None => find_in_list ls
      | x => x
      end
    end.
End find_in_list.

Global Instance Decidable_eq_string (a b : string) : Decidable (a = b) :=
  {| Decidable_witness := String.eqb a b
   ; Decidable_spec := @String.eqb_eq a b |}.

Section dec_list.
  Context {T : Type} {dec : forall a b : T, Decidable (a = b)}.

  Fixpoint dec_list (a b : list T) : bool :=
    match a , b with
    | nil , nil => true
    | x :: xs , y :: ys => decide (x = y) && dec_list xs ys
    | _ , _ => false
    end.

  Lemma dec_list_ok:
    forall a b : list T, dec_list a b = true <-> a = b.
  Proof.
    induction a; destruct b; simpl; intros; try solve [ tauto | split; congruence ].
    split.
    - intros. eapply Bool.andb_true_iff in H. destruct H.
      eapply Decidable_sound in H.
      eapply IHa in H0. f_equal; assumption.
    - inversion 1; subst.
      eapply Bool.andb_true_iff.
      split.
      eapply Decidable_complete. auto.
      eapply IHa. reflexivity.
  Qed.

  Global Instance Decidable_eq_list (a b : list T) : Decidable (a = b) :=
  {| Decidable_witness := dec_list a b
   ; Decidable_spec := dec_list_ok a b |}.

  Definition dec_option (a b : option T) : bool :=
    match a , b with
    | None , None => true
    | Some a , Some b => decide (a = b)
    | _ , _ => false
    end.

  Lemma dec_option_ok : forall a b, dec_option a b = true <-> a = b.
  Proof.
    destruct a; destruct b; simpl; try solve [ tauto | split; congruence ].
    generalize (dec t t0).
    destruct d.
    simpl. etransitivity. eassumption.
    split; congruence.
  Qed.

  Global Instance Decidable_eq_option (a b : option T) : Decidable (a = b) :=
  {| Decidable_witness := dec_option a b
   ; Decidable_spec := dec_option_ok a b |}.

End dec_list.

Section dec_sum.
  Context {T U : Type}
          {decT : forall a b : T, Decidable (a = b)}
          {decU : forall a b : U, Decidable (a = b)}.

  Definition dec_sum (a b : T + U) : bool :=
    match a , b with
    | inl a , inl b => decide (a = b)
    | inr a , inr b => decide (a = b)
    | _ , _ => false
    end.

  Lemma dec_sum_ok : forall a b, dec_sum a b = true <-> a = b.
  Proof.
    destruct a; destruct b; simpl; try solve [ split; congruence ].
    all: etransitivity; [ eapply Decidable_spec | split; congruence ].
  Qed.

  Global Instance Decidable_eq_sum (a b : T + U) : Decidable (a = b) :=
  {| Decidable_witness := dec_sum a b
   ; Decidable_spec := dec_sum_ok a b |}.


  Definition dec_prod (a b : T * U) : bool :=
    decide (fst a = fst b) && decide (snd a = snd b).

  Lemma dec_prod_ok : forall a b, dec_prod a b = true <-> a = b.
  Proof.
    destruct a; destruct b; unfold dec_prod; simpl; try solve [ split; congruence ].
    etransitivity. eapply Bool.andb_true_iff.
    do 2 rewrite Decidable_spec.
    split; firstorder; congruence.
  Qed.

  Global Instance Decidable_eq_prod (a b : T * U) : Decidable (a = b) :=
  {| Decidable_witness := dec_prod a b
   ; Decidable_spec := dec_prod_ok a b |}.

End dec_sum.
