(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Definition resolve (t : Type) : Type := t.
Definition use {t} (r : resolve t) : t := r.
Existing Class resolve.
Typeclasses Transparent resolve.
Hint Extern 1 (resolve _) => red : typeclass_instances.

Lemma decide_ok : forall P {ok : Decidable P}, decide P = true <-> P.
Proof.
  intros. eapply Decidable_spec.
Qed.

Lemma decide_not_ok : forall P {ok : Decidable P}, decide P = false <-> not P.
Proof.
  intros.
  destruct ok. unfold decide. simpl in *.
  destruct (Decidable_witness).
  { split; try tauto; congruence. }
  { split; try tauto. do 2 intro. apply Decidable_spec in H0. congruence. }
Qed.

Lemma decide_both : forall P {ok : Decidable P},
    if decide P then P else not P.
Proof.
  intros.
  generalize (decide_ok P).
  generalize (decide_not_ok P).
  destruct (decide P); tauto.
Qed.

(* note(gmm): this file should be eliminated in favor of definitions defined elsewhere, e.g. in ExtLib *)

(* Section find_in_list. *)
(*   Context {T U : Type}. *)
(*   Variable f : T -> option U. *)

(*   Fixpoint find_in_list (ls : list T) : option U := *)
(*     match ls with *)
(*     | nil => None *)
(*     | l :: ls => *)
(*       match f l with *)
(*       | None => find_in_list ls *)
(*       | x => x *)
(*       end *)
(*     end. *)
(* End find_in_list. *)

Global Instance Decidable_eq_string (a b : string) : Decidable (a = b) :=
  {| Decidable_witness := String.eqb a b
   ; Decidable_spec := @String.eqb_eq a b |}.

Global Instance Decidable_eq_ascii (a b : Ascii.ascii) : Decidable (a = b) :=
  {| Decidable_witness := Ascii.eqb a b
   ; Decidable_spec := @Ascii.eqb_eq a b |}.

Global Instance Decidable_or (P Q : Prop) {DP : Decidable P} {DQ : Decidable Q}
: Decidable (P \/ Q).
Proof.
refine
  {| Decidable_witness := decide P || decide Q |}.
abstract (rewrite Bool.orb_true_iff;
          do 2 rewrite decide_ok; reflexivity).
Defined.

Global Instance Decidable_and (P Q : Prop) {DP : Decidable P} {DQ : Decidable Q}
: Decidable (P /\ Q).
Proof.
refine
  {| Decidable_witness := decide P && decide Q |}.
abstract (rewrite Bool.andb_true_iff;
          do 2 rewrite decide_ok; reflexivity).
Defined.

Global Instance Decidable_not (P : Prop) {DP : Decidable P}
: Decidable (not P).
Proof.
refine
  {| Decidable_witness := negb (decide P) |}.
abstract (rewrite Bool.negb_true_iff;
          generalize (@decide_ok P DP);
          destruct (decide P); split; intros; try congruence;
          [ exfalso; tauto | intro; eapply H in H1; congruence ]).
Defined.

Global Instance Decidable_True : Decidable True.
Proof.
refine
  {| Decidable_witness := true |}.
abstract (tauto).
Defined.

Global Instance Decidable_False : Decidable False.
Proof.
refine
  {| Decidable_witness := false |}.
abstract (split; first [ tauto | congruence ]).
Defined.

Global Instance Decidable_impl (P Q : Prop) {DP : Decidable P} {DQ : Decidable Q}
: Decidable (P -> Q).
Proof.
refine
  {| Decidable_witness := decide (not P) || decide Q |}.
abstract (rewrite Bool.orb_true_iff;
          do 2 rewrite decide_ok;
          split;
          [ intros; destruct H; auto; exfalso; auto
          | generalize (decide_both P); destruct (decide P); eauto ]).
Defined.

Section dec_list.
  Context {T : Type} {dec : resolve (forall a b : T, Decidable (a = b))}.
  Let dec' := use dec.
  Existing Instance dec'.

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
    rewrite Bool.andb_true_iff.
    rewrite decide_ok. rewrite IHa.
    firstorder (try congruence).
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
    rewrite decide_ok.
    firstorder congruence.
  Qed.

  Global Instance Decidable_eq_option (a b : option T) : Decidable (a = b) :=
  {| Decidable_witness := dec_option a b
   ; Decidable_spec := dec_option_ok a b |}.

End dec_list.

Section dec_sum.
  Context {T U : Type}
          {decT : resolve (forall a b : T, Decidable (a = b))}
          {decU : resolve (forall a b : U, Decidable (a = b))}.
  Let decT' := use decT.
  Let decU' := use decU.
  Existing Instance decT'.
  Existing Instance decU'.

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

Definition Decidable_dec {T} (a b : T) {Dec : Decidable (a = b)}
  : {a = b} + {a <> b}.
Proof.
  destruct Dec.
  destruct Decidable_witness.
  - left. apply Decidable_spec. reflexivity.
  - right. intro. apply Decidable_spec in H. congruence.
Defined.

(* note(gmm): this isn't the most computationally efficient way to
 * define a [Decidable] instance, but it is convenient because
 * of [decide equality].
 *)
Definition dec_Decidable {T} {a b : T} (Dec : {a = b} + {a <> b})
  : Decidable (a = b).
Proof.
  refine {| Decidable_witness := if Dec then true else false |}.
  destruct Dec; split; congruence.
Defined.
