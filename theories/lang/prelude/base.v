(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** "Prelude" for available-everywhere dependencies. *)

From stdpp Require Export prelude countable.
From iris.prelude Require Export prelude.
From bedrock.lang.prelude Require Export notations tc_cond_type.

(** Workaround https://github.com/coq/coq/issues/4230. Taken from Software Foundations. *)
#[global] Remove Hints Bool.trans_eq_bool : core.

Global Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)
Global Set Default Proof Using "Type".
(** Disable [Program]'s compiler for pattern matches.
It's more expressive, but it mangles definitions and can cause a quadratic size
explosion. *)
Global Unset Program Cases.

Lemma TCElemOf_iff {A} (x : A) (l : list A) : TCElemOf x l ↔ x ∈ l.
Proof. split; induction 1; by constructor. Qed.

Lemma iff_forall T P Q :
  (forall i: T, P i <-> Q i) ->
  (forall i: T, P i) <-> (forall i: T, Q i).
Proof. naive_solver. Qed.

Instance reflexive_proper A :
  Proper (pointwise_relation A (pointwise_relation A iff) ==> iff) Reflexive.
Proof.
  unfold Reflexive=> r1 r2 Heq.
  apply iff_forall => i. by rewrite Heq.
Qed.

Instance transitive_proper A :
  Proper (pointwise_relation A (pointwise_relation A iff) ==> iff) Transitive.
Proof.
  unfold Reflexive=> r1 r2 Heq.
  apply iff_forall => i.
  apply iff_forall => j.
  apply iff_forall => k.
  by rewrite Heq.
Qed.

Instance preorder_proper A :
  Proper (pointwise_relation A (pointwise_relation A iff) ==> iff) PreOrder.
Proof. by intros r1 r2 Heq; split => -[]; [rewrite Heq|rewrite -Heq]. Qed.

(** Not an instance, because of the risk of loops. *)
Lemma flip_assoc {A} {R : relation A} `{!Symmetric R} `{!Assoc R f}: Assoc R (flip f).
Proof. intros ???. symmetry. apply: (assoc f). Qed.

Section flip_app.
  Context {A : Type}.

  Global Instance flip_app_left_id : LeftId (=) (@nil A) (flip app).
  Proof. apply: right_id. Qed.
  Global Instance flip_app_right_id : RightId (=) (@nil A) (flip app).
  Proof. apply: left_id. Qed.
  Global Instance flip_app_assoc : Assoc (=) (flip (@app A)).
  Proof. apply: flip_assoc. Qed.
End flip_app.

Lemma negb_bool_decide `{Hdec : Decision P} : negb (bool_decide P) = bool_decide (not P).
Proof. by case: Hdec. Qed.

Notation Unfold x tm :=
  ltac:(let H := eval unfold x in tm in exact H) (only parsing).

(* Very incomplete set of monadic liftings. *)
Definition liftM2 `{MRet M, MBind M} `(f : A → B → C) : M A → M B → M C :=
  λ mx my,
    x ← mx; y ← my; mret (f x y).

(* Less common; name inspired by Haskell. *)
Definition bindM2 `{MBind M} `(f : A → B → M C) : M A → M B → M C :=
  λ mx my,
    x ← mx; y ← my; f x y.

#[global] Notation Reduce tm :=
  ltac:(let H := eval red in tm in exact H) (only parsing).
#[global] Notation Hnf tm :=
  ltac:(let H := eval hnf in tm in exact H) (only parsing).
#[global] Notation Cbn tm :=
  ltac:(let H := eval cbn in tm in exact H) (only parsing).
#[global] Notation Evaluate tm :=
  ltac:(let H := eval vm_compute in tm in exact H) (only parsing).
