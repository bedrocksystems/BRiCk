(** "Prelude" for available-everywhere dependencies. *)
(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From stdpp Require Export prelude countable.
From iris.algebra Require Export base.
From bedrock.lang.prelude Require Export notations.

(** Workaround https://github.com/coq/coq/issues/4230. Taken from Software Foundations. *)
Remove Hints Bool.trans_eq_bool : core.

Global Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)
Global Set Default Proof Using "Type".

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
