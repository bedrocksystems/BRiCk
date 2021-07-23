(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(*
 * The following code contains code derived from code original to the
 * stdpp project. That original code is
 *
 *	Copyright stdpp developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original stdpp License:
 * https://gitlab.mpi-sws.org/iris/stdpp/-/blob/5415ad3003fd4b587a2189ddc2cc29c1bd9a9999/LICENSE
 *)

From stdpp Require Import base decidable countable.
From bedrock.prelude Require Import base option.

(* From stdpp START, to drop on bump. *)
#[global] Program Instance countable_sig `{Countable A} (P : A → Prop)
        `{!∀ x, Decision (P x), !∀ x, ProofIrrel (P x)} :
  Countable { x : A | P x } :=
  inj_countable proj1_sig (λ x, guard (P x) as Hx; Some (x ↾ Hx)) _.
Next Obligation.
  intros A ?? P ?? [x Hx]. by erewrite (option_guard_True_pi (P x)).
Qed.
(* From stdpp END. *)

#[local] Open Scope N_scope.

Implicit Types (n : N) (p : positive).

Definition fin n := {m : N | m < n}.

Definition as_fin (p : positive) (n : N) : fin (Npos p) :=
  match decide (n < Npos p) with
  | left prf => n ↾ prf
  | right _ => 0 ↾ eq_refl
  end.

#[global] Instance fin_eq_dec n : EqDecision (fin n) := _.
#[global] Instance fin_countable n : Countable (fin n) := _.
#[global] Instance fin_pos_inhabited p : Inhabited (fin (Npos p)) := populate (as_fin _ 0).
#[global] Hint Opaque fin : typeclass_instances.

(* Was [fin_eq], unused. *)
Lemma proj1_sig_proper {n} (a b : fin n) : a = b -> proj1_sig a = proj1_sig b.
Proof. apply f_equal. Qed.

(* Was [fineq] *)
Lemma fin_proj1_sig_inj {n} (a b : fin n):
  proj1_sig a = proj1_sig b -> a = b.
Proof. apply: proj1_sig_inj. Qed.
