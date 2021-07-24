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

Module fin.
  Definition t n := {m : N | m < n}.

  Definition of_N (p : positive) (n : N) : t (Npos p) :=
    match decide (n < Npos p) with
    | left prf => n ↾ prf
    | right _ => 0 ↾ eq_refl
    end.
  Definition to_N {n} (f : t n) : N := proj1_sig f.

  (** Declared an instance, because it is not redudant after [t] is made opaque. *)
  #[global] Instance to_N_inj n : Inj eq eq (to_N (n := n)) := _.
  #[global] Instance fin_eq_dec n : EqDecision (t n) := _.
  #[global] Instance fin_countable n : Countable (t n) := _.
  #[global] Instance fin_pos_inhabited p : Inhabited (t (Npos p)) := populate (of_N _ 0).
  #[global] Hint Opaque t : typeclass_instances.
End fin.
