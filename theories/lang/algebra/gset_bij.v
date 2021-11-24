(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Export iris.algebra.lib.gset_bij.
Require Import bedrock.prelude.base.

(** PDS: Misplaced. *)
Section gset_bij.
  Context `{Countable A, Countable B}.
  Implicit Types a : A.
  Implicit Types b : B.

  (** Useful corollary to [gset_bij_auth_extend] that also produces
      the new element. *)
  Lemma gset_bij_update_alloc {L} a b :
    (∀ b', (a, b') ∉ L) → (∀ a', (a', b) ∉ L) →
    gset_bij_auth 1 L ~~> gset_bij_auth 1 ({[(a, b)]} ∪ L) ⋅ gset_bij_elem a b.
  Proof.
    intros. etrans; first exact: gset_bij_auth_extend.
    rewrite {1}(core_id_extract (gset_bij_elem _ _) (gset_bij_auth _ _))//.
    apply bij_view_included. set_solver+.
  Qed.
End gset_bij.
