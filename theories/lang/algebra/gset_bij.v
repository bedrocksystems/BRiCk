(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export iris.algebra.lib.gset_bij.
Require Import bedrock.prelude.base.

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
