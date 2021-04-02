(*
 * Copyright (C) BedRock Systems Inc. 2020
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *)
From iris.bi Require Export telescopes.
Set Default Proof Using "Type".

(** Small improvements to telescopes *)
Section telescopes.
  Context {PROP : bi} {TT : tele}.

  (** Enable, e.g., [f_equiv] on proofmode goals [(∀.. x, P) -∗ ∀.. x, Q]. *)
  Global Instance bi_tforall_mono' :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_tforall PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_tforall_forall. solve_proper. Qed.

  Global Instance bi_texist_mono' :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_texist PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_texist_exist. solve_proper. Qed.

  (** Enable, e.g., [f_equiv] on goals [(∀.. x, P) -∗ ∀.. x, Q]. *)
  Global Instance bi_tforall_flip_mono' :
    Proper (
      pointwise_relation _ (flip (⊢)) ==>
      (flip (⊢))
    ) (@bi_tforall PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_tforall_forall. solve_proper. Qed.

  Global Instance bi_texist_flip_mono' :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_texist PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_texist_exist. solve_proper. Qed.
End telescopes.
