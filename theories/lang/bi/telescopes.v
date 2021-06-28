(*
 * Copyright (C) BedRock Systems Inc. 2020-21
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *)
Require Export iris.bi.telescopes.
Require Export bedrock.lang.bi.prelude.
Require iris.proofmode.class_instances.

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

(** On [Import], hide IPM instances related to [bi_texist],
    [bi_tforall]. Those instances can impose spurious universe
    constraints when proving universe polymorphic lemmas about
    [tbi_exist], [tbi_forall]. For example, [iDestruct] on a
    hypothesis of the form [tbi_exist@{X Z Y} (tele_bind ...)] uses
    the [IntoExist] instance for [bi_texist] with the side-effect of
    constraining universe [Y] to being below a small universe like
    [Type.0]. *)
Module disable_proofmode_telescopes.
  #[export] Remove Hints
    class_instances.into_exist_texist
    class_instances.from_exist_texist
    class_instances.into_forall_tforall
    class_instances.from_forall_tforall
  : typeclass_instances.
End disable_proofmode_telescopes.
