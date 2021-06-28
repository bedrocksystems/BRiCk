(*
 * Copyright (C) BedRock Systems Inc. 2020-21
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *)
Require Import bedrock.lang.algebra.telescopes.
Require Export iris.bi.telescopes.
Require Export bedrock.lang.bi.prelude.
Require iris.proofmode.class_instances.
Import ChargeNotation.

#[local] Set Universe Polymorphism.
#[local] Set Printing Universes.
#[local] Set Printing Coercions.

(** Analogues of [bi_texist] and [bi_tforall], with extra universe
polymorphism and a slightly different interface. *)
Fixpoint tbi_exist@{X Z Y} {PROP : bi} {t : tele@{X}}
  : forall (P : tele_fun@{X Z Y} t PROP), PROP :=
  match t as t0 return ((t0 -t> PROP) → PROP) with
  | [tele] => fun x : PROP => x
  | @TeleS X binder =>
    fun P : (∀ x : X, binder x -t> PROP) => Exists x : X, tbi_exist (P x)
  end.

Fixpoint tbi_forall@{X Z Y} {PROP : bi} {t : tele@{X}}
  : forall (P : tele_fun@{X Z Y} t PROP), PROP :=
  match t as t0 return ((t0 -t> PROP) → PROP) with
  | [tele] => fun x : PROP => x
  | @TeleS X binder =>
    fun P : (∀ x : X, binder x -t> PROP) => Forall x : X, tbi_forall (P x)
  end.

(** Small improvements to [bi_tforall], [bi_texist] *)
Section telescopes.
  Context {PROP : bi} {TT : tele}.

  (** Enable, e.g., [f_equiv] on proofmode goals [(∀.. x, P) -∗ ∀.. x, Q]. *)
  #[global] Instance bi_tforall_mono' :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_tforall PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_tforall_forall. solve_proper. Qed.

  #[global] Instance bi_texist_mono' :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_texist PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_texist_exist. solve_proper. Qed.

  (** Enable, e.g., [f_equiv] on goals [(∀.. x, P) -∗ ∀.. x, Q]. *)
  #[global] Instance bi_tforall_flip_mono' :
    Proper (
      pointwise_relation _ (flip (⊢)) ==>
      (flip (⊢))
    ) (@bi_tforall PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_tforall_forall. solve_proper. Qed.

  #[global] Instance bi_texist_flip_mono' :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_texist PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_texist_exist. solve_proper. Qed.
End telescopes.

Section tele_fun_quantifiers.
  Context {PROP : bi}.
  Implicit Types t : tele.

  Lemma tbi_exist_bi_texist {t} (P : t -t> PROP) : tbi_exist P -|- ∃.. x, tele_app P x.
  Proof. induction t as [|?? IH]; simpl; first done. f_equiv=>x. by rewrite IH. Qed.
  Lemma bi_texist_tbi_exist {t} (R : t -> PROP) : (∃.. x, R x) -|- tbi_exist (tele_bind R).
  Proof. rewrite tbi_exist_bi_texist. f_equiv=>x. by rewrite tele_app_bind. Qed.
  Lemma tbi_exist_exist {t} (P : t -t> PROP) : tbi_exist P -|- Exists x, tele_app P x.
  Proof. by rewrite tbi_exist_bi_texist bi_texist_exist. Qed.

  Lemma tbi_forall_bi_tforall {t} (P : t -t> PROP) : tbi_forall P -|- ∀.. x, tele_app P x.
  Proof. induction t as [|?? IH]; simpl; first done. f_equiv=>x. by rewrite IH. Qed.
  Lemma bi_tforall_tbi_forall {t} (R : t -> PROP) : (∀.. x, R x) -|- tbi_forall (tele_bind R).
  Proof. rewrite tbi_forall_bi_tforall. f_equiv=>x. by rewrite tele_app_bind. Qed.
  Lemma tbi_forall_forall {t} (P : t -t> PROP) : tbi_forall P -|- Forall x, tele_app P x.
  Proof. by rewrite tbi_forall_bi_tforall bi_tforall_forall. Qed.

  #[global] Instance tbi_exist_ne t : NonExpansive (@tbi_exist PROP t).
  Proof. intros n P Q ?. rewrite !tbi_exist_exist. solve_proper. Qed.
  #[global] Instance tbi_exist_proper t : Proper (equiv ==> equiv) (@tbi_exist PROP t).
  Proof.
    apply ne_proper.
    (** TODO: Typeclass resolution here takes a long time to find
        [tbi_exist_ne] because it first tries [contractive_ne]. Can
        similarly slow searches arise downstream? *)
    apply tbi_exist_ne.
  Qed.

  #[global] Instance tbi_forall_ne t : NonExpansive (@tbi_forall PROP t).
  Proof. intros n P Q ?. rewrite !tbi_forall_forall. solve_proper. Qed.
  #[global] Instance tbi_forall_proper t : Proper (equiv ==> equiv) (@tbi_forall PROP t).
  Proof. apply ne_proper, tbi_forall_ne. Qed.
End tele_fun_quantifiers.

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
