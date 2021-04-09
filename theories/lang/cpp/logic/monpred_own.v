(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Own instances for monPred **)
(* TODO: these should be upstreamed to Iris. *)
Require Import iris.si_logic.bi.
Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.own. (* << exporting [inG] and [gFunctors] *)

Require Import bedrock.lang.bi.own.
Require Import bedrock.lang.cpp.logic.iprop_own.

(* Instances for monpred *)

Section si_monpred_embedding.
  Context {I : biIndex} {Σ : gFunctors}.

  Notation monPred  := (monPred I (iPropI Σ)).
  Notation monPredI := (monPredI I (iPropI Σ)).

  #[local] Arguments siProp_holds !_ _ /.
  #[local] Arguments uPred_holds !_ _ _ /.

  #[global] Instance si_monpred_embed : Embed siPropI monPredI :=
    λ P, embed (embed P).

  #[local] Ltac un_membed := rewrite /embed /si_monpred_embed /=.

  #[global] Instance si_monpred_embed_mono :
    Proper ((⊢) ==> (⊢)) (@embed siPropI monPredI _).
  Proof. intros ?? PQ. un_membed. by rewrite PQ. Qed.

  #[global] Instance si_monpred_embed_ne : NonExpansive (@embed siPropI monPredI _).
  Proof. un_membed. solve_proper. Qed.

  (* TODO: generalize to embedding of embedding *)
  Definition siProp_monpred_embedding_mixin :
    BiEmbedMixin siPropI monPredI si_monpred_embed.
  Proof.
    split; try apply _; un_membed.
    - intros P. rewrite embed_emp_valid. apply siProp_embedding_mixin.
    - intros PROP' IN P Q.
      rewrite embed_interal_inj; by apply siProp_embedding_mixin.
    - rewrite -embed_emp. apply embed_mono, siProp_embedding_mixin.
    - intros P Q. rewrite -embed_impl. apply embed_mono, siProp_embedding_mixin.
    - intros A Φ. rewrite -embed_forall. apply embed_mono, siProp_embedding_mixin.
    - intros A Φ. rewrite -embed_exist. apply embed_mono, siProp_embedding_mixin.
    - intros P Q. rewrite -embed_sep. apply embed_proper, siProp_embedding_mixin.
    - intros P Q. rewrite -embed_wand. apply embed_mono, siProp_embedding_mixin.
    - intros P. rewrite -embed_persistently.
      apply embed_proper, siProp_embedding_mixin.
  Qed.

  #[global] Instance siProp_bi_monpred_embed : BiEmbed siPropI monPredI :=
    {| bi_embed_mixin := siProp_monpred_embedding_mixin |}.
  #[global] Instance siProp_bi_monpred_embed_emp : BiEmbedEmp siPropI monPredI.
  Proof.
    rewrite /BiEmbedEmp /bi_embed_embed /si_monpred_embed /=.
    rewrite -embed_emp. apply embed_mono. by rewrite -embed_emp_1.
  Qed.
End si_monpred_embedding.

Section monpred_instances.
  Context {I : biIndex} `{Hin: inG Σ A}.

  Notation iPropI   := (iPropI Σ).
  Notation monPred  := (monPred I iPropI).
  Notation monPredI := (monPredI I iPropI).

  (* sealing here should boost performance, but it requires us to re-export
    properties of embedding. *)
  Program Definition has_own_monpred_def : HasOwn monPredI A := {|
    own := λ γ a , ⎡ own γ a ⎤%I |}.
  Next Obligation. intros. by rewrite -embed_sep -own_op. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  #[local] Definition has_own_monpred_aux : seal (@has_own_monpred_def). Proof. by eexists. Qed.
  #[global] Instance has_own_monpred : HasOwn monPredI A := has_own_monpred_aux.(unseal).
  Definition has_own_monpred_eq :
    @has_own_monpred = @has_own_monpred_def := has_own_monpred_aux.(seal_eq).

  #[local] Ltac unseal_monpred :=
    constructor; intros; rewrite /own has_own_monpred_eq /has_own_monpred_def; red.

  #[global] Instance has_own_valid_monpred: HasOwnValid monPredI A.
  Proof. unseal_monpred. by rewrite own_valid. Qed.

  #[global] Instance has_own_update_monpred : HasOwnUpd monPredI A.
  Proof.
    unseal_monpred.
    - by rewrite -embed_bupd -own_update.
    - setoid_rewrite <-(@embed_pure iPropI).
      setoid_rewrite <-embed_affinely.
      setoid_rewrite <-(@embed_sep iPropI).
      setoid_rewrite <-embed_exist. rewrite -embed_bupd -(@embed_emp iPropI).
      by rewrite -own_alloc_strong_dep.
  Qed.

  (* some re-exporting of embedding properties *)
  #[global] Instance monPred_own_objective γ (a : A) :
    Objective (own γ a).
  Proof. rewrite has_own_monpred_eq. apply _. Qed.
End monpred_instances.

Instance has_own_unit_monpred {I : biIndex} {Σ} {A : ucmraT} `{Hin: inG Σ A} :
  HasOwnUnit (monPredI I (iPropI Σ)) A.
Proof.
  constructor; intros; rewrite /own has_own_monpred_eq /has_own_monpred_def; red.
  by rewrite -(@embed_emp (iPropI _)) -embed_bupd own_unit.
Qed.
