(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Own instances for iProp and monPred **)
(* TODO: these should be upstreamed to Iris. *)
Require Export iris.si_logic.bi.
Require Import iris.bi.monpred.

Require Export iris.base_logic.lib.own. (* << exporting [inG] and [gFunctors] *)

Require Export bedrock.lang.bi.own.

(* Instances for iProp *)

(* Embedding of si in iProp. It seems that such an embedding doesn't exist
  upstream yet. *)
Section si_embedding.
  Context {Σ : gFunctors}.

  #[local] Arguments siProp_holds !_ _ /.
  #[local] Arguments uPred_holds !_ _ _ /.

  Notation iPropI := (iPropI Σ).
  Notation iProp  := (iProp Σ).

  #[global] Program Instance si_embed : Embed siPropI iPropI :=
    λ P, {| uPred_holds n x := P n |}.
  Solve Obligations with naive_solver eauto using siProp_closed.

  #[global] Instance si_embed_mono : Proper ((⊢) ==> (⊢)) (@embed siPropI _ _).
  Proof. intros ?? PQ. constructor => ??? /=. by apply PQ. Qed.

  #[global] Instance si_embed_ne : NonExpansive (@embed siPropI _ _).
  Proof. intros ??? EQ. constructor => ???? /=. by apply EQ. Qed.

  Program Definition si_unembed (P : iProp) : siProp :=
    {| siProp_holds n := P n ε |}.
  Next Obligation. simpl. intros P n1 n2 ??. by eapply uPred_mono; eauto. Qed.
  Instance si_unembed_ne : NonExpansive si_unembed.
  Proof. intros ??? EQ. constructor => ??. rewrite /=. by apply EQ. Qed.

  Lemma si_embed_unembed (P : siProp) : si_unembed (embed P) ≡ P.
  Proof. by constructor. Qed.

  #[local] Ltac unseal :=
    rewrite /bi_emp /= /uPred_emp /= ?uPred_pure_eq /=
            /bi_emp /= /siProp_emp /= ?siProp_pure_eq /=
            /bi_impl /= ?uPred_impl_eq /bi_impl /= ?siProp_impl_eq /=
            /bi_forall /= ?uPred_forall_eq /= /bi_forall /= ?siProp_forall_eq /=
            /bi_exist /= ?siProp_exist_eq /bi_exist /= ?uPred_exist_eq /=
            /bi_sep /= /siProp_sep ?siProp_and_eq /bi_sep /= ?uPred_sep_eq /=
            /bi_wand /= ?uPred_wand_eq /bi_wand /= /siProp_wand ?siProp_impl_eq /=
            /bi_persistently /= /siProp_persistently /bi_persistently /=
            ?uPred_persistently_eq.
  #[local] Ltac unseal' := constructor => ???; unseal.

  Definition siProp_embedding_mixin : BiEmbedMixin siPropI iPropI si_embed.
  Proof.
    split; try apply _.
    - intros P [EP]. constructor => ??. apply (EP _ ε). done. by unseal.
    - intros PROP' IN P Q.
      rewrite -{2}(si_embed_unembed P) -{2}(si_embed_unembed Q).
      apply (f_equivI si_unembed).
    - by unseal'.
    - intros ??. unseal' => PQ ??. eapply PQ; [done..|by eapply cmra_validN_le].
    - intros A Φ. by unseal'.
    - intros A Φ. by unseal'.
    - intros P Q. unseal'. split; last naive_solver.
      intros []. exists ε. eexists. by rewrite left_id.
    - intros P Q. unseal' => PQ ??.
      apply (PQ _ ε); [done|rewrite right_id; by eapply cmra_validN_le].
    - intros P. by unseal'.
  Qed.

  #[global] Instance siProp_bi_embed : BiEmbed siPropI iPropI :=
    {| bi_embed_mixin := siProp_embedding_mixin |}.
  #[global] Instance siProp_bi_embed_emp : BiEmbedEmp siPropI iPropI.
  Proof. constructor. intros. by rewrite /bi_emp /= /uPred_emp uPred_pure_eq. Qed.
End si_embedding.

Section iprop_instances.
  Context `{Hin: inG Σ A}.

  Notation iPropI := (iPropI Σ).

  Definition has_own_iprop_def : HasOwn iPropI A := {|
    own := base_logic.lib.own.own ;
    own_op := base_logic.lib.own.own_op ;
    own_mono := base_logic.lib.own.own_mono ;
    own_ne := base_logic.lib.own.own_ne ;
    own_timeless := base_logic.lib.own.own_timeless ;
    own_core_persistent := base_logic.lib.own.own_core_persistent ;
  |}.
  #[local] Definition has_own_iprop_aux : seal (@has_own_iprop_def). Proof. by eexists. Qed.
  #[global] Instance has_own_iprop : HasOwn iPropI A := has_own_iprop_aux.(unseal).
  Definition has_own_iprop_eq :
    @has_own_iprop = @has_own_iprop_def := has_own_iprop_aux.(seal_eq).

  Lemma uPred_cmra_valid_bi_cmra_valid (a : A) :
    (uPred_cmra_valid a) ⊣⊢@{iPropI} bi_cmra_valid a.
  Proof. constructor => n x ? /=. by rewrite si_cmra_valid_eq uPred_cmra_valid_eq. Qed.

  #[global] Instance has_own_valid_iprop : HasOwnValid iPropI A.
  Proof.
    constructor. intros. rewrite -uPred_cmra_valid_bi_cmra_valid.
    by rewrite has_own_iprop_eq /= base_logic.lib.own.own_valid.
  Qed.

  #[global] Instance has_own_update_iprop : HasOwnUpd iPropI A.
  Proof.
    constructor; rewrite has_own_iprop_eq /=.
    - by apply base_logic.lib.own.own_update.
    - setoid_rewrite (bi.affine_affinely (bi_pure _)).
      by apply base_logic.lib.own.own_alloc_strong_dep.
  Qed.
End iprop_instances.

Instance has_own_unit_iprop {Σ} {A : ucmraT} `{Hin: inG Σ A} :
  HasOwnUnit (iPropI Σ) A.
Proof. constructor; rewrite has_own_iprop_eq /=. by apply base_logic.lib.own.own_unit. Qed.


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
