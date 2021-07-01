(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
From iris.bi Require Import bi monpred embedding.
From iris.proofmode Require Import tactics.

(**
[only_provable P], written [ [| P |] ], is a variant of [⌜ P ⌝] that, in a
linear logic, cannot "absorb" any resources.

Hence, if [A ⊢ B ∗ [| P |] ], all resources owned by [A] are owned by [B],
and none are owned by [ [| P |] ].

See also [only_provable_equiv].

For an academic reference on the [<affine>] derived modality and the concept
of "absorbing" propositions, see
"MoSeL: A general, extensible modal framework for interactive proofs in separation logic"
(http://doi.acm.org/10.1145/3236772).
*)
Definition only_provable {PROP : bi} (P : Prop) : PROP := (<affine> ⌜P⌝)%I.
Arguments only_provable {_} _%type_scope : simpl never, rename.
Instance: Params (@only_provable) 1 := {}.

Notation "[ | P | ]" := (only_provable P) (format "[ |  P  | ]").

(** * Properties of [only_provable]. *)
Section bi.
  Context {PROP : bi} `{PF : BiPureForall PROP}.

  Implicit Types P Q : Prop.
  Implicit Types p q r : PROP.
  Local Notation "p ⊢ q" := (p ⊢@{PROP} q) (only parsing).
  Local Notation "p ⊣⊢ q" := (p ⊣⊢@{PROP} q) (only parsing).

  (** [ [| P |] ] indeed holds no resources. This is also an unfolding lemma, since [only_provable] is [Opaque]. *)
  Lemma only_provable_equiv P : [| P |] ⊣⊢ emp ∧ ⌜ P ⌝.
  Proof. done. Qed.

  Global Instance only_provable_ne n :
    Proper (iff ==> dist n) (@only_provable PROP).
  Proof. solve_proper. Qed.
  Global Instance only_provable_proper :
    Proper (iff ==> (⊣⊢)) (@only_provable PROP).
  Proof. solve_proper. Qed.
  Global Instance only_provable_mono' :
    Proper (impl ==> (⊢)) (@only_provable PROP).
  Proof. solve_proper. Qed.
  Global Instance only_provable_flip_mono :
    Proper (flip impl ==> flip (⊢)) (@only_provable PROP).
  Proof. solve_proper. Qed.

  Global Instance only_provable_persistent P : Persistent (PROP:=PROP) [| P |].
  Proof. apply _. Qed.
  Global Instance only_provable_affine P : Affine (PROP:=PROP) [| P |].
  Proof. apply _. Qed.

  (* This is provable, but only usable under `BiAffine`, hence misleading. *)
  Lemma only_provable_absorbing `{BiAffine PROP} P :
    Absorbing (PROP:=PROP) [| P |].
  Proof. apply _. Qed.

  Lemma only_provable_mono P Q : (P → Q) → [| P |] ⊢ [| Q |].
  Proof. apply only_provable_mono'. Qed.
  Lemma only_provable_iff P Q : (P ↔ Q) → [| P |] ⊣⊢ [| Q |].
  Proof. apply only_provable_proper. Qed.
  Lemma only_provable_intro P p `{!Affine p} : P → p ⊢ [| P |].
  Proof. intros ?. apply: bi.affinely_intro. exact: bi.pure_intro. Qed.
  Lemma only_provable_elim' P p : (P → True ⊢ p) → [| P |] ⊢ p.
  Proof. rewrite/only_provable bi.affinely_elim. exact: bi.pure_elim'. Qed.
  Lemma only_provable_elim_l P q r : (P → q ⊢ r) → [| P |] ∧ q ⊢ r.
  Proof. rewrite /only_provable bi.affinely_elim. apply bi.pure_elim_l. Qed.
  Lemma only_provable_elim_r P q r : (P → q ⊢ r) → q ∧ [| P |] ⊢ r.
  Proof. rewrite comm. apply only_provable_elim_l. Qed.
  Lemma only_provable_emp : [| True |] ⊣⊢ emp.
  Proof. by rewrite/only_provable bi.affinely_True_emp bi.affinely_emp. Qed.
  Lemma only_provable_True P : P → [| P |] ⊣⊢ emp.
  Proof. intros. by rewrite -only_provable_emp /only_provable bi.pure_True. Qed.
  Lemma only_provable_False P : ¬P → [| P |] ⊣⊢ False.
  Proof.
    intros. by rewrite /only_provable bi.pure_False// bi.affinely_False.
  Qed.
  Lemma only_provable_sep P Q : [|P ∧ Q|] ⊣⊢ [| P |] ∗ [| Q |].
  Proof. apply (anti_symm _); auto. Qed.
  Lemma only_provable_and P Q : [|P ∧ Q|] ⊣⊢ [| P |] ∧ [| Q |].
  Proof. by rewrite -bi.affinely_and -bi.pure_and. Qed.
  Lemma only_provable_or P Q : [|P ∨ Q|] ⊣⊢ [| P |] ∨ [| Q |].
  Proof. by rewrite -bi.affinely_or -bi.pure_or. Qed.
  Lemma only_provable_impl P Q : [|P → Q|] ⊢ ([| P |] → [| Q |]).
  Proof. auto. Qed.
  Lemma only_provable_forall_1 {A} (φ : A → Prop) : [|∀ x, φ x|] ⊢ ∀ x, [|φ x|].
  Proof. auto. Qed.
  Lemma only_provable_forall_2 `{Inhabited A} (φ : A → Prop) :
    (∀ x, [|φ x|]) ⊢ [|∀ x, φ x|].
  Proof using PF.
    rewrite/only_provable/bi_affinely. iIntros "Hφ". iSplit; first done.
    rewrite bi.pure_forall. iIntros (x). iDestruct ("Hφ" $! x) as "[_ $]".
  Qed.
  Lemma only_provable_forall `{Inhabited A} (φ : A → Prop) :
    [|∀ x, φ x|] ⊣⊢ ∀ x, [|φ x|].
  Proof using PF. apply: anti_symm. apply only_provable_forall_1. apply only_provable_forall_2. Qed.
  (** Not very useful, but the best we can do in general:
  it's unclear how to commute [emp ∧ ∀ x : A, P] into [∀ x : A, emp ∧ P]. *)
  Lemma only_provable_forall_2_gen {A} (φ : A → Prop)
    (Hswap : emp ∧ (∀ x : A, [| φ x |]) ⊣⊢ (∀ x : A, [| φ x |])) :
    ([| ∀ x : A, φ x |]) ⊣⊢@{PROP} (∀ x : A, [| φ x |]).
  Proof using PF.
    rewrite -Hswap /only_provable; iSplit.
    { iIntros "!% /=". done. }
    { iIntros "[_ HPQ]". iRevert "HPQ". iIntros "!% /=". done. }
  Qed.
  Lemma only_provable_forall_2_biaffine `{BiAffine PROP} {A} (φ : A → Prop) :
    ([| ∀ x : A, φ x |]) ⊣⊢@{PROP} (∀ x : A, [| φ x |]).
  Proof using PF.
    apply only_provable_forall_2_gen.
    iSplit; [|done]. iIntros "[_ $]".
  Qed.

  Lemma only_provable_exist {A} (φ : A → Prop) : [|∃ x, φ x|] ⊣⊢ ∃ x, [|φ x|].
  Proof. rewrite/only_provable. by rewrite bi.pure_exist bi.affinely_exist. Qed.
  Lemma only_provable_impl_forall P q : ([| P |] → q) ⊢ (∀ _ : P, emp → q).
  Proof. apply bi.forall_intro=>?. by rewrite only_provable_True. Qed.
  Lemma only_provable_alt P : [| P |] ⊣⊢ ∃ _ : P, emp.
  Proof.
    rewrite /only_provable bi.pure_alt bi.affinely_exist.
    do 2!f_equiv. exact: only_provable_emp.
  Qed.
  Lemma only_provable_wand_forall_1 P q : ([| P |] -∗ q) ⊢ (∀ _ : P, q).
  Proof.
    apply bi.forall_intro=>?. by rewrite only_provable_True// left_id.
  Qed.
  Lemma only_provable_wand_forall_2 P q `{!Absorbing q} :
    (∀ _ : P, q) ⊢ ([| P |] -∗ q).
  Proof. by rewrite /only_provable -bi.pure_wand_forall// bi.affinely_elim. Qed.
  Lemma only_provable_wand_forall P q `{!Absorbing q} :
    ([| P |] -∗ q) ⊣⊢ (∀ _ : P, q).
  Proof.
    apply: anti_symm; auto using
      only_provable_wand_forall_1, only_provable_wand_forall_2.
  Qed.

  Lemma persistently_only_provable P : <pers> [| P |] ⊣⊢@{PROP} ⌜ P ⌝.
  Proof. by rewrite /only_provable bi.persistently_affinely_elim bi.persistently_pure. Qed.
  Lemma affinely_only_provable P : <affine> [| P |] ⊣⊢@{PROP} [| P |].
  Proof. by rewrite /only_provable bi.affinely_idemp. Qed.
  Lemma absorbingly_only_provable P : <absorb> [| P |] ⊣⊢@{PROP} ⌜ P ⌝.
  Proof. by rewrite /only_provable bi.persistent_absorbingly_affinely. Qed.

  Lemma intuitionistically_only_provable P : □ [| P |] ⊣⊢@{PROP} [| P |].
  Proof. by rewrite /bi_intuitionistically persistently_only_provable. Qed.
End bi.
#[global] Hint Resolve only_provable_intro : core.

Section bi.
  Context {PROP : bi}.

  Global Instance only_provable_timeless `{BiAffine PROP} P :
    Timeless (PROP:=PROP) [| P |].
  Proof. apply _. Qed.
  Global Instance only_provable_plain `{BiPlainly PROP} P :
    Plain (PROP:=PROP) [| P |].
  Proof. apply _. Qed.
End bi.

Section monpred.
  Context {I : biIndex} {PROP : bi}.

  Global Instance only_provable_objective P : @Objective I PROP [| P |].
  Proof. rewrite/only_provable. apply _. Qed.

  Lemma monPred_at_only_provable (i : I) P :
    monPred_at [| P |] i ⊣⊢@{PROP} [| P |].
  Proof. by rewrite monPred_at_affinely monPred_at_pure. Qed.
End monpred.

Lemma embed_only_provable `{BiEmbedEmp PROP1 PROP2} (P : Prop) :
  embed [| P |] ⊣⊢@{PROP2} [| P |].
Proof. by rewrite embed_affinely embed_pure. Qed.

Section proofmode.
  Context {PROP : bi} {PF: BiPureForall PROP}.

  (**
   * We don't register instances
   *
   * - [@FromAffinely PROP [| P |] ⌜P⌝]
   *
   * - [@IntoAbsorbingly PROP ⌜P⌝ [| P |]]
   *
   * as they would interact poorly with, e.g., [iSplit], changing
   * goals like [[| P |] ** Q] into subgoals involving [bi_pure]
   * rather than [only_provable].
   *)
  Global Instance into_pure_only_provable P : @IntoPure PROP [| P |] P.
  Proof. by rewrite/IntoPure/only_provable bi.affinely_elim. Qed.
  Global Instance from_pure_only_provable P : @FromPure PROP true [| P |] P.
  Proof. by rewrite/FromPure/only_provable. Qed.
  Global Instance into_wand_only_provable p (P : Prop) Q :
    Absorbing Q → @IntoWand PROP p false (∀ _ : P, Q) [| P |] Q.
  Proof.
    intros. rewrite/IntoWand. rewrite (bi.intuitionistically_if_elim p) /=.
    by rewrite -only_provable_wand_forall.
  Qed.
  Global Instance from_and_only_provable P Q :
    @FromAnd PROP [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/FromAnd only_provable_and. Qed.
  Global Instance into_and_only_provable p P Q :
    @IntoAnd PROP p [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/IntoAnd only_provable_and. Qed.
  Global Instance from_sep_only_provable P Q :
    @FromSep PROP [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/FromSep only_provable_sep. Qed.
  Global Instance into_sep_only_provable P Q :
    @IntoSep PROP [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/IntoSep only_provable_sep. Qed.
  Global Instance from_or_only_provable P Q :
    @FromOr PROP [| P ∨ Q |] [| P |] [| Q |].
  Proof. by rewrite/FromOr only_provable_or. Qed.
  Global Instance into_or_only_provable P Q :
    @IntoOr PROP [| P ∨ Q |] [| P |] [| Q |].
  Proof. by rewrite/IntoOr only_provable_or. Qed.
  Global Instance from_exist_only_provable {A} (P : A → Prop) :
    @FromExist PROP A [| ∃ x, P x |] (λ a, [| P a |]).
  Proof. by rewrite/FromExist only_provable_exist. Qed.
  Global Instance into_exist_only_provable {A} (P : A → Prop) name :
    AsIdentName P name ->
    @IntoExist PROP A [| ∃ x, P x |] (λ a, [| P a |]) name.
  Proof. by rewrite/IntoExist only_provable_exist. Qed.

  (* TODO: avoid backtracking between these two instances by adding a TCOrT;
  TCOr does not work because it only takes Props but Inhabited is in Type. *)
  Global Instance from_forall_only_provable
      `{HTC : TCOrT (BiAffine PROP) (Inhabited A)} (P : A → Prop) name :
    AsIdentName P name ->
    @FromForall PROP A [| ∀ x, P x |] (λ a, [| P a |]) name.
  Proof using PF.
    destruct HTC.
    - by rewrite/FromForall only_provable_forall_2_biaffine.
    - by rewrite/FromForall only_provable_forall_2.
  Qed.

  Global Instance into_forall_only_provable {A} (P : A → Prop) :
    @IntoForall PROP A [| ∀ x, P x |] (λ a, [| P a |]).
  Proof. by rewrite/IntoForall only_provable_forall_1. Qed.
End proofmode.
Typeclasses Opaque only_provable.
Global Opaque only_provable.	(** Less important *)
