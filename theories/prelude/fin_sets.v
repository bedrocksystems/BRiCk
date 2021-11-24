(*
 * Copyright (C) BedRock Systems Inc. 2020-21
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.fin_sets.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.sets.

(** * Small extensions to [stdpp.fin_sets]. *)

(** TODO: Drop this once it lands in stdpp. *)
#[global] Instance: Params (@set_map) 8 := {}.
Section finset.
  #[local] Set Default Proof Using "Type*".
  Context `{FinSet A C}.
  Implicit Types X Y : C.

  Lemma set_not_elem_of x Y `{Hdec : Decision (x ∈ Y)} : ¬ (x ∉ Y) ↔ x ∈ Y.
  Proof. split. by destruct Hdec. by destruct Hdec; auto. Qed.

  Lemma set_not_Forall (P : A -> Prop) `{Hdec : !∀ x, Decision (P x)} X :
    ¬ set_Forall P X <-> exists x, x ∈ X /\ ¬ P x.
  Proof.
    rewrite set_Forall_elements. split.
    - rewrite/Decision in Hdec. move=>/neg_Forall_Exists_neg-/(_ Hdec)/Exists_exists.
      intros (x & ?%elem_of_elements & ?). by exists x.
    - intros (x & ?%elem_of_elements & ?). move/Forall_forall. auto.
  Qed.

  (** Witnesses for non-disjoint finite sets *)
  Lemma set_not_disjoint X Y `{!∀ x, Decision (x ∈ Y)} :
    ¬ X ## Y <-> exists x, x ∈ X /\ x ∈ Y.
  Proof.
    rewrite set_disjoint_not_Forall_1 set_not_Forall.
    f_equiv=>x. by rewrite set_not_elem_of.
  Qed.

  (* Temporarily imported from new upstream stdpp START. Drop at the next bump *)
  Lemma list_to_set_elements X : list_to_set (elements X) ≡ X.
  Proof. intros ?. rewrite elem_of_list_to_set. apply elem_of_elements. Qed.
  Lemma list_to_set_elements_L `{!LeibnizEquiv C} X : list_to_set (elements X) = X.
  Proof. unfold_leibniz. apply list_to_set_elements. Qed.
  (* Temporarily imported from new upstream stdpp END. *)

  (* In general, the only converse we get is [elements_proper]. *)
  Lemma elements_set_equiv_1 (x y : C) :
    elements x = elements y -> x ≡ y.
  Proof. intros Heq. apply elem_of_equiv => e. by rewrite -!elem_of_elements Heq. Qed.

  Lemma elements_set_equiv_L `{!LeibnizEquiv C} (x y : C) :
    elements x = elements y <-> x = y.
  Proof.
    split; last by [move->]. intros Heq.
    apply leibniz_equiv, elements_set_equiv_1, Heq.
  Qed.

  Lemma size_empty_iff_L `{!LeibnizEquiv C} X : size X = 0 ↔ X = ∅.
  Proof. unfold_leibniz. apply size_empty_iff. Qed.
End finset.

(** [set_seq] *)
Section set_seq.
  Lemma size_set_seq `{FinSet nat C} start len :
    size (set_seq (C:=C) start len) = len.
  Proof.
    revert start; induction len as [|n IH]=>start; csimpl.
    { by rewrite size_empty. }
    rewrite size_union.
    - by rewrite size_singleton IH.
    - rewrite disjoint_singleton_l elem_of_set_seq. lia.
  Qed.
End set_seq.

(** The [set_map] operation *)
Section set_map.
  #[local] Set Default Proof Using "Type*".
  Context `{FinSet A C, Set_ B D}.

  Lemma set_map_disjoint (f : A → B) (X Y : C) :
    (∀ x y, f x = f y → x ∈ X → y ∈ Y → False) →
    set_map (D:=D) f X ## set_map (D:=D) f Y.
  Proof. set_solver. Qed.
  Lemma set_map_disjoint_singleton_l (f : A → B) (x : A) (Y : C) :
    (∀ y, f x = f y → y ∉ Y) → {[f x]} ## set_map (D:=D) f Y.
  Proof. set_solver. Qed.
  Lemma set_map_disjoint_singleton_r (f : A → B) (x : A) (Y : C) :
    (∀ y, f x = f y → y ∉ Y) → set_map (D:=D) f Y ## {[f x]}.
  Proof. set_solver. Qed.

  Lemma set_map_singleton (f : A → B) (x : A) :
    set_map (D:=D) f (singleton (B:=C) x) ≡ {[f x]}.
  Proof. set_solver. Qed.
  Lemma set_map_singleton_L `{!LeibnizEquiv D} (f : A → B) (x : A) :
    set_map (D:=D) f (singleton (B:=C) x) = {[f x]}.
  Proof. unfold_leibniz. apply set_map_singleton. Qed.

  Lemma set_map_union (f : A → B) (X Y : C) :
    set_map (D:=D) f (X ∪ Y) ≡ set_map (D:=D) f X ∪ set_map (D:=D) f Y.
  Proof. set_solver. Qed.
  Lemma set_map_union_L `{!LeibnizEquiv D} (f : A → B) (X Y : C) :
    set_map (D:=D) f (X ∪ Y) = set_map (D:=D) f X ∪ set_map (D:=D) f Y.
  Proof. unfold_leibniz. apply set_map_union. Qed.

  Lemma set_map_empty `{Set_ B D} (f : A -> B) : set_map (C:=C) (D:=D) f ∅ = ∅.
  Proof. rewrite /set_map. by rewrite elements_empty. Qed.
End set_map.

Section set_map.
  #[local] Set Default Proof Using "Type*".
  Context `{FinSet A C, Set_ B D}.

  Lemma set_map_empty_iff `{FinSet B D} (f : A -> B) X :
    set_map (C:=C) (D:=D) f X ≡ ∅ <-> X ≡ ∅.
  Proof.
    split; first last.
    - move=>->. by rewrite set_map_empty.
    - rewrite - !size_empty_iff.
      pattern X. apply set_ind; clear X; first by intros ?? ->.
      { by rewrite size_empty. }
      intros x X Hni IH.
      rewrite set_map_union set_map_singleton.
      rewrite (comm union) size_union_alt.
      intros Hsz.
      assert (size (set_map (D := D) f X) = 0) as Hsz0 by lia.
      exfalso. move: Hsz. rewrite Hsz0 /=.
      have {Hsz0} IH := IH Hsz0; rewrite (size_empty_inv _ IH).
      by rewrite set_map_empty difference_empty size_singleton.
  Qed.

  Lemma set_map_empty_iff_L `{FinSet B D, !LeibnizEquiv C, !LeibnizEquiv D}
      (f : A -> B) X :
    set_map (C:=C) (D:=D) f X = ∅ <-> X = ∅.
  Proof. unfold_leibniz. exact: set_map_empty_iff. Qed.

  Lemma size_map_inj `{FinSet B D} (f : A -> B) `{!Inj (=) (=) f} (X : C) :
    size (C:=D) (set_map f X) = size X.
  Proof.
    pattern X. apply set_ind; clear X.
    { by intros X1 X2 ->. }
    { by rewrite set_map_empty !size_empty. }
    intros x X Hx IH.
    rewrite set_map_union !size_union.
    - by rewrite set_map_singleton !size_singleton IH.
    - intros y ->%elem_of_singleton. by apply Hx.
    - clear IH. rewrite set_map_singleton. intros y ->%elem_of_singleton.
      intros (y & Hy & He)%elem_of_map_1. by simplify_eq.
  Qed.
End set_map.

(** Pairwise disjointness *)
Section fin_set.
  #[local] Set Default Proof Using "Type*".
  Context `{FinSet C D, Disjoint C, !RelDecision (##@{C})}.
  Implicit Types Xs Ys : D.

  #[global] Instance fin_set_pairwise_disjoint_dec : RelDecision (##ₚ@{D}).
  Proof. rewrite/RelDecision. apply _. Defined.

  (** Witnesses for non-pairwise disjoint finite sets *)
  Lemma not_pairwise_disjoint Xs Ys :
    ¬ Xs ##ₚ Ys <-> exists X Y, X ∈ Xs /\ Y ∈ Ys /\ ¬ (X = Y \/ X ## Y).
  Proof.
    rewrite/pairwise_disjoint/set_pairwise_disjoint.
    rewrite set_not_Forall. f_equiv=>X. split.
    - intros (? & (Y & ? & ?)%set_not_Forall); last by apply _. by exists Y.
    - intros (Y & ? & ? & ?). split; first done. rewrite set_not_Forall. by exists Y.
  Qed.
End fin_set.
