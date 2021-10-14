(*
 * Copyright (C) BedRock Systems Inc. 2021
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.list.
From bedrock.prelude Require Import base numbers.
Export bedrock.prelude.base.

(** * Small extensions to [stdpp.list]. *)

Lemma foldr_cons {A B} (f : A -> B -> B) x y ys : foldr f x (y :: ys) = f y (foldr f x ys).
Proof. done. Qed.

(* From stdlib's [repeat] to stdpp's [replicate]. *)
Lemma repeat_replicate {A} (x : A) n :
  repeat x n = replicate n x.
Proof. by elim: n => [//| n /= ->]. Qed.

Lemma repeatN_replicateN {A} (x : A) n :
  repeat x (N.to_nat n) = replicateN n x.
Proof. apply repeat_replicate. Qed.

Lemma repeat_replicateN {A} (x : A) n :
  repeat x n = replicateN (N.of_nat n) x.
Proof. by rewrite repeat_replicate /replicateN Nat2N.id. Qed.

Lemma replicateN_0 {A} (x : A) : replicateN 0 x = [].
Proof. done. Qed.

Lemma replicateN_S {A} (x : A) n : replicateN (N.succ n) x = x :: replicateN n x.
Proof. by rewrite /replicateN/= N2Nat.inj_succ. Qed.

Section list.
  Context {A : Type}.
  Implicit Types l k : list A.

  (** List disjointness is decidable *)
  Section disjoint_dec.
    Notation Disjoint l k :=
      (List.Forall (λ x, List.Forall (x ≠.) k) l) (only parsing).

    #[local] Lemma list_disjoint_alt l k : l ## k <-> Disjoint l k.
    Proof. rewrite Forall_forall. setoid_rewrite Forall_forall. set_solver. Qed.
    #[global] Instance list_disjoint_dec `{EqDecision A} : RelDecision (##@{list A}).
    Proof.
      refine (λ l k, cast_if (decide (Disjoint l k)));
        by rewrite list_disjoint_alt.
    Defined.
  End disjoint_dec.

  (** Witnesses for non-disjoint lists *)
  Lemma list_not_disjoint `{EqDecision A} l k :
    ¬ l ## k <-> exists x, x ∈ l /\ x ∈ k.
  Proof.
    split; last set_solver+. rewrite list_disjoint_alt.
    move/not_Forall_Exists=>/Exists_exists [] x [] ? /=.
    move/not_Forall_Exists=>/Exists_exists [] y [] ? /=.
    destruct (decide (x = y)); [by exists x; simplify_eq|done].
  Qed.
  Lemma disjoint_cons_r l x k : l ## x :: k <-> x ∉ l /\ l ## k.
  Proof. set_solver+. Qed.

  #[local] Lemma not_elem_of_list_alt x l : x ∉ l <-> List.Forall (x ≠.) l.
  Proof. rewrite Forall_forall. set_solver. Qed.
  Lemma not_elem_of_list `{EqDecision A} x l : ¬ (x ∉ l) ↔ x ∈ l.
  Proof.
    split; last set_solver. rewrite not_elem_of_list_alt.
    move/not_Forall_Exists=>/Exists_exists [] y [] Hy /=.
    by destruct (decide (x = y)); simplify_eq.
  Qed.
End list.
#[global] Hint Resolve NoDup_nil_2 | 0 : core.
#[global] Hint Resolve NoDup_cons_2 : core.
#[global] Hint Resolve not_elem_of_nil | 0 : core.

Section list_difference.
  Context `{EqDecision A}.
  Implicit Types l k : list A.
  Implicit Types x y : A.
  Lemma list_difference_nil_r l : list_difference l [] = l.
  Proof. induction l; simpl; auto with f_equal. Qed.
  Lemma list_difference_cons_r y l k :
    list_difference l (y :: k) =
    list_difference (list_difference l [y]) k.
  Proof.
    induction l as [|x l IH]; [done | ].
    rewrite [RHS]/=. case_decide as Hy.
    { simpl. rewrite decide_True; set_solver. }
    rewrite [RHS]/=. case_decide as Hk; simpl.
    - rewrite decide_True; set_solver.
    - rewrite IH decide_False; set_solver.
  Qed.
  Lemma list_difference_app_r l k1 k2 :
    list_difference l (k1 ++ k2) = list_difference (list_difference l k1) k2.
  Proof.
    revert l. induction k1 as [|y k1 IH]=>l; simpl.
    - by rewrite list_difference_nil_r.
    - by rewrite (list_difference_cons_r y) IH -(list_difference_cons_r y).
  Qed.

  Lemma list_difference_id l x :
    (¬ x ∈ l) ->
    list_difference l [x] = l.
  Proof.
    intros Hin.
    induction l; [ reflexivity | ].
    simpl in *.
    rewrite -> elem_of_cons in Hin.
    rewrite decide_False; [ | intros Hax].
    {
      f_equal. apply IHl. tauto.
    }
    {
      inversion Hax; subst; try tauto.
      by rewrite -> @elem_of_nil in *.
    }
  Qed.

End list_difference.

Lemma tail_length {A} (l : list A):
  length (tail l) <= length l <= length (tail l) + 1.
Proof.
  induction l; simpl; by lia.
Qed.

Lemma tail_length_eq {A} (l : list A):
  0 < length l ->
  length (tail l) + 1 = length l.
Proof.
  intros H.
  destruct l; simpl in *; by lia.
Qed.

Lemma elem_of_replicateN {A} (count : N) (b a : A) : a ∈ replicateN count b → b = a.
Proof. by intros [-> _]%elem_of_replicate. Qed.
