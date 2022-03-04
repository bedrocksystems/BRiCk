(*
 * Copyright (C) BedRock Systems Inc. 2021
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(*
 * The following code contains code derived from code original to the
 * stdpp project. That original code is
 *
 *	Copyright stdpp developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original stdpp License:
 * https://gitlab.mpi-sws.org/iris/stdpp/-/blob/221197c43d43ce34b211068b84eff0ec4a9ee57a/LICENSE
 *)

Require Export stdpp.list.
From bedrock.prelude Require Import base numbers.
Export bedrock.prelude.base.

(** * Small extensions to [stdpp.list]. *)

(** ** Teach [set_solver] to reason about more list operations, similarly to set
operations. *)

(* Upstreamed in https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/366 *)
#[global] Instance set_unfold_list_bind {A B} (f : A → list B) l P Q y :
  (∀ x, SetUnfoldElemOf x l (P x)) → (∀ x, SetUnfoldElemOf y (f x) (Q x)) →
  SetUnfoldElemOf y (l ≫= f) (∃ x, Q x ∧ P x).
Proof. constructor. rewrite elem_of_list_bind. naive_solver. Qed.

(* To upstream, based on upstream [set_unfold_filter]. *)
#[global] Instance set_unfold_list_filter
    {A} (P : A → Prop) `{!∀ x, Decision (P x)}
    (xs : list A) Q x :
  SetUnfoldElemOf x xs Q →
  SetUnfoldElemOf x (filter P xs) (P x ∧ Q).
Proof. constructor. rewrite elem_of_list_filter. set_solver. Qed.

#[global] Instance set_unfold_list_difference `{EqDecision A} (x : A) l k P Q :
  SetUnfoldElemOf x l P → SetUnfoldElemOf x k Q →
  SetUnfoldElemOf x (list_difference l k) (P ∧ ¬ Q).
Proof. constructor. rewrite elem_of_list_difference. set_solver. Qed.

#[global] Instance set_unfold_list_intersection `{EqDecision A} (x : A) l k P Q :
  SetUnfoldElemOf x l P → SetUnfoldElemOf x k Q →
  SetUnfoldElemOf x (list_intersection l k) (P ∧ Q).
Proof. constructor. rewrite elem_of_list_intersection. set_solver. Qed.

#[global] Instance set_unfold_list_union `{EqDecision A} (x : A) l k P Q :
  SetUnfoldElemOf x l P → SetUnfoldElemOf x k Q →
  SetUnfoldElemOf x (list_union l k) (P ∨ Q).
Proof. constructor. rewrite elem_of_list_union. set_solver. Qed.

#[global] Instance set_unfold_list_intersection_with `{EqDecision A} (y : A) l k P Q R f :
  (∀ x, SetUnfoldElemOf x l (P x)) → (∀ x, SetUnfoldElemOf x k (Q x)) →
  (∀ x1 x2, SetUnfold (f x1 x2 = Some y) (R x1 x2)) →
  SetUnfoldElemOf y (list_intersection_with f l k) (∃ x1 x2 : A, P x1 ∧ Q x2 ∧ R x1 x2).
Proof. constructor. rewrite elem_of_list_intersection_with. set_solver. Qed.

(* [list_union_with] does not exist. *)

#[global] Instance set_unfold_in {A} (x : A) l P :
  SetUnfoldElemOf x l P → SetUnfold (In x l) P.
Proof. constructor. rewrite -elem_of_list_In. set_solver. Qed.

#[global] Instance set_unfold_list_ret {A} (x y : A) P :
  SetUnfold (x = y) P →
  SetUnfoldElemOf x (mret (M := list) y) P.
Proof. constructor. rewrite elem_of_list_ret. set_solver. Qed.

#[global] Instance set_unfold_list_mjoin {A} (x : A) (xss : list (list A)) P Q :
  (∀ xs, SetUnfoldElemOf x xs (P xs)) → (∀ xs, SetUnfoldElemOf xs xss (Q xs)) →
  SetUnfoldElemOf x (mjoin (M := list) xss) (∃ xs, P xs ∧ Q xs).
Proof. constructor. rewrite elem_of_list_join. set_solver. Qed.

#[global] Instance set_unfold_list_omap {A B} (y : B) xs (f : A → option B) P Q :
  (∀ x, SetUnfoldElemOf x xs (P x)) → (∀ x, SetUnfold (f x = Some y) (Q x)) →
  SetUnfoldElemOf y (omap (M := list) f xs) (∃ x : A, P x ∧ Q x).
Proof. constructor. rewrite elem_of_list_omap. set_solver. Qed.

(*
Outside this theory remain [elem_of_list_split*], [elem_of_list_lookup] and
[elem_of_list_lookup_total].

Of those, [elem_of_list_lookup] seems interesting but might be a breaking
change.
*)

Lemma foldr_cons {A B} (f : A -> B -> B) x y ys : foldr f x (y :: ys) = f y (foldr f x ys).
Proof. done. Qed.

(* From stdlib's [repeat] to stdpp's [replicate]. *)
Lemma repeat_replicate {A} (x : A) n :
  repeat x n = replicate n x.
Proof. by elim: n => [//| n /= ->]. Qed.

Lemma elem_of_seq (len start n : nat) :
  n ∈ seq start len ↔ start <= n < start + len.
Proof. by rewrite elem_of_list_In in_seq. Qed.

Section list.
  Context {A : Type}.
  Implicit Types l k : list A.

  Lemma fmap_ext_in {B} (f g : A → B) l :
    (∀ a : A, a ∈ l → f a = g a) → f <$> l = g <$> l.
  Proof.
    elim: l => [//|x l IHl Hext]; cbn; f_equiv.
    { apply Hext, elem_of_cons, or_introl, eq_refl. }
    apply IHl => y Hin. apply Hext, elem_of_cons, or_intror, Hin.
  Qed.

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

  Lemma list_difference_singleton_not_in l x :
    x ∉ l -> list_difference l [x] = l.
  Proof.
    elim: l => /= [//|y l IHl] /not_elem_of_cons [Hne Hni].
    rewrite decide_False.
    2: { by intros ->%elem_of_list_singleton. }
    f_equal. apply IHl, Hni.
  Qed.

End list_difference.

#[deprecated(note="Use list_difference_singleton_not_in")]
Notation list_difference_id := list_difference_singleton_not_in.

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

(* Make [take 0 xs] reduce with [cbn] *)
#[global] Arguments take : simpl nomatch.

Lemma head_Some_elem_of {A} (x : A) (xs : list A) : head xs = Some x → x ∈ xs.
Proof. destruct xs => [//|[->]]. by apply elem_of_cons; left. Qed.

Lemma list_empty_eq_ext {A} (xs : list A) :
  (∀ x : A, x ∈ xs ↔ False) ↔ xs = [].
Proof. case: xs; set_solver. Qed.

Lemma list_singleton_eq_ext {A} (x : A) xs (HnoDup : NoDup xs) :
  (∀ y, y ∈ xs ↔ y = x) ↔ xs = [x].
Proof.
  split => [H | -> y]; last by set_solver.
  apply symmetry, Permutation_singleton_l, NoDup_Permutation;
    [apply NoDup_singleton|done|..] => z.
  set_solver.
Qed.
