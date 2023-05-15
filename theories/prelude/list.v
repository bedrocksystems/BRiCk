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

(** ** Type-level list quantifier *)

Inductive ForallT {A} (P : A -> Type) : list A -> Type :=
| ForallT_nil : ForallT P []
| ForallT_cons x l : P x -> ForallT P l -> ForallT P (x :: l).

Definition ForallT_true {A} (P : A -> Type) (go : ∀ x, P x) : ∀ l, ForallT P l :=
  fix go_list l :=
  match l with
  | [] => ForallT_nil _
  | x :: l => ForallT_cons _ _ _ (go x) (go_list l)
  end.

(** ** Teach [set_solver] to reason about more list operations, similarly to set
operations. *)

(* Upstreamed in https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/366 *)
#[global] Instance set_unfold_list_bind {A B} (f : A → list B) l P Q y :
  (∀ x, SetUnfoldElemOf x l (P x)) → (∀ x, SetUnfoldElemOf y (f x) (Q x)) →
  SetUnfoldElemOf y (l ≫= f) (∃ x, Q x ∧ P x).
Proof. constructor. rewrite elem_of_list_bind. naive_solver. Qed.

#[global] Instance list_bind_mono {A B} :
  Proper (pointwise_relation _ (⊆) ==> (⊆) ==> (⊆))
    (mbind (M := list) (A := A) (B := B)).
Proof. rewrite /pointwise_relation =>f1 f2 Hf xs1 xs2 Hxs. set_solver. Qed.

#[global] Instance list_bind_perm {A B} :
  Proper (pointwise_relation _ Permutation ==> Permutation ==> Permutation)
    (mbind (M := list) (A := A) (B := B)).
Proof. move =>f1 f2 Hf xs _ <-. elim: xs => [//|x xs IH]; csimpl. by rewrite {}IH (Hf x). Qed.

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

Lemma foldr_rev {A B} (f : B -> A -> A) acc l :
  foldr f acc (rev l) = foldl (fun acc x => f x acc) acc l.
Proof. move: acc. induction l=>acc //=. by rewrite foldr_app IHl. Qed.
Lemma foldl_rev {A B} (f : A -> B -> A) acc l :
  foldl f acc (rev l) = foldr (fun x acc => f acc x) acc l.
Proof. by rewrite -foldr_rev rev_involutive. Qed.

(* From stdlib's [repeat] to stdpp's [replicate]. *)
Lemma repeat_replicate {A} (x : A) n :
  repeat x n = replicate n x.
Proof. by elim: n => [//| n /= ->]. Qed.

Section list.
  Context {A : Type}.
  Implicit Types (l k xs : list A) (i j : nat).

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

  Lemma list_alter_insert l i f :
    alter f i l = if l !! i is Some x then <[i:=f x]> l else l.
  Proof.
    elim: l i => [//|x l IHl] [//|i]; csimpl.
    rewrite IHl. by case_match.
  Qed.

  Lemma list_filter_empty_iff xs `(∀ x, Decision (P x)) :
    filter P xs = [] ↔ List.Forall (λ x, ¬P x) xs.
  Proof.
    elim: xs => [//|x xs IH] /=.
    rewrite filter_cons Forall_cons.
    case_decide; naive_solver.
  Qed.

  (** List variant of
  << map_filter_insert : ...
    filter P (<[i:=x]> m) =
      if decide (P (i, x))
        then <[i:=x]> (filter P m)
        else filter P (delete i m) ].
  In the [P x] branch, we cannot reuse [<[i:=x]> (filter P m)]:
  [x] must be inserted not at position [i] but [length (filter P (take i xs))].
  Instead, we use an alternative version. *)
  Lemma list_filter_insert i x xs P `(∀ x, Decision (P x)) :
    i < length xs →
    filter P (<[i:=x]> xs) =
      if decide (P x) then
        filter P (take i xs) ++ [x] ++ filter P (drop (S i) xs)
      else
        filter P (delete i xs).
  Proof.
    move=> Hle; rewrite insert_take_drop // delete_take_drop.
    by rewrite !(filter_app, filter_cons, filter_nil); case_decide.
  Qed.

  (** Properties of [list_fmap] *)
  Lemma list_fmap_filter {B} P Q xs (f : A -> B)
      `(∀ x, Decision (P x)) `(∀ x, Decision (Q x)) :
    (∀ x, P x <-> Q (f x)) →
    f <$> filter P xs = filter Q (f <$> xs).
  Proof.
    move=> Heq. elim: xs => [//|x xs IH]; csimpl; rewrite !filter_cons.
    repeat case_decide; csimpl; rewrite IH; naive_solver.
  Qed.

  Lemma list_fmap_id' l (f : A -> A):
    (forall x, f x = x) -> f <$> l = l.
  Proof. move => ?. elim: l => // ?? {2}<-. csimpl. by f_equal. Qed.

  (** Properties of [list_delete] *)
  Lemma list_delete_elem_of_1 l i x y:
    l !! i = Some y -> x ≠ y ->
    x ∈ l -> x ∈ delete i l.
  Proof. move => Hl ?. rewrite {1}(delete_Permutation _ _ _ Hl). set_solver. Qed.

  Lemma list_delete_elem_of_2 l x i:
    x ∈ delete i l -> x ∈ l.
  Proof. elim: l i => // a l IH [ |i]/=; set_solver. Qed.

  (** Properties of [NoDup] *)
  Lemma NoDup_Permutation' l k:
    NoDup l -> length l = length k -> (∀ x : A, x ∈ l -> x ∈ k) → l ≡ₚ k.
  Proof.
    move => ???. apply submseteq_length_Permutation; last lia.
    by apply NoDup_submseteq.
  Qed.

  Lemma NoDup_not_in_delete l i x:
    NoDup l -> l !! i = Some x -> x ∉ delete i l.
  Proof. move => + Hin. by rewrite {1}(delete_Permutation _ _ _ Hin) => /NoDup_cons[??]. Qed.
End list.

#[global] Hint Resolve NoDup_nil_2 | 0 : core.
#[global] Hint Resolve NoDup_cons_2 : core.
#[global] Hint Resolve not_elem_of_nil | 0 : core.

Section lists.
  Context {A B : Type}.
  Implicit Types (xs : list A) (ys : list B).

  Section zip_with.
    Context {C : Type}.

    Lemma NoDup_zip_with_fst_gen xs ys (f : A -> B -> C) :
      (∀ x1 x2 y1 y2, f x1 y1 = f x2 y2 -> x1 = x2) ->
      NoDup xs → NoDup (zip_with f xs ys).
    Proof.
      move=> Hinj. elim: xs ys => /= [//|x xs IHxs] [//|y ys] /NoDup_cons [Hni Hnd].
      apply NoDup_cons, conj, IHxs, Hnd.
      intros ?%elem_of_zip_with. naive_solver.
    Qed.

    Lemma NoDup_zip_with_fst_inj xs ys (f : A -> B -> C) `{!Inj2 eq eq eq f} :
      NoDup xs → NoDup (zip_with f xs ys).
    Proof. apply NoDup_zip_with_fst_gen. naive_solver. Qed.

    Lemma NoDup_zip_with_snd_gen xs ys (f : A -> B -> C) :
      (∀ x1 x2 y1 y2, f x1 y1 = f x2 y2 -> y1 = y2) ->
      NoDup ys → NoDup (zip_with f xs ys).
    Proof.
      move=> Hinj. elim: xs ys => /= [//|x xs IHxs] [//|y ys] /NoDup_cons [Hni Hnd].
      apply NoDup_cons, conj, IHxs, Hnd.
      intros ?%elem_of_zip_with. naive_solver.
    Qed.

    Lemma NoDup_zip_with_snd_inj xs ys `(f : A -> B -> C) `{!Inj2 eq eq eq f} :
      NoDup ys → NoDup (zip_with f xs ys).
    Proof. apply NoDup_zip_with_snd_gen. naive_solver. Qed.
  End zip_with.

  Lemma NoDup_zip_fst xs ys :
    NoDup xs → NoDup (zip xs ys).
  Proof. exact: NoDup_zip_with_fst_inj. Qed.

  Lemma NoDup_zip_snd xs ys :
    NoDup ys → NoDup (zip xs ys).
  Proof. exact: NoDup_zip_with_snd_inj. Qed.

  Lemma elem_of_zip x1 x2 xs ys :
    (x1, x2) ∈ zip xs ys → x1 ∈ xs ∧ x2 ∈ ys.
  Proof. intros. eauto using elem_of_zip_l, elem_of_zip_r. Qed.

  (** Properties of [Forall] *)

  (** Strengthens [mapM_fmap_Some_inv] by weakening the second premiss *)
  Lemma mapM_fmap_Forall_Some_inv (f : A -> option B) (g : B -> A) l k :
    mapM f l = Some k ->
    Forall (fun x => ∀ y, f x = Some y -> g y = x) l ->
    g <$> k = l.
  Proof.
    intros Hmap Hl. have Hlen := mapM_length _ _ _ Hmap.
    apply mapM_Some_1 in Hmap. elim: Hl k Hmap Hlen; intros.
    - by rewrite (nil_length_inv k).
    - decompose_Forall_hyps. auto with f_equal.
  Qed.

  Lemma Forall_fmap_fmap_1 (f : A -> B) (g : B -> A) l :
    Forall (fun x => g (f x) = x) l -> g <$> (f <$> l) = l.
  Proof.
    intros. rewrite -list_fmap_compose -{2}(list_fmap_id l).
    exact: Forall_fmap_ext_1.
  Qed.

  Lemma Forall_fmap_fmap (f : A -> B) (g : B -> A) l :
    Forall (fun x => g (f x) = x) l <-> g <$> (f <$> l) = l.
  Proof.
    split; first apply Forall_fmap_fmap_1.
    rewrite -list_fmap_compose -{2}(list_fmap_id l).
    by rewrite -Forall_fmap_ext.
  Qed.
End lists.

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

Lemma not_elem_of_list_lookup {A} {i} {xs : list A} {x} y :
  xs !! i = Some x → y ∉ xs → x ≠ y.
Proof. intros Hl Hni ->. eapply Hni, elem_of_list_lookup_2, Hl. Qed.

Lemma list_difference_delete `{EqDecision A} i (x : A) (xs : list A) :
  xs !! i = Some x →
  NoDup xs -> (* Needed because [list_difference xs [x]] removes all occurrences of [x]. *)
  list_difference xs [x] = delete i xs.
Proof.
  elim: xs i => [//|y xs /= IHxs] [[->] |i /= Hl] /NoDup_cons [Hni HnoDup] /=. {
    by rewrite decide_True ?list_difference_singleton_not_in ?elem_of_list_singleton.
  }
  rewrite decide_False ?(IHxs i) // elem_of_list_singleton.
  by have := not_elem_of_list_lookup _ Hl Hni.
Qed.

Lemma list_remove_delete `{EqDecision A} i (x : A) (xs : list A) :
  xs !! i = Some x →
  NoDup xs -> (* Needed because [i] might not be the first occurrence. *)
  list_remove x xs = Some (delete i xs).
Proof.
  elim: xs i => /= [|y xs IHxs] // [/= [->]|i /= Hl] //= /NoDup_cons [Hni HnoDup].
  { by rewrite decide_True. }
  rewrite decide_False ?(IHxs i Hl) //.
  by have := not_elem_of_list_lookup _ Hl Hni.
Qed.

Lemma list_difference_remove `{EqDecision A} (x : A) (xs : list A) :
  x ∈ xs →
  NoDup xs ->
  list_remove x xs = Some (list_difference xs [x]).
Proof.
  intros [i Hl]%elem_of_list_lookup_1 HnoDup.
  by rewrite !(list_remove_delete i, list_difference_delete i).
Qed.

#[global] Instance map_Inj A B (f : A -> B) : Inj eq eq f -> Inj eq eq (map f).
Proof.
  move=>Hinj x.
  induction x; induction y; first done.
  - by move=>H; case:( nil_cons H).
  - by rewrite eq_comm; move=>H; case:( nil_cons H).
  - by move=>[/Hinj<-/IHx->].
Qed.
