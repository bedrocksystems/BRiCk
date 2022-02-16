(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** "Prelude" for available-everywhere dependencies. *)

From stdpp Require Export prelude countable.
From bedrock.prelude Require Export stdpp_ssreflect tc_cond_type notations.

#[global] Hint Opaque elem_of : typeclass_instances.

(** Workaround https://github.com/coq/coq/issues/4230. Taken from Software Foundations. *)
#[global] Remove Hints Bool.trans_eq_bool : core.

#[global] Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)
#[global] Set Default Proof Using "Type".
(** Disable [Program]'s compiler for pattern matches.
It's more expressive, but it mangles definitions and can cause a quadratic size
explosion. *)
#[global] Unset Program Cases.
#[global] Set Ltac Backtrace.

(** * Small extensions to [stdpp.base] *)

(** Solve decidable goal [P] via [vm_compute] on [bool_decide P]. *)
Ltac vm_decide := apply: bool_decide_eq_true_1; vm_compute; reflexivity.

Lemma TCElemOf_iff {A} (x : A) (l : list A) : TCElemOf x l ↔ x ∈ l.
Proof. split; induction 1; by constructor. Qed.

Lemma iff_forall T P Q :
  (forall i: T, P i <-> Q i) ->
  (forall i: T, P i) <-> (forall i: T, Q i).
Proof. naive_solver. Qed.

#[global] Instance reflexive_proper A :
  Proper (pointwise_relation A (pointwise_relation A iff) ==> iff) Reflexive.
Proof.
  unfold Reflexive=> r1 r2 Heq.
  apply iff_forall => i. by rewrite Heq.
Qed.

#[global] Instance transitive_proper A :
  Proper (pointwise_relation A (pointwise_relation A iff) ==> iff) Transitive.
Proof.
  unfold Reflexive=> r1 r2 Heq.
  apply iff_forall => i.
  apply iff_forall => j.
  apply iff_forall => k.
  by rewrite Heq.
Qed.

#[global] Instance preorder_proper A :
  Proper (pointwise_relation A (pointwise_relation A iff) ==> iff) PreOrder.
Proof. by intros r1 r2 Heq; split => -[]; [rewrite Heq|rewrite -Heq]. Qed.

(** Not an instance, because of the risk of loops. *)
Lemma flip_assoc {A} {R : relation A} `{!Symmetric R} `{!Assoc R f}: Assoc R (flip f).
Proof. intros ???. symmetry. apply: (assoc f). Qed.

Section flip_app.
  Context {A : Type}.

  #[global] Instance flip_app_left_id : LeftId (=) (@nil A) (flip app).
  Proof. apply: right_id. Qed.
  #[global] Instance flip_app_right_id : RightId (=) (@nil A) (flip app).
  Proof. apply: left_id. Qed.
  #[global] Instance flip_app_assoc : Assoc (=) (flip (@app A)).
  Proof. apply: flip_assoc. Qed.
End flip_app.

(** Not an instance to avoid TC resolution loops *)
Lemma subrelation_flip {A} (R S : relation A) :
  subrelation R S -> subrelation (flip R) (flip S).
Proof. intros HR x y ?. exact: HR. Qed.

Lemma negb_bool_decide `{Hdec : Decision P} : negb (bool_decide P) = bool_decide (not P).
Proof. by case: Hdec. Qed.

(* Very incomplete set of monadic liftings. *)
Definition liftM2 `{MRet M, MBind M} `(f : A → B → C) : M A → M B → M C :=
  λ mx my,
    x ← mx; y ← my; mret (f x y).

(* Less common; name inspired by Haskell. *)
Definition bindM2 `{MBind M} `(f : A → B → M C) : M A → M B → M C :=
  λ mx my,
    x ← mx; y ← my; f x y.

#[global] Notation Unfold x tm :=
  ltac:(let H := eval unfold x in tm in exact H) (only parsing).
#[global] Notation Reduce tm :=
  ltac:(let H := eval red in tm in exact H) (only parsing).
#[global] Notation Hnf tm :=
  ltac:(let H := eval hnf in tm in exact H) (only parsing).
#[global] Notation Cbn tm :=
  ltac:(let H := eval cbn in tm in exact H) (only parsing).
#[global] Notation Beta tm :=
  ltac:(let H := eval cbv beta in tm in exact H) (only parsing).
#[global] Notation Evaluate tm :=
  ltac:(let H := eval vm_compute in tm in exact H) (only parsing).

(**
Useful to force typeclass inference; inspired by math-comp's [!!] notation.
Example:
[suff Hname: Refine (∀ (xs : gset nat), xs ∪ xs = xs).]
*)
#[global] Notation Refine x := (ltac:(refine x)) (only parsing).

(** ** Pairwise disjointness *)
(** Operational type class for pairwise disjointness, with notation
[Xs ##ₚ Ys] and [[##ₚ Xs]]. *)
Class PairwiseDisjoint A := pairwise_disjoint : relation A.
#[global] Hint Mode PairwiseDisjoint ! : typeclass_instances.
#[global] Instance: Params (@pairwise_disjoint) 2 := {}.
Infix "##ₚ" := pairwise_disjoint (at level 70) : stdpp_scope.
Notation "(##ₚ)" := pairwise_disjoint (only parsing) : stdpp_scope.
Notation "( Xs ##ₚ.)" := (pairwise_disjoint Xs) (only parsing) : stdpp_scope.
Notation "(.##ₚ Ys )" := (fun Xs => Xs ##ₚ Ys) (only parsing) : stdpp_scope.

Infix "##ₚ@{ A }" := (@pairwise_disjoint A _) (at level 70, only parsing) : stdpp_scope.
Notation "(##ₚ@{ A } )" := (@pairwise_disjoint A _) (only parsing) : stdpp_scope.

Notation "[##ₚ  Xs ]" := (Xs ##ₚ Xs) (at level 0) : stdpp_scope.
Notation "[##ₚ@{ A }  Xs ]" := (Xs ##ₚ@{A} Xs) (at level 0, only parsing) : stdpp_scope.

(** ** Typeclass operations *)
(** [TCLeq (a ?= b)] expresses [a <= b] in a way that can be proved,
    for some [a]s and [b]s, during typeclass resolution. *)
Variant TCLeq : comparison -> Prop :=
| TCLeq_eq : TCLeq Eq
| TCLeq_lt : TCLeq Lt.
Existing Class TCLeq.
#[global] Existing Instances TCLeq_eq TCLeq_lt.
#[global] Hint Mode TCLeq + : typeclass_instances.

Lemma TCLeq_iff c : TCLeq c <-> c ≠ Gt.
Proof. split. by inversion 1. by destruct c; first [done|constructor]. Qed.
Lemma TCLeq_positive x y : (TCLeq (x ?= y) <-> x <= y)%positive.
Proof. by rewrite TCLeq_iff. Qed.
Lemma TCLeq_Z x y : (TCLeq (x ?= y) <-> x <= y)%Z.
Proof. by rewrite TCLeq_iff. Qed.
Lemma TCLeq_N x y : (TCLeq (x ?= y) <-> x <= y)%N.
Proof. by rewrite TCLeq_iff. Qed.
Lemma TCLeq_nat x y : (TCLeq (x ?= y) <-> x <= y)%nat.
Proof. by rewrite TCLeq_iff Nat.compare_le_iff. Qed.

(** [TCLt (a ?= b)] expresses [a < b] in a way that can be proved,
    for some [a]s and [b]s, during typeclass resolution. *)
Variant TCLt : comparison -> Prop :=
| TCLt_lt : TCLt Lt.
Existing Class TCLt.
#[global] Existing Instance TCLt_lt.
#[global] Hint Mode TCLt + : typeclass_instances.

Lemma TCLt_iff c : TCLt c <-> c = Lt.
Proof. split. by destruct 1. by intros ->. Qed.
Lemma TCLt_positive x y : (TCLt (x ?= y) <-> x < y)%positive.
Proof. by rewrite TCLt_iff. Qed.
Lemma TCLt_Z x y : (TCLt (x ?= y) <-> x < y)%Z.
Proof. by rewrite TCLt_iff. Qed.
Lemma TCLt_N x y : (TCLt (x ?= y) <-> x < y)%N.
Proof. by rewrite TCLt_iff. Qed.
Lemma TCLt_nat x y : (TCLt (x ?= y) <-> x < y)%nat.
Proof. by rewrite TCLt_iff Nat.compare_lt_iff. Qed.

(** Let TC resolution discharge side-conditions [n <> 0] (sometimes). *)
Class NNonZero (n : N) : Prop := N_non_zero : (n ≠ 0)%N.
#[global] Hint Mode NNonZero ! : typeclass_instances.
#[global] Instance N_non_empty p : NNonZero (Npos p).
Proof. done. Qed.

(** Useful when rewriting. *)
Lemma refl_True `(R : relation A) `{!Reflexive R} a : R a a ↔ True.
Proof. done. Qed.

(** Witnessing non-disjointness *)
(** We prove a few lemmas witnessing non-disjointness. Examples
include [list_not_disjoint] in [./list.v] and [set_not_disjoint] in
[./fin_sets.v]. Such lemmas convert non-disjointness into constructive
evidence; for example, turning `¬ X ## Y` when `X, Y : list A` into an
`x : A` s.t. `x ∈ X`, `y ∈ Y`.

Such witnesses can be useful to prove disjointness properties from
ownership. Suppose, for example, that you have a representation
predicate [myList (l : list A) : Rep] for some [A : Type] defined so
that [myList l ** myList k] implies [l ## k]. One way to prove an
observation like [Observe2 [| l ## k |] (myList l) (mList k)] is to

- decide if [l ## k] (possible because lists have finite inhabitants)
  and,

- when they are not disjoint, convert [¬ l ## k] into a witness [x :
  A] such that [x ∈ l], [y ∈ k], and

- use that witness to derive a contradiction from the ownership in
  [myList l ** myList k]. *)
