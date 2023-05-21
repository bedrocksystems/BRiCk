(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Most clients should import [bedrock.lang.cpp.logic.rep] instead of this file.
This file defines the core type [Rep] of representation predicates.
TODO: merge back into [rep.v]?
*)
From elpi Require Import locker.
From bedrock.lang.bi Require Import prelude monpred.
From bedrock.lang.cpp Require Import semantics.values logic.mpred.

Import ChargeNotation.
Implicit Types (σ resolve : genv) (p : ptr) (o : offset).

(** Representation predicates are implicitly indexed by a location, and should be used to
  * assert properties of the heap
  *)
Canonical Structure ptr_bi_index : biIndex :=
  BiIndex ptr _ eq _.

#[global] Instance ptr_bi_index_discrete : BiIndexDiscrete ptr_bi_index.
Proof. by move=>i i'. Qed.

(** The tactic [intros ->%ptr_rel_elim] is much faster than [intros
    ->] when introducing [p1 ⊑ p2] (when the latter works at all). *)
Lemma ptr_rel_elim (p1 p2 : ptr) : p1 ⊑ p2 → p1 = p2.
Proof. done. Qed.

Canonical Structure RepI `{Σ : cpp_logic} := monPredI ptr_bi_index mpredI.
Definition Rep `{Σ : cpp_logic} : Type := RepI.
Definition RepO `{Σ : cpp_logic} : ofe := RepI.

#[global] Bind Scope bi_scope with Rep.

Section defs.
  Context `{Σ : cpp_logic}.

  Definition as_Rep (P : ptr -> mpred) : Rep := MonPred P _.

  (** Values
   * These `Rep` predicates wrap `ptsto` facts
   *)
  (* todo(gmm): make opaque *)
  Definition pureR (P : mpred) : Rep :=
    as_Rep (fun _ => P).
End defs.
#[global] Instance: Params (@as_Rep) 2 := {}.
#[global] Instance: Params (@pureR) 2 := {}.

mlock Definition at_aux `{Σ : cpp_logic} (p : ptr) (R : Rep) : mpred :=
  R.(monPred_at) p.
#[global] Arguments at_aux {_ _} _ _ : assert.

mlock Definition offsetR_aux `{Σ : cpp_logic} (o : offset) (R : Rep) : Rep :=
  as_Rep (fun base => R.(monPred_at) (base ,, o)).
#[global] Arguments offsetR_aux {_ _} _ _ : assert.

(* TODO replace by the right instances. *)
#[global] Instance: Params (@at_aux) 3 := {}.
#[global] Instance: Params (@offsetR_aux) 3 := {}.

(* points-to *)
#[projections(primitive=yes)]
Structure AT `{Σ : cpp_logic} : Type :=
  { #[canonical=yes] AT_LHS :> Type
  ; #[canonical=yes] AT_Result : Type
  ; #[canonical=no] AT_at : AT_LHS -> Rep -> AT_Result }.
#[global] Arguments AT_at {AT} _ _ : rename, simpl never.

mlock Definition __at := @AT_at.
#[global] Arguments __at {ti Σ AT} _ _ : rename.

Canonical Structure ptrA `{Σ : cpp_logic} : AT :=
  {| AT_LHS := ptr; AT_Result := mpred; AT_at := at_aux |}.
Canonical Structure offsetA `{Σ : cpp_logic} : AT :=
  {| AT_LHS := offset; AT_Result := Rep; AT_at := offsetR_aux |}.

(** [_at base R] states that [R base] holds.

    NOTE This is "weakly at"
  *)
#[global] Notation _at := (__at (AT := ptrA)).
#[global] Notation _offsetR := (__at (AT := offsetA)).

(* Added later to have higher priority. *)
#[global] Notation "p |-> r" := (__at p r)
  (at level 15, r at level 20, right associativity) : stdpp_scope.

Module INTERNAL.
  Ltac unfold_at := rewrite __at.unlock /AT_at/= 1?at_aux.unlock 1?offsetR_aux.unlock.
  Lemma _at_eq `{Σ : cpp_logic} p R : p |-> R = R.(monPred_at) p.
  Proof. by unfold_at. Qed.
  Lemma _offsetR_eq `{Σ : cpp_logic} o R : o |-> R =
    as_Rep (fun p => R.(monPred_at) (p ,, o)).
  Proof. by unfold_at. Qed.
End INTERNAL.

(* Test suite *)
Module Type TEST_SUITE.
Section test_suite.
  Context {σ : genv} `{Σ : cpp_logic} (R : Rep) (f g : field) (o : offset) (p : ptr) (v : val).

  #[local] Ltac syntactically_equal :=
    lazymatch goal with
    | _ : _ |- ?X = ?X => idtac
    end;
    reflexivity.

  Goal o ., f = o ,, _field f.
  Proof. syntactically_equal. Qed.

  Goal p |-> R = _at p R.
  Proof. syntactically_equal. Qed.

  Goal o |-> R = _offsetR o R.
  Proof. syntactically_equal. Qed.

  (*Example _0 := |> p |-> R.

  Example _1 := |> p ., f |-> R.

  Example _1' := |> _eqv v ., f |-> R.*)

  Example _2 := p |-> _field f |-> R.

  Example _3 := p .[ Tint ! 0 ] |-> R.

  Example _4 := p |-> _field f .[ Tint ! 0 ] |-> R.

  Example _4a := p ., f |-> R.

  Example _4b : p ., f .[ Tint ! 0] = (p ., f) .[ Tint ! 0].
  Proof. syntactically_equal. Qed.

  Example _5 := p .[ Tint ! 0 ] .[ Tint ! 3 ] |-> R.

  Example _6 := p ., f .[ Tint ! 0 ] ., g |-> R.

  Example _7 := p ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> _field f |-> R.

  Example _8 := p ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> .[ Tint ! 1 ] |-> R.

  Example _9 := o ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> R.

  Example _10 := o ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> R.

  Example _11 := o .[ Tint ! 1 ] |-> R.

  Example _12 := o .[ Tint ! 1 ] |-> R.

  (*Example _13 := _eqv v .[ Tint ! 1 ] |-> R.

  Example _13' := _eqv v |-> R.*)

  Example _14 := .[ Tint ! 1 ] |-> R.

  (*Example _15 := |> .[ Tint ! 1 ] |-> |> R.*)

  Example _16 := p .[ Tint ! 1] |-> _offsetR (_field f) R.

  (*backwards compatibility*)
  Example b0 := _at p R.

  Example b1 := _offsetR (_field f) R.

  Example b2 := _at (p .[ Tint ! 1]) R.

  Example b3 := _at (p .[ Tint ! 1]) (_offsetR (_field f) R).

  (*failure cases*)
  (*Fail Example fail0 := p |-> ▷ R ∗ R.
  (*Fail Example fail1 := p |-> |> R ** R. (* requires parsing as [(p |-> |> R) ** R] *)*)

  Fail Example fail2 := p |-> R ** R.*) (* requires parsing as [(p |-> R) ** R] *)

  Fail Example fail3 := p |-> R q.
End test_suite.
End TEST_SUITE.
