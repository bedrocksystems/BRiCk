(*
 * Copyright (c) 2020-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import locker.

(* points-to *)
Structure AT : Type :=
  { #[canonical=yes] AT_LHS : Type
  ; #[canonical=no] AT_RHS : Type
  ; #[canonical=yes] AT_Result : Type
  ; #[canonical=no] AT_at : AT_LHS -> AT_RHS -> AT_Result }.
#[global] Arguments AT_at {AT} _ _ : rename, simpl never.
#[global] Bind Scope bi_scope with AT_RHS.

mlock Definition __at := @AT_at.
#[global] Arguments __at {AT} _ _ : rename.

#[global] Notation "p |-> r" := (__at p r)
  (at level 15, r at level 20, right associativity) : stdpp_scope.

From bedrock.lang.cpp.semantics Require Import values.
From bedrock.lang.cpp.logic Require Import mpred rep_defs.

Canonical Structure AT_ptr `{Σ : cpp_logic} : AT :=
  {| AT_LHS := ptr; AT_RHS := Rep; AT_Result := mpred; AT_at := _at |}.
Canonical Structure AT_offset `{Σ : cpp_logic} : AT :=
  {| AT_LHS := offset; AT_RHS := Rep; AT_Result := Rep; AT_at := _offsetR |}.

#[global] Notation _at := (@__at AT_ptr) (only parsing).
#[global] Notation _offsetR := (@__at AT_offset) (only parsing).

Module INTERNAL.
  Ltac unfold_at := rewrite __at.unlock /AT_at/=; try rewrite rep_defs._at_eq; try rewrite rep_defs._offsetR_eq.
  Lemma _at_eq `{Σ : cpp_logic} p R : p |-> R = rep_defs._at_def p R.
  Proof. by unfold_at. Qed.
  Lemma _offsetR_eq `{Σ : cpp_logic} o R : o |-> R = rep_defs._offsetR_def o R.
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
