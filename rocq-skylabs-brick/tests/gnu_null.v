(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.logic.
Require Import skylabs.lang.cpp.parser.expr.
Require Import skylabs.lang.cpp.notations.
Import ParserExpr.

(** * GNU <<__null>>

    cpp2v emits GNU C++'s <<NULL>> as [Egnu_null "long"] (on LP64), wrapped in
    [Cnull2ptr] wherever clang expects a pointer. *)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit) (ρ : region).

  (** <<long f() { return NULL; }>>, <<NULL + 1>> *)
  Lemma gnu_null_int Q :
    Q (Vint 0) FreeTemps.id |-- wp_operand tu ρ (Egnu_null "long") Q.
  Proof.
    iIntros "Q". iApply wp_operand_int. iSplit; last done.
    iPureIntro. apply has_int_type. red; simpl; lia.
  Qed.

  (** <<int* p = NULL;>>, <<return NULL;>>, <<p == NULL>>, <<p = NULL>>,
      <<(void* )NULL>> *)
  Lemma gnu_null_ptr ty Q :
    is_pointer ty ->
    Q (Vptr nullptr) FreeTemps.id
    |-- wp_operand tu ρ (Ecast (Cnull2ptr ty) (Egnu_null "long")) Q.
  Proof.
    iIntros (?) "Q". iApply wp_operand_cast_null_int; [done..|].
    rewrite /wp_discard /=. by iApply gnu_null_int.
  Qed.
End with_cpp.
