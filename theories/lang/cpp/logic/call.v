(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp destroy.
Require Import bedrock.lang.cpp.heap_notations.

Section with_resolve.
  Context `{Σ : cpp_logic} {σ : genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Local Notation wp_lval := (wp_lval M ti ρ).
  Local Notation wp_prval := (wp_prval M ti ρ).
  Local Notation wp_xval := (wp_xval M ti ρ).
  Local Notation wp_init := (wp_init M ti ρ).

  Fixpoint wp_args (es : list (ValCat * Expr)) (Q : list val -> FreeTemps -> mpred)
  : mpred :=
    match es with
    | nil => Q nil emp%I
    | (vc,e) :: es =>
      let ty := erase_qualifiers $ type_of e in
      match vc with
      | Lvalue =>
        Exists Qarg,
        wp_lval e Qarg **
          wp_args es (fun vs frees => Forall v free,
                                   Qarg v free -* Q (Vptr v :: vs) (free ** frees))
      | Prvalue =>
        if is_aggregate ty then
          Forall a : ptr, a |-> tblockR (σ:=σ) ty 1 -*
          let (e,dt) := destructor_for e in
          Exists Qarg,
          wp_init ty a e Qarg **
            wp_args es (fun vs frees =>
                          Forall free,
                          Qarg free -* Q (Vptr a :: vs) (destruct_val (σ:=σ) ti false ty a (a |-> tblockR (σ:=σ) ty 1 ** free) ** frees))
        else
          Exists Qarg,
          wp_prval e Qarg **
            wp_args es (fun vs frees => Forall v free,
                                     Qarg v free -* Q (v :: vs) (free ** frees))
      | Xvalue =>
        Exists Qarg,
        wp_xval e Qarg **
            wp_args es (fun vs frees => Forall v free,
                                     Qarg v free -* Q (Vptr v :: vs) (free ** frees))
      end
    end.

  Lemma wp_args_frame_strong : forall es Q Q',
      (Forall vs free, [| length vs = length es |] -* Q vs free -* Q' vs free) |-- wp_args es Q -* wp_args es Q'.
  Proof.
    elim => /=.
    { by iIntros (? ?) "H"; iApply "H". }
    { iIntros ([vc e] ? IH ? ?) "H".
      destruct vc.
      { iIntros "X"; iDestruct "X" as (Qarg) "[He Hes]".
        iExists Qarg; iFrame.
        iRevert "Hes"; iApply IH; iIntros (? ?) "% X".
        iIntros (? ?) "Y"; iApply "H" => /=; eauto. iApply "X"; iFrame. }
      { case_match.
        { iIntros "X" (a) "B"; iDestruct ("X" with "B") as "X".
          destruct (destructor_for e).
          iRevert "X".
          iIntros "X"; iDestruct "X" as (Qarg) "[He Hes]".
          iExists Qarg; iFrame; iRevert "Hes"; iApply IH.
          iIntros (? ?) "% Y"; iIntros (?) "Q"; iApply "H" => /=; eauto; iApply "Y"; iFrame. }
        { iIntros "X"; iDestruct "X" as (Qarg) "[He Hes]".
          iExists Qarg; iFrame.
          iRevert "Hes"; iApply IH; iIntros (? ?) "% X".
          iIntros (? ?) "Y"; iApply "H" => /=; eauto; iApply "X"; iFrame. } }
      { iIntros "X"; iDestruct "X" as (Qarg) "[He Hes]".
        iExists Qarg; iFrame.
        iRevert "Hes"; iApply IH; iIntros (? ?) "% X".
        iIntros (? ?) "Y"; iApply "H" => /=; eauto; iApply "X"; iFrame. } }
  Qed.

  Lemma wp_args_frame : forall es Q Q',
      (Forall vs free, Q vs free -* Q' vs free) |-- wp_args es Q -* wp_args es Q'.
  Proof.
    intros; iIntros "X".
    iApply wp_args_frame_strong.
      by iIntros (vs free) "% H"; iApply "X".
  Qed.

End with_resolve.
