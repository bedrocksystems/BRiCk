(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.logic.heap_pred.prelude.
Require Import bedrock.lang.cpp.logic.heap_pred.valid.
Require Import bedrock.lang.cpp.logic.heap_pred.null.
Require Import bedrock.lang.cpp.logic.heap_pred.simple.
Require Import bedrock.lang.cpp.logic.heap_pred.any.

Import rep_defs.INTERNAL. (* for access to [unfold_at] *)


#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** [blockR sz q] represents [q] ownership of a contiguous chunk of
      [sz] bytes without any C++ structure on top of it. *)
  Definition blockR_def {σ} sz (q : cQp.t) : Rep :=
    _offsetR (o_sub σ Tu8 (Z.of_N sz)) validR **
    (* ^ Encodes valid_ptr (this .[ Tu8 ! sz]). This is
    necessary to get [l |-> blockR n -|- l |-> blockR n ** l .[ Tu8 ! m] |-> blockR 0]. *)
    [∗list] i ∈ seq 0 (N.to_nat sz),
      _offsetR (o_sub σ Tu8 (Z.of_nat i)) (anyR Tu8 q).
  Definition blockR_aux : seal (@blockR_def). Proof. by eexists. Qed.
  Definition blockR := blockR_aux.(unseal).
  Definition blockR_eq : @blockR = _ := blockR_aux.(seal_eq).
  #[global] Arguments blockR {_} _%_N _%_Qp.

  #[global] Instance blockR_timeless sz q :
    Timeless (blockR sz q).
  Proof. rewrite blockR_eq /blockR_def. unfold_at. apply _. Qed.
  #[global] Instance blockR_cfractional sz :
    CFractional (blockR sz).
  Proof. rewrite blockR_eq. apply _. Qed.
  #[global] Instance blockR_as_cfractional sz :
    AsCFractional0 (blockR sz).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance blockR_observe_frac_valid sz :
    TCLt (0 ?= sz)%N ->
    CFracValid0 (blockR sz).
  Proof.
    rewrite TCLt_N blockR_eq/blockR_def. intros.
    destruct (N.to_nat sz) eqn:?; [ lia | ] => /=.
    try solve_cfrac_valid.
  Qed.

  Lemma nullptr_blockR sz q :
    nullptr |-> blockR sz q |-- [| sz = 0%N |].
  Proof.
    rewrite blockR_eq/blockR_def _at_sep.
    destruct sz; eauto.
    have->: (N.to_nat (N.pos p) = S (N.to_nat (N.pos p - 1))) by lia.
    rewrite -cons_seq /= o_sub_0 => //.
    rewrite !_at_offsetR _offsetR_id _at_sep.
    iIntros "(?&B&C)".
    iDestruct (observe (nullptr |-> nonnullR) with "B") as "X".
    rewrite _at_nonnullR.
    by iDestruct "X" as %[].
  Qed.

  Lemma blockR_disjoint (l : ptr):
    l |-> blockR 1 (cQp.m 1) |-- l |-> blockR 1 (cQp.m 1) -* False.
  Proof.
    iIntros "K L". iCombine "K L" as "P".
    by iDestruct (observe [| _ ≤ 1 |]%Qp with "P") as %?.
  Qed.

  (* [tblockR ty] is a [blockR] that is the size of [ty] and properly aligned.
   * it is a convenient short-hand since it happens frequently, but there is nothing
   * special about it.
   *)
  Definition tblockR (ty : type) (q : cQp.t) : Rep :=
    match size_of σ ty , align_of ty with
    | Some sz , Some al => blockR (σ:=σ) sz q ** alignedR al
    | _ , _  => False
    end.

  #[global] Instance tblockR_timeless ty q :
    Timeless (tblockR ty q).
  Proof. rewrite/tblockR. case_match; apply _. Qed.
  #[global] Instance tblockR_cfractional ty :
    CFractional (tblockR ty).
  Proof.
    rewrite/tblockR. do 2!(case_match; last by apply _).
    apply _.
  Qed.
  #[global] Instance tblockR_as_cfractional ty : AsCFractional0 (tblockR ty).
  Proof. solve_as_cfrac. Qed.
  #[global] Instance tblockR_observe_frac_valid ty n :
    SizeOf ty n -> TCLt (0 ?= n)%N ->
    CFracValid0 (tblockR ty).
  Proof.
    rewrite/tblockR=>-> ?. case_match; solve_cfrac_valid.
  Qed.

  #[global] Instance blockR_nonnull n q :
    TCLt (0 ?= n)%N -> Observe nonnullR (blockR n q).
  Proof.
    rewrite TCLt_N blockR_eq/blockR_def.
    destruct (N.to_nat n) eqn:Hn; [ lia | ] => {Hn} /=.
    rewrite o_sub_0 ?_offsetR_id; [ | by eauto].
    assert (TCEq (zero_sized_array Tu8) false) by done.
    apply _.
  Qed.
  #[global] Instance blockR_valid_ptr sz q : Observe validR (blockR sz q).
  Proof.
    rewrite blockR_eq/blockR_def.
    destruct sz.
    { iIntros "[#A _]".
      rewrite o_sub_0; last by econstructor.
      rewrite _offsetR_id. eauto. }
    { iIntros "[_ X]".
      unfold N.to_nat. destruct (Pos.to_nat p) eqn:?; first lia.
      simpl. iDestruct "X" as "[X _]".
      rewrite o_sub_0; last by econstructor. rewrite _offsetR_id.
      iApply (observe with "X"). }
  Qed.

  #[global] Instance tblockR_nonnull n ty q :
    SizeOf ty n -> TCLt (0 ?= n)%N ->
    Observe nonnullR (tblockR ty q).
  Proof.
    intros Heq ?. rewrite/tblockR {}Heq.
    case_match; by apply _.
  Qed.

  #[global] Instance tblockR_valid_ptr ty q : Observe validR (tblockR ty q).
  Proof.
    rewrite /tblockR. case_match; refine _.
    case_match; refine _.
  Qed.
End with_cpp.
