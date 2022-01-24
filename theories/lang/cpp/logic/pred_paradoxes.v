(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(* Demonstrate paradoxes from alluring but incorrect axioms. *)
Require Import iris.proofmode.proofmode.
Require Import bedrock.prelude.base.

From bedrock.lang.cpp Require Import semantics logic.pred ast.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
  (*
  In contrast to [strict_valid_ptr_field_sub], in [p .., o_sub σ ty i] the subscript might cancel out after
  normalization. Hence we can give a counterexample to [strict_valid_ptr_sub_bad]:

  [[
  Axiom valid_ptr_sub_bad : ∀ p ty (i : Z),
    (0 <= i)%Z ->
    valid_ptr (p .., o_sub σ ty i) |-- valid_ptr p.
  ]]
  Take [p = p_base .., o_sub σ ty -i], assuming [valid_ptr p_base] but not [valid_ptr p]:
  that gives [valid_ptr (p .., o_sub σ ty i)] hence [valid_ptr p].

  Choosing [p_base = nullptr] gives [False], but we get incorrect results even
  if [p_base] points to the beginning of an array.
  *)
  Let bad_valid_ptr_sub : mpred :=
    (∀ p (i : Z) ty, [| 0 <= i |]%Z -∗ valid_ptr (p .., o_sub σ ty i) -∗ valid_ptr p).

  Lemma not_strict_valid_ptr_sub_bad p_base i {ty} (Hsz : is_Some (size_of σ ty)) (_ : (0 ≤ i)%Z) :
    let p := (p_base .., o_sub σ ty (-i))%ptr in
    bad_valid_ptr_sub ⊢ valid_ptr p_base -∗ (valid_ptr p -∗ False) -∗ False.
  Proof.
    iIntros "H #V NV". iApply "NV".
    iApply ("H" $! (p_base .., o_sub σ ty (-i))%ptr i ty with "[//]").
    by rewrite o_sub_sub Z.add_opp_diag_l o_sub_0 ?offset_ptr_id.
  Qed.

  Lemma not_strict_valid_ptr_sub_bad' ty (Hsz : is_Some (size_of σ ty)) :
    bad_valid_ptr_sub ⊢ False.
  Proof.
    iIntros "H".
    iApply (not_strict_valid_ptr_sub_bad nullptr 1 Hsz with "H"); first done.
    by iApply valid_ptr_nullptr.
    by iApply _valid_ptr_nullptr_sub_false.
  Qed.

End with_cpp.
