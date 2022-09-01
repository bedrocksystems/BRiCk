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
  In contrast to [strict_valid_ptr_field_sub], in [p ,, o_sub σ ty i] the subscript might cancel out after
  normalization. Hence we can give a counterexample to [strict_valid_ptr_sub_bad]:

  [[
  Axiom valid_ptr_sub_bad : ∀ p ty (i : Z),
    (0 <= i)%Z ->
    valid_ptr (p ,, o_sub σ ty i) |-- valid_ptr p.
  ]]
  Take [p = p_base ,, o_sub σ ty -i], assuming [valid_ptr p_base] but not [valid_ptr p]:
  that gives [valid_ptr (p ,, o_sub σ ty i)] hence [valid_ptr p].

  Choosing [p_base = nullptr] gives [False], but we get incorrect results even
  if [p_base] points to the beginning of an array.
  *)
  Let bad_valid_ptr_sub : mpred :=
    (∀ p (i : Z) ty, [| 0 <= i |]%Z -∗ valid_ptr (p ,, o_sub σ ty i) -∗ valid_ptr p).

  Lemma not_strict_valid_ptr_sub_bad (p_base : ptr) i {ty} (Hsz : is_Some (size_of σ ty)) (_ : (0 ≤ i)%Z) :
    let p := p_base ,, o_sub σ ty (-i) in
    bad_valid_ptr_sub ⊢ valid_ptr p_base -∗ (valid_ptr p -∗ False) -∗ False.
  Proof.
    iIntros "H #V NV". iApply "NV".
    iApply ("H" $! (p_base ,, o_sub σ ty (-i)) i ty with "[//]").
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

  (* The following [Axiom] reflects a generalization of the [faithful] version
     in which arbitrary offsets can be erased down to (appropriately bounded)
     byte offsets. THIS IS UNSOUND.
   *)
  Section type_ptr_object_representation_full_is_unsound.
    Hypothesis type_ptr_obj_repr_full :
      forall (σ : genv) (ty : type) (p : ptr) (o : offset) (i sz : N) (off : Z),
        size_of σ ty = Some sz ->     (* 1) [ty] has some byte-size [sz] *)
        eval_offset σ o = Some off -> (* 2) [o] has some numerical byte-offset value [off] *)
        (off <= i < off + sz)%Z ->     (* 3) by (1) and (2), [sz] is nonzero and [i] is a
                                            byte-offset into the object rooted at [p ,, o]

                                            NOTE: [forall ty, size_of (Tarray ty 0) = Some 0],
                                            but zero-length arrays are not permitted by the
                                            Standard (cf. <https://eel.is/c++draft/dcl.array#def:array,bound>).
                                            NOTE: if support for flexible array members is
                                            ever added, it will need to be carefully
                                            coordinated with these sorts of transport lemmas.
                                      *)
        (* 4) The existence of the "object representation" of an object of type [ty] -
           |  in conjunction with the premises - justifies "lowering" any
           |  [type_ptr ty (p ,, o)] fact to a family of [type_ptr Tu8 (p ,, .[Tu8 ! i])]
           |  facts - where [i] is a byte-offset that "covers" the [sizeof(ty)].
           v *)
        type_ptr ty (p ,, o) |-- type_ptr Tu8 (p ,, .[ Tu8 ! i ]).
    Parameter (q : ptr).
    Let p := q .[ Tu16 ! -1000 ].
    Let o := .[ Tu16 ! 1000 ].

    Lemma type_ptr_obj_repr_full_bad :
      type_ptr Tu8 (p ,, o) |-- type_ptr Tu8 (p ,, .[ Tu8 ! 2000 ]).
    Proof using type_ptr_obj_repr_full.
      subst p o.
      iIntros "tptr".
      iDestruct (type_ptr_obj_repr_full _ _ _ _ 2000 with "tptr")
        as "tptr_byte"; rewrite ?eval_o_sub; simpl; eauto.
      simpl. lia.
    Qed.
  End type_ptr_object_representation_full_is_unsound.
End with_cpp.
