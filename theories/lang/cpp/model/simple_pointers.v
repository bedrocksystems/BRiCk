(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
A simple consistency proof for [PTRS]; this one is inspired by Cerberus's
model of pointer provenance, and resembles CompCert's model.

Unlike [PTRS_IMPL], this model cannot be extended to support
[VALID_PTR_AXIOMS] because it collapses the structure of pointers.
*)

From stdpp Require Import gmap.
From bedrock.prelude Require Import base addr avl bytestring option numbers.

From bedrock.lang.cpp Require Import ast.
From bedrock.lang.cpp.semantics Require Import sub_module values.
From bedrock.lang.cpp.model Require Import simple_pointers_utils.

Implicit Types (σ : genv).
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

Module SIMPLE_PTRS_IMPL <: PTRS_INTF.

  (**
  In this model, a pointer is either [invalid_ptr] (aka [None]) or a pair of
  a provenance and an address.

  We use [Z] for addresses to allow temporary underflows, but understand
  negative addresses as _invalid_. In this model (but not in general), all valid pointers have an address.
  *)
  Definition ptr' : Set := alloc_id * Z.
  Definition ptr : Set := option ptr'.

  Definition null_alloc_id : alloc_id := null_alloc_id.

  Definition invalid_ptr : ptr := None.
  Definition mkptr a n : ptr := Some (a, n).
  Definition nullptr : ptr := mkptr null_alloc_id 0.

  Definition ptr_alloc_id : ptr -> option alloc_id := fmap fst.
  Definition ptr_vaddr : ptr -> option vaddr := λ p,
    '(_, va) ← p;
    guard 0 ≤ va;
    Some (Z.to_N va).

  Lemma ptr_alloc_id_nullptr : ptr_alloc_id nullptr = Some null_alloc_id.
  Proof. done. Qed.

  Definition offset := option Z.
  Instance offset_eq_dec : EqDecision offset := _.
  Instance offset_countable : Countable offset := _.

  Declare Scope ptr_scope.
  Bind Scope ptr_scope with ptr.
  Delimit Scope ptr_scope with ptr.

  Declare Scope offset_scope.
  Bind Scope offset_scope with offset.
  Delimit Scope offset_scope with offset.

  Instance ptr_eq_dec : EqDecision ptr := _.
  Instance ptr_countable : Countable ptr := _.
  Definition ptr_eq_dec' := ptr_eq_dec.

  Lemma ptr_vaddr_nullptr : ptr_vaddr nullptr = Some 0%N.
  Proof. done. Qed.

  Definition o_id : offset := Some 0.
  Definition o_dot : offset → offset → offset := liftM2 Z.add.
  Notation "o1 .., o2" := (o_dot o1 o2) : offset_scope.

  Instance dot_id : RightId (=) o_id o_dot.
  Proof. case => [o|//] /=. by rewrite right_id_L. Qed.
  Instance id_dot : LeftId (=) o_id o_dot.
  Proof. case => [o|//] /=. by rewrite left_id_L. Qed.
  Instance dot_assoc : Assoc (=) o_dot.
  Proof. case => [x|//] [y|//] [z|//] /=. by rewrite assoc. Qed.

  (**
  [_offset_ptr] is basically [Z.add] lifted over a couple of functors.
  However, we perform the lifting in 2 stages. *)
  (*
   *** The first layer takes offsets in [Z] instead of [offset := option Z].
   This layer, with its associated lemmas, is useful after case analysis on [offset].
   *)
  Definition offset_ptr_raw : Z -> ptr -> ptr :=
    λ z p, p ≫= (λ '(aid, pa), Some (aid, z + pa)).

  (* Raw versions of [offset_ptr_id], [offset_ptr_dot]. *)
  Lemma offset_ptr_raw_id p : offset_ptr_raw 0 p = p.
  Proof. by case: p => [[a p]|]. Qed.

  Lemma offset_ptr_raw_dot {p o o'} :
    offset_ptr_raw o' (offset_ptr_raw o p) = offset_ptr_raw (o + o') p.
  Proof. case: p => [[a v]|//] /=. by rewrite assoc_L (comm_L _ o o'). Qed.

  (** Conveniences over [offset_ptr_raw_dot]. *)
  Lemma offset_ptr_raw_cancel {p} {o1 o2 : Z} o3
    (Hsum : o1 + o2 = o3) :
    offset_ptr_raw o2 (offset_ptr_raw o1 p) = (offset_ptr_raw o3 p).
  Proof. by rewrite offset_ptr_raw_dot Hsum. Qed.

  Lemma offset_ptr_raw_cancel0 (o1 o2 : Z) p
    (Hsum : o1 + o2 = 0) :
    offset_ptr_raw o2 (offset_ptr_raw o1 p) = p.
  Proof. by rewrite (offset_ptr_raw_cancel 0 Hsum) offset_ptr_raw_id. Qed.

  (* *** The second layer encapsulates case analysis on [ptr]. *)
  Definition _offset_ptr : ptr -> offset -> ptr :=
    λ p oz, z ← oz; offset_ptr_raw z p.
  Notation "p .., o" := (_offset_ptr p o) : ptr_scope.
  #[local] Open Scope ptr_scope.

  Lemma offset_ptr_id p : p .., o_id = p.
  Proof. apply offset_ptr_raw_id. Qed.

  Lemma offset_ptr_dot p o1 o2 :
    p .., (o1 .., o2) = p .., o1 .., o2.
  Proof. destruct o1, o2 => //=. apply symmetry, offset_ptr_raw_dot. Qed.

  Lemma ptr_alloc_id_offset {p o} :
    let p' := p .., o in
    is_Some (ptr_alloc_id p') ->
    ptr_alloc_id p' = ptr_alloc_id p.
  Proof. move=> /= -[aid]. by case: o p => [?|] [[??]|] /=. Qed.

  Definition o_field σ f : offset := o_field_off σ f.
  Definition o_sub σ ty z : offset := o_sub_off σ ty z.
  Definition o_base σ derived base := o_base_off σ derived base.
  Definition o_derived σ base derived := o_derived_off σ base derived.

  Lemma o_base_derived_raw σ p derived base :
    (p .., o_base σ derived base)%ptr <> invalid_ptr ->
    (p .., o_base σ derived base .., o_derived σ base derived = p)%ptr.
  Proof.
    rewrite /o_base /o_base_off /o_derived /o_derived_off.
    case: parent_offset => [o|//] /= Hval. apply offset_ptr_raw_cancel0. lia.
  Qed.

  Lemma o_derived_base_raw σ p derived base :
    (p .., o_derived σ base derived)%ptr <> invalid_ptr ->
    (p .., o_derived σ base derived .., o_base σ derived base = p)%ptr.
  Proof.
    rewrite /o_base /o_base_off /o_derived /o_derived_off.
    case: parent_offset => [o|//] /= Hval. apply: offset_ptr_raw_cancel0. lia.
  Qed.

  Lemma o_sub_sub_raw σ p ty n1 n2 :
    (p .., o_sub σ ty n1 .., o_sub σ ty n2 = p .., o_sub σ ty (n1 + n2))%ptr.
  Proof.
    rewrite /o_sub /o_sub_off. case: size_of => [o|//] /=.
    apply: offset_ptr_raw_cancel. lia.
  Qed.

  Lemma o_sub_0 σ ty :
    is_Some (size_of σ ty) ->
    o_sub σ ty 0 = o_id.
  Proof. rewrite /o_sub /o_sub_off => -[? ->] //=. Qed.

  Lemma o_dot_sub {σ : genv} i j ty :
    o_dot (o_sub _ ty i) (o_sub _ ty j) = o_sub _ ty (i + j).
  Proof.
    rewrite /o_sub /o_sub_off; case: size_of => //= sz. f_equiv. lia.
  Qed.

  (* Caveat: This model of [global_ptr] isn't correct, beyond proving
  [global_ptr]'s isn't contradictory.
  This model would fail proving that [global_ptr] is injective, that objects
  are disjoint, or that
  [global_ptr tu1 "staticR" |-> anyR T 1%Qp  ... ∗
   global_ptr tu2 "staticR" |-> anyR T 1%Qp  ...] actually holds at startup.
  *)
  Definition global_ptr (tu : translation_unit) (o : obj_name) : ptr :=
    Some (global_ptr_encode_aid o, Z.of_N $ global_ptr_encode_vaddr o).

  Definition fun_ptr := global_ptr.

  Lemma global_ptr_nonnull tu o : global_ptr tu o <> nullptr.
  Proof. done. Qed.

  Lemma ptr_vaddr_global_ptr tu o :
    ptr_vaddr (global_ptr tu o) = Some (global_ptr_encode_vaddr o).
  Proof. done. Qed.
  Lemma ptr_alloc_id_global_ptr tu o :
    ptr_alloc_id (global_ptr tu o) = Some (global_ptr_encode_aid o).
  Proof. done. Qed.

  Lemma global_ptr_nonnull_addr tu o : ptr_vaddr (global_ptr tu o) <> Some 0%N.
  Proof. rewrite ptr_vaddr_global_ptr. done. Qed.
  Lemma global_ptr_nonnull_aid tu o : ptr_alloc_id (global_ptr tu o) <> Some null_alloc_id.
  Proof. rewrite ptr_alloc_id_global_ptr. done. Qed.

  Instance global_ptr_inj tu : Inj (=) (=) (global_ptr tu).
  Proof. by intros o1 o2 [?%(inj global_ptr_encode_aid) _]%(inj Some)%(inj2 _). Qed.

  Instance global_ptr_addr_inj tu : Inj (=) (=) (λ o, ptr_vaddr (global_ptr tu o)).
  Proof. intros ??. rewrite !ptr_vaddr_global_ptr. by intros ?%(inj _)%(inj _). Qed.
  Instance global_ptr_aid_inj tu : Inj (=) (=) (λ o, ptr_alloc_id (global_ptr tu o)).
  Proof. intros ??. rewrite !ptr_alloc_id_global_ptr. by intros ?%(inj _)%(inj _). Qed.

  Lemma ptr_vaddr_o_sub_eq p σ ty n1 n2 sz
    (Hsz : size_of σ ty = Some sz) (Hsz0 : (sz > 0)%N) :
    (same_property ptr_vaddr (p .., o_sub σ ty n1) (p .., o_sub σ ty n2) ->
    n1 = n2)%ptr.
  Proof.
    rewrite same_property_iff /ptr_vaddr /o_sub /o_sub_off Hsz => -[addr []] /=.
    case: p => [[aid va]|] Haddr ?; simplify_option_eq. nia.
  Qed.

  Instance o_sub_mono :
    Proper (genv_leq ==> eq ==> eq ==> Roption_leq eq) (@o_sub).
  Proof.
    move => σ1 σ2 /Proper_size_of + _ ty -> _ n -> => /(_ ty ty eq_refl).
    rewrite /o_sub /o_sub_off.
    move: (size_of σ1) (size_of σ2) => [sz1|] [sz2|] LE //=; inversion LE; constructor.
    naive_solver .
  Qed.

  (* Not exposed directly, but proof sketch for
  [valid_o_sub_size]; recall that in this model, all valid pointers have an
  address. *)
  Lemma raw_valid_o_sub_size σ p ty i :
    is_Some (ptr_vaddr (p .., o_sub σ ty i)) ->
    is_Some (size_of σ ty).
  Proof. rewrite /o_sub /o_sub_off. case: size_of=> //. by eexists. Qed.

  Definition eval_offset (_ : genv) (o : offset) : option Z := o.
  Lemma eval_o_sub σ ty (i : Z) :
    eval_offset _ (o_sub _ ty i) =
      (* This order enables reducing for known ty. *)
      (fun n => Z.of_N n * i) <$> size_of _ ty.
  Proof.
    rewrite /o_sub/o_sub_off. case: size_of => //= sz.
    by rewrite (comm _ i).
  Qed.

  Lemma eval_o_field σ f n cls st :
    f = {| f_name := n ; f_type := cls |} ->
    glob_def σ cls = Some (Gstruct st) ->
    st.(s_layout) = POD \/ st.(s_layout) = Standard ->
    eval_offset σ (o_field σ f) = offset_of σ (f_type f) (f_name f).
  Proof. done. Qed.

  Lemma offset_ptr_vaddr_raw resolve o n va va' p :
    eval_offset resolve o = Some n ->
    ptr_vaddr p = Some va ->
    ptr_vaddr (p .., o) = Some va' ->
    Z.to_N (Z.of_N va + n) = va'.
  Proof.
    rewrite /eval_offset /ptr_vaddr.
    case: p => [[aid ?]|] /=;
      intros; simplify_option_eq. lia.
  Qed.

  Lemma offset_ptr_vaddr resolve o n va p :
    eval_offset resolve o = Some n ->
    ptr_vaddr p = Some va ->
    ptr_vaddr (p .., o) = Some (Z.to_N (Z.of_N va + n)).
  Proof.
    case E: (ptr_vaddr (p .., o)) => [va'|] Hoff Hp.
    { by erewrite offset_ptr_vaddr_raw. }
    move: E Hp Hoff.
    rewrite /eval_offset /ptr_vaddr.
    case: p => [[aid ?]|] //=;
      intros; simplify_option_eq => //.
    (* False. *)
    (* have: 0 <= n by admit. *)
    (* lia. *)
  Abort.

  Include PTRS_DERIVED_MIXIN.
  Include PTRS_MIXIN.
End SIMPLE_PTRS_IMPL.
