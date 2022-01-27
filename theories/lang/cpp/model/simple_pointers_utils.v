(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Support code for [simple_pointers.v]. *)

From stdpp Require Import gmap.
From bedrock.prelude Require Import base addr option avl.
From bedrock.lang.cpp.semantics Require Import values.

Implicit Types (σ : genv).
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

Module canonical_tu.
  Definition im_to_gmap {V} (m : IM.t V) : gmap BS.t V :=
    list_to_map (map_to_list m).
  Definition symbol_table_canon : Set := gmap BS.t ObjValue.
  Definition type_table_canon : Set := gmap BS.t GlobDecl.

  #[global] Instance symbol_table_canon_eq_dec : EqDecision symbol_table_canon.
  Proof. solve_decision. Qed.
  #[global] Instance type_table_canon_eq_dec : EqDecision type_table_canon.
  Proof. solve_decision. Qed.

  Record translation_unit_canon : Set := Build_translation_unit_canon
  { symbols    : symbol_table_canon
  ; globals    : type_table_canon
  ; byte_order : endian
  }.
  #[global] Instance translation_unit_canon_eq_dec : EqDecision translation_unit_canon.
  Proof. solve_decision. Qed.

  #[global] Instance symbol_canon_lookup : Lookup obj_name ObjValue translation_unit_canon :=
    fun k m => m.(symbols) !! k.

  Record genv_canon : Set := Build_genv_canon
  { genv_tu : translation_unit_canon
    (* ^ the [translation_unit] *)
  ; pointer_size_bitsize : bitsize
    (* ^ the size of a pointer *)
  }.
  #[global] Instance genv_canon_eq_dec : EqDecision genv_canon.
  Proof. solve_decision. Qed.

  Definition tu_to_canon (tu : translation_unit) : translation_unit_canon :=
    let (s, g, init, bo) := tu in Build_translation_unit_canon (im_to_gmap s) (im_to_gmap g) bo.
  #[local] Definition genv_to_canon σ : genv_canon :=
    let (tu, sz) := σ in Build_genv_canon (tu_to_canon tu) sz.
End canonical_tu.

Definition null_alloc_id : alloc_id := MkAllocId 0.
Definition invalid_alloc_id : alloc_id := MkAllocId 1.

(** Compute the actual raw offsets in Z. *)
Section eval_offset_seg.
  Context σ.
  Definition o_field_off (f : field) : option Z := offset_of σ f.(f_type) f.(f_name).
  Definition o_sub_off ty z : option Z := Z.mul z <$> (Z.of_N <$> size_of σ ty).
  Definition o_base_off derived base : option Z := parent_offset σ derived base.
  Definition o_derived_off base derived : option Z := Z.opp <$> parent_offset σ derived base.
End eval_offset_seg.

(*
Utility function, used to emulate [global_ptr] without a linker.
This is a really bad model and it'd fail a bunch of sanity checks.

Caveat: a model this to model [global_ptr] isn't correct, beyond proving
[global_ptr]'s isn't contradictory.
This model would fail proving that objects are disjoint or that
[global_ptr tu1 "staticR" |-> anyR T 1%Qp  ... ∗
  global_ptr tu2 "staticR" |-> anyR T 1%Qp  ...] actually holds at startup.
*)

Definition global_ptr_encode_vaddr (o : obj_name) : vaddr := Npos (encode o).
Definition global_ptr_encode_aid (o : obj_name) : alloc_id := MkAllocId (global_ptr_encode_vaddr o).

#[global] Instance global_ptr_encode_vaddr_inj : Inj (=) (=) global_ptr_encode_vaddr := _.
#[global] Instance global_ptr_encode_aid_inj : Inj (=) (=) global_ptr_encode_aid := _.

Lemma global_ptr_encode_vaddr_nonnull o va : va = global_ptr_encode_vaddr o -> va <> 0%N.
Proof. by move->. Qed.

Lemma global_ptr_encode_aid_nonnull o aid : aid = global_ptr_encode_aid o -> aid <> null_alloc_id.
Proof. by move->. Qed.

(*
A slightly better model might be something like the following, but we don't
bother defining this [Countable] instance. And this is not a great model
anyway. *)

(*
Declare Instance ObjValue_countable: Countable ObjValue.
Definition global_ptr (tu : translation_unit) (o : obj_name) : ptr :=
  let obj : option ObjValue := tu !! o in
  let p := Npos (encode obj) in (mkptr p p).
*)

Module Type PTRS_DERIVED_MIXIN (Import P : PTRS).
  Definition same_alloc : ptr -> ptr -> Prop := same_property ptr_alloc_id.
  Lemma same_alloc_eq : same_alloc = same_property ptr_alloc_id.
  Proof. done. Qed.

  Definition same_address : ptr -> ptr -> Prop := same_property ptr_vaddr.
  Lemma same_address_eq : same_address = same_property ptr_vaddr.
  Proof. done. Qed.

  Definition pinned_ptr_pure (va : vaddr) (p : ptr) := ptr_vaddr p = Some va.
  Lemma pinned_ptr_pure_eq :
    pinned_ptr_pure = fun (va : vaddr) (p : ptr) => ptr_vaddr p = Some va.
  Proof. done. Qed.
End PTRS_DERIVED_MIXIN.

(* Double-check [PTRS_DERIVED_MIXIN] matches its interface. *)
Module PTRS_DERIVED_TEST (P : PTRS) : PTRS_DERIVED P.
Include PTRS_DERIVED_MIXIN P.
End PTRS_DERIVED_TEST.
