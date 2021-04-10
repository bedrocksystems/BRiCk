(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
Require Import iris.proofmode.tactics.
From iris.bi.lib Require Import fractional.

Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred translation_unit.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.logic.z_to_bytes.
Require Import bedrock.lang.cpp.logic.arr.
Require Export bedrock.lang.cpp.logic.raw.

Require Import bedrock.lang.cpp.heap_notations.

Section with_Σ.
  Context `{Σ : cpp_logic} {resolve:genv}.

  (** TODO move to pred.v *)
  Axiom struct_padding : genv -> Qp -> globname -> Rep.
  Axiom union_padding : genv -> Qp -> globname -> nat -> Rep.

  Axiom struct_padding_fractional : forall cls, Fractional (fun q => struct_padding resolve q cls).
  Axiom struct_padding_timeless : forall q cls, Timeless  (struct_padding resolve q cls).
  Axiom struct_padding_frac_valid : forall (q : Qp) cls, Observe [| q ≤ 1 |]%Qp (struct_padding resolve q cls).
  Axiom union_padding_fractional : forall cls idx, Fractional (fun q => union_padding resolve q cls idx).
  Axiom union_padding_timeless : forall q cls idx, Timeless (union_padding resolve q cls idx).
  Axiom union_padding_frac_valid : forall (q : Qp) cls idx, Observe [| q ≤ 1 |]%Qp (union_padding resolve q cls idx).

  #[global] Existing Instances
    struct_padding_fractional struct_padding_timeless struct_padding_frac_valid
    union_padding_fractional union_padding_timeless union_padding_frac_valid.

  #[global] Instance struct_padding_as_fractional q cls :
    AsFractional (struct_padding resolve q cls) (λ q, struct_padding resolve q cls) q.
  Proof. exact: Build_AsFractional. Qed.
  #[global] Instance union_padding_as_fractional q cls idx :
    AsFractional (union_padding resolve q cls idx) (λ q, union_padding resolve q cls idx) q.
  Proof. exact: Build_AsFractional. Qed.

  Axiom struct_padding_type_ptr_observe : forall q cls, Observe (type_ptrR (Tnamed cls)) (struct_padding resolve q cls).
  #[global] Existing Instance struct_padding_type_ptr_observe.
  #[global] Instance struct_padding_strict_valid_observe q cls : Observe svalidR (struct_padding resolve q cls).
  Proof. rewrite -type_ptrR_svalidR; apply _. Qed.
  #[global] Instance struct_padding_valid_observe q cls : Observe validR (struct_padding resolve q cls).
  Proof. rewrite -svalidR_validR; apply _. Qed.

  Axiom union_padding_type_ptr_observe : forall q cls i, Observe (type_ptrR (Tnamed cls)) (union_padding resolve q cls i).
  #[global] Existing Instance union_padding_type_ptr_observe.
  #[global] Instance union_padding_strict_valid_observe q cls i : Observe svalidR (union_padding resolve q cls i).
  Proof. rewrite -type_ptrR_svalidR; apply _. Qed.
  #[global] Instance union_padding_valid_observe q cls i : Observe validR (union_padding resolve q cls i).
  Proof. rewrite -svalidR_validR; apply _. Qed.

  (* TODO: Do we need type_ptrR here? *)
  Axiom struct_to_raw : forall cls st rss (q : Qp),
    glob_def resolve cls = Some (Gstruct st) ->
    st.(s_layout) = POD ->
    ([∗ list] fld ∈ st.(s_fields),
       Exists rs, [| rss !! fld.(mem_name) = Some rs |] **
       _offsetR (_field {| f_name := fld.(mem_name) ; f_type := cls |}) (rawsR q rs))
      ** struct_padding resolve q cls -|-
      Exists rs, rawsR q rs ** [| raw_bytes_of_struct resolve cls rss rs |].

  Definition implicit_destruct_ty (ty : type) := anyR ty 1 |-- |={↑pred_ns}=> tblockR ty 1.


  (** implicit destruction of a primitive *)
  Axiom implicit_destruct_int : forall sz sgn, Reduce (implicit_destruct_ty (Tint sz sgn)).
  Axiom implicit_destruct_bool : Reduce (implicit_destruct_ty Tbool).
  Axiom implicit_destruct_nullptr : Reduce (implicit_destruct_ty Tnullptr).
  Axiom implicit_destruct_ptr : forall ty, Reduce (implicit_destruct_ty (Tptr ty)).
  Axiom implicit_destruct_member_pointer : forall cls ty, Reduce (implicit_destruct_ty (Tmember_pointer cls ty)).

  (** implicit destruction of an aggregate *)
  Axiom implicit_destruct_struct
  : forall cls st,
      glob_def resolve cls = Some (Gstruct st) ->
      st.(s_trivially_destructible) ->
      type_ptrR (Tnamed cls)
      |-- (([∗list] base ∈ st.(s_bases),
         let '(gn,_) := base in
         _offsetR (_base cls gn) (tblockR (Tnamed gn) 1)) **
      ([∗list] fld ∈ st.(s_fields),
         _offsetR (_field {| f_name := fld.(mem_name) ; f_type := cls |})
                  (tblockR (erase_qualifiers fld.(mem_type)) 1)) **
      (if has_vtable st (* this is almost certainly [false] if the
                           object is trivially destructible. *)
       then identityR cls None 1
       else emp)
      ** struct_padding resolve 1 cls)
      -* |={↑pred_ns}=> tblockR (Tnamed cls) 1.

  (** decompose a struct into its constituent fields and base classes.
   *)
  Axiom anyR_struct
  : forall cls st,
    glob_def resolve cls = Some (Gstruct st) ->
        anyR (Tnamed cls) 1
    -|- ([∗list] base ∈ st.(s_bases),
              let '(gn,_) := base in
              _offsetR (_base cls gn) (anyR (Tnamed gn) 1)) **
           ([∗list] fld ∈ st.(s_fields),
              _offsetR (_field {| f_name := fld.(mem_name) ; f_type := cls |})
                       (anyR (erase_qualifiers fld.(mem_type)) 1)) **
           (if has_vtable st
            then identityR cls None 1
            else emp)
           ** struct_padding resolve 1 cls.

  (** implicit destruction of a union. *)
  Axiom implicit_destruct_union
  : forall (cls : globname) st,
      glob_def resolve cls = Some (Gunion st) ->
      type_ptrR (Tnamed cls)
      |-- ([∨list] idx↦it ∈ st.(u_fields),
           let f := _field {| f_name := it.(mem_name) ; f_type := cls |} in
           f |-> tblockR (erase_qualifiers it.(mem_type)) 1 **
           union_padding resolve 1 cls idx)
          -* |={↑pred_ns}=> tblockR (Tnamed cls) 1.

(*
  (* the following rule would allow you to change the active entity in a union
     using only ghost code. The C++ semantics does not permit this, rather
     it requires this to happen in code, so we will need to fuse this rule into
     the assignment rule.

     NOTE the axiom requires the the union element has been destructed
          (which will often be done implicitly), and the result gives you
          uninitialized memory ([tblockR]).

     NOTE C++ permits this rule to be slightly stronger becaues it guarantees
          that if two fields have common prefixes, that those values are preserved
          across this operation.
   *)
  Axiom union_change
  : forall (cls : globname) st,
      glob_def resolve cls = Some (Gunion st) ->
(*      st.(u_trivially_destructible) -> *)
      type_ptrR (Tnamed cls)
      |-- ([∨ list] idx ↦ it ∈ st.(u_fields),
           let f := _field {| f_name := it.(mem_name) ; f_type := cls |} in
           f |-> tblockR (erase_qualifiers it.(mem_type)) 1 **
           union_padding resolve 1 cls idx)
      -* [∧ list] idx ↦ it ∈ st.(u_fields),
          let f := _field {| f_name := it.(mem_name) ; f_type := cls |} in
          |={↑pred_ns}=> f |-> tblockR (erase_qualifiers it.(mem_type)) 1 **
               union_padding resolve 1 cls idx.
*)

  (** decompose a union into the classical disjunction of the alternatives
   *)
  Axiom anyR_union
  : forall (cls : globname) st,
    glob_def resolve cls = Some (Gunion st) ->
        anyR (Tnamed cls) 1
    -|- [∨ list] idx↦it ∈ st.(u_fields),
           let f := _field {| f_name := it.(mem_name) ; f_type := cls |} in
           _offsetR f (anyR (erase_qualifiers it.(mem_type)) 1) **
           union_padding resolve 1 cls idx.

  (** decompose an array into individual components
      note that one past the end of an array is a valid location, but
      it doesn't store anything.

      TODO this should move
   *)
  Theorem tblockR_array : forall t n q,
      (0 < n)%N ->
        tblockR (Tarray t n) q
    -|- _offsetR (_sub t (Z.of_N n)) validR **
        [∗list] i ↦ _ ∈ repeat () (BinNatDef.N.to_nat n),
           _offsetR (_sub t (Z.of_nat i)) (tblockR t q).
  Proof.
    rewrite /tblockR /=. intros.
    assert (exists n', BinNatDef.N.to_nat n = S n').
    { admit. }
    destruct H0. rewrite H0. simpl.
    rewrite align_of_array.
    destruct (size_of resolve t) => /=.
    { case_match; eauto.
      { admit. }
      { split'. iIntros "[]".
        rewrite _offsetR_pure. iIntros "(? & [] & ?)". } }
    { split'; try solve [ iIntros "[]" ].
      rewrite _offsetR_pure. iIntros "(? & [] & ?)". }
  Admitted.

End with_Σ.
