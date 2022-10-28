(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import base numbers list.
Require Import iris.proofmode.proofmode.
From iris.bi.lib Require Import fractional.

Require Import bedrock.lang.cpp.arith.z_to_bytes.
Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred translation_unit.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.logic.arr.
Require Export bedrock.lang.cpp.logic.raw.

Require Import bedrock.lang.cpp.heap_notations.
Require Import bedrock.lang.bi.linearity.

Section with_Σ.
  Context `{Σ : cpp_logic}.

  (** TODO move to pred.v *)
  Axiom struct_paddingR : forall {σ:genv}, Qp -> globname -> Rep.

  (* [union_paddingR q cls active_member] is [q] fractional ownership of
     the union padding for union [cls] for the active member
     [active_member]. When there is no active member the [active_member]
     is [None], otherwise it is [Some idx] where [idx] is the numeric
     index of member field.
  *)
  Axiom union_paddingR : forall {σ:genv}, Qp -> globname -> option nat -> Rep.

  Context {σ : genv}.

  Axiom struct_padding_fractional : forall cls, Fractional (fun q => struct_paddingR q cls).
  Axiom struct_padding_timeless : forall q cls, Timeless  (struct_paddingR q cls).
  Axiom struct_padding_frac_valid : forall (q : Qp) cls, Observe [| q ≤ 1 |]%Qp (struct_paddingR q cls).
  Axiom union_padding_fractional : forall cls idx, Fractional (fun q => union_paddingR q cls idx).
  Axiom union_padding_timeless : forall q cls idx, Timeless (union_paddingR q cls idx).
  Axiom union_padding_frac_valid : forall (q : Qp) cls idx, Observe [| q ≤ 1 |]%Qp (union_paddingR q cls idx).

  #[global] Existing Instances
    struct_padding_fractional struct_padding_timeless struct_padding_frac_valid
    union_padding_fractional union_padding_timeless union_padding_frac_valid.

  #[global] Instance struct_padding_as_fractional q cls :
    AsFractional (struct_paddingR q cls) (λ q, struct_paddingR q cls) q.
  Proof. exact: Build_AsFractional. Qed.
  #[global] Instance union_padding_as_fractional q cls idx :
    AsFractional (union_paddingR q cls idx) (λ q, union_paddingR q cls idx) q.
  Proof. exact: Build_AsFractional. Qed.

  Axiom struct_paddingR_type_ptr_observe : forall q cls, Observe (type_ptrR (Tnamed cls)) (struct_paddingR q cls).
  #[global] Existing Instance struct_paddingR_type_ptr_observe.
  #[global] Instance struct_paddingR_strict_valid_observe q cls : Observe svalidR (struct_paddingR q cls).
  Proof. rewrite -type_ptrR_svalidR; apply _. Qed.
  #[global] Instance struct_paddingR_valid_observe q cls : Observe validR (struct_paddingR q cls).
  Proof. rewrite -svalidR_validR; apply _. Qed.

  Axiom union_paddingR_type_ptr_observe : forall q cls i, Observe (type_ptrR (Tnamed cls)) (union_paddingR q cls i).
  #[global] Existing Instance union_paddingR_type_ptr_observe.
  #[global] Instance union_paddingR_strict_valid_observe q cls i : Observe svalidR (union_paddingR q cls i).
  Proof. rewrite -type_ptrR_svalidR; apply _. Qed.
  #[global] Instance union_paddingR_valid_observe q cls i : Observe validR (union_paddingR q cls i).
  Proof. rewrite -svalidR_validR; apply _. Qed.

  (** Convert a `struct` to its raw representation.
   Justified by the concept of object representation.
   https://eel.is/c++draft/basic.types.general#def:representation,object
   *)
  Axiom struct_to_raw : forall cls st rss q,
    glob_def σ cls = Some (Gstruct st) ->
    st.(s_layout) ∈ [POD;Standard] ->
       struct_paddingR q cls **
       ([∗ list] b ∈ st.(s_bases),
          Exists rs, [| rss !! FieldOrBase.Base b.1 = Some rs |] ** _base cls b.1 |-> rawsR q rs) **
       ([∗ list] fld ∈ st.(s_fields),
          Exists rs, [| rss !! FieldOrBase.Field fld.(mem_name) = Some rs |] **
            _field {| f_name := fld.(mem_name) ; f_type := cls |} |-> rawsR q rs)
    -|- type_ptrR (Tnamed cls) **
      Exists rs, rawsR q rs ** [| raw_bytes_of_struct σ cls rss rs |].

  #[local] Definition implicit_destruct_ty (ty : type) :=
    anyR ty 1 |-- |={↑pred_ns}=> tblockR ty 1.

  (** implicit destruction of a primitive *)
  Axiom implicit_destruct_int : forall sz sgn, Reduce (implicit_destruct_ty (Tnum sz sgn)).
  Axiom implicit_destruct_bool : Reduce (implicit_destruct_ty Tbool).
  Axiom implicit_destruct_nullptr : Reduce (implicit_destruct_ty Tnullptr).
  Axiom implicit_destruct_ptr : forall ty, Reduce (implicit_destruct_ty (Tptr ty)).
  Axiom implicit_destruct_member_pointer : forall cls ty, Reduce (implicit_destruct_ty (Tmember_pointer cls ty)).

  Definition struct_def (R : type -> Rep) (cls : globname) (st : Struct) : Rep :=
    ([∗list] base ∈ st.(s_bases),
       let '(gn,_) := base in
       _offsetR (_base cls gn) (R (Tnamed gn))) **
    ([∗list] fld ∈ st.(s_fields),
       _offsetR (_field {| f_name := fld.(mem_name) ; f_type := cls |})
                (R (erase_qualifiers fld.(mem_type)))) **
    (if has_vtable st (* this is almost certainly [false] if the
                         object is trivially destructible. *)
     then identityR cls nil 1 (** NOTE this doesn't really work out because i generally
                                   require a fancy update to forget the MDC. *)
     else emp)%I **
    struct_paddingR 1 cls.


  (** implicit destruction of an aggregate *)
  Axiom implicit_destruct_struct
  : forall cls st,
      glob_def σ cls = Some (Gstruct st) ->
      st.(s_trivially_destructible) ->
          type_ptrR (Tnamed cls)
      |-- (Reduce (struct_def (fun ty => tblockR ty 1) cls st)) -*
          |={↑pred_ns}=> tblockR (Tnamed cls) 1.

  (** decompose a struct into its constituent fields and base classes.
   *)
  Axiom anyR_struct
  : forall cls st,
    glob_def σ cls = Some (Gstruct st) ->
        anyR (Tnamed cls) 1
    -|- Reduce (struct_def (fun ty => anyR ty 1) cls st).

  Definition union_def (R : type -> Rep) (cls : globname) (st : translation_unit.Union) : Rep :=
    union_paddingR 1 cls None \\//
    [∨list] idx↦it ∈ st.(u_fields),
       let f := _field {| f_name := it.(mem_name) ; f_type := cls |} in
       f |-> R (erase_qualifiers it.(mem_type)) **
       union_paddingR 1 cls (Some idx).

  (** implicit destruction of a union. *)
  Axiom implicit_destruct_union
  : forall (cls : globname) un,
      glob_def σ cls = Some (Gunion un) ->
      un.(u_trivially_destructible) ->
          type_ptrR (Tnamed cls)
      |-- (Reduce (union_def (fun ty => tblockR ty 1) cls un)) -* |={↑pred_ns}=> tblockR (Tnamed cls) 1.

(*
  (* the following rule would allow you to change the active entity in a union
     using only ghost code. The C++ semantics does not permit this, rather
     it requires this to happen in code, so we will need to fuse this rule into
     the assignment rule.

     NOTE the axiom requires that the union element has been destructed
          (which will often be done implicitly), and the result gives you
          uninitialized memory ([tblockR]).

     NOTE C++ would permit this rule to be slightly stronger than stated here, because C++ guarantees
          that if two fields have common prefixes, that those values are preserved
          across this operation.
   *)
  Axiom union_change
  : forall (cls : globname) un,
      glob_def resolve cls = Some (Gunion un) ->
(*      un.(u_trivially_destructible) -> *)
      type_ptrR (Tnamed cls)
      |-- (union_def (fun ty => tblockR ty 1) cls un)
      -* [∧ list] idx ↦ it ∈ un.(u_fields),
          let f := _field {| f_name := it.(mem_name) ; f_type := cls |} in
          |={↑pred_ns}=> f |-> tblockR (erase_qualifiers it.(mem_type)) 1 **
               union_paddingR resolve 1 cls (Some idx).
*)

  (** decompose a union into the classical disjunction of the alternatives
   *)
  Axiom anyR_union
  : forall (cls : globname) un,
    glob_def σ cls = Some (Gunion un) ->
        anyR (Tnamed cls) 1
    -|- Reduce (union_def (fun ty => anyR ty 1) cls un).

 (** Proof requires the generalization of [anyR] to support aggregates (and arrays) *)
  Lemma anyR_array_0 t q :
    anyR (Tarray t 0) q -|- validR ** [| is_Some (size_of σ t) |].
  Admitted.

  Lemma anyR_array_succ t n q :
    anyR (Tarray t (N.succ n)) q -|-
    type_ptrR t ** anyR t q ** .[ t ! 1 ] |-> anyR (Tarray t n) q.
  Admitted.

  (** decompose an array into individual components
      note that one past the end of an array is a valid location, but
      it doesn't store anything.

      TODO this should move
   *)
  Lemma anyR_array' t n q :
        anyR (Tarray t n) q
    -|- arrayR t (fun _ => anyR t q) (replicateN n ()).
  Proof.
    induction n using N.peano_ind;
      rewrite (replicateN_0, replicateN_S) (arrayR_nil, arrayR_cons).  {
      apply anyR_array_0.
    }
    by rewrite -IHn anyR_array_succ.
  Qed.

  (* Wrapper using [repeat] instead of [replicate] for compatibility. *)
  Lemma anyR_array t n q :
        anyR (Tarray t n) q
    -|- arrayR t (fun _ => anyR t q) (repeat () (N.to_nat n)).
  Proof. by rewrite anyR_array' repeatN_replicateN. Qed.

  (** decompose an array into individual components
      note that one past the end of an array is a valid location, but
      it doesn't store anything.

      TODO this should move
   *)
  (* TODO a type has a size if and only if it has an alignment *)
  Lemma tblockR_array_better t n q sz :
        size_of σ t = Some sz ->
        tblockR (Tarray t n) q
    -|- .[ Tu8 ! Z.of_N (n * sz) ] |-> validR **
        [∗list] i ∈ seq 0 (N.to_nat n),
           .[ Tu8 ! Z.of_N (N.of_nat i * sz) ] |-> tblockR t q.
  Proof.
    rewrite /tblockR /= => Hsz.
    rewrite Hsz /= align_of_array.
    case: (align_of_size_of _ _ Hsz) => [al [Hal HalSz]].
    rewrite Hal.
    (*
    Unclear if unfolding is recommended, but at least it should be sufficient for a hacky proof;
    maybe we should lift lemmas about [blockR] (not sure which).
    *)
    rewrite blockR_eq /blockR_def.
    rewrite -assoc.
    f_equiv.
    (* Maybe useful? *)
    apply Rep_equiv_at => p.
    (* To finish the proof, we need to rearrange [anyR], use [o_sub_sub] & c and
    [anyR_valid_observe], and reason about pointer alignment. For alignment, we
    need to unfold [alignedR], and maybe [aligned_ptr]. *)
  Admitted.

  (* TODO: migrate client to the statement above, and drop this. *)
  Lemma tblockR_array : forall t n q,
        tblockR (Tarray t n) q
    -|- _offsetR (_sub t (Z.of_N n)) validR **
        [∗list] i ↦ _ ∈ repeat () (BinNatDef.N.to_nat n),
           _offsetR (_sub t (Z.of_nat i)) (tblockR t q).
  Admitted.

End with_Σ.
