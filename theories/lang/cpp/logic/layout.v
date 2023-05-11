(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import base numbers list.
Require Import iris.proofmode.proofmode.

Require Import bedrock.lang.cpp.arith.z_to_bytes.
Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred translation_unit.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.logic.arr.
Require Export bedrock.lang.cpp.logic.raw.

Require Import bedrock.lang.bi.linearity.

Section with_Σ.
  Context `{Σ : cpp_logic}.

  (** TODO move to pred.v *)
  (* TODO swap the order of [cQp.t] and [globname] *)
  Axiom struct_paddingR : forall {σ:genv}, cQp.t -> globname -> Rep.

  (* [union_paddingR q cls active_member] is [q] fractional ownership of
     the union padding for union [cls] for the active member
     [active_member]. When there is no active member the [active_member]
     is [None], otherwise it is [Some idx] where [idx] is the numeric
     index of member field.

     TODO swap the order of [cQp.t] and [globname].
  *)
  Axiom union_paddingR : forall {σ:genv}, cQp.t -> globname -> option nat -> Rep.

  Context {σ : genv}.

  #[global] Declare Instance struct_padding_fractional : CFractional1 struct_paddingR.
  #[global] Declare Instance struct_padding_timeless : Timeless2 struct_paddingR.
  #[global] Declare Instance struct_padding_frac_valid : CFracValid1 struct_paddingR.

  #[global] Declare Instance union_padding_fractional : CFractional2 union_paddingR.
  #[global] Declare Instance union_padding_timeless : Timeless3 union_paddingR.
  #[global] Declare Instance union_padding_frac_valid : CFracValid2 union_paddingR.

  #[global] Instance struct_padding_as_fractional : AsCFractional1 struct_paddingR.
  Proof. solve_as_cfrac. Qed.
  #[global] Instance union_padding_as_fractional : AsCFractional2 union_paddingR.
  Proof. solve_as_cfrac. Qed.

  #[global] Declare Instance struct_paddingR_type_ptr_observe : forall q cls, Observe (type_ptrR (Tnamed cls)) (struct_paddingR q cls).
  #[global] Instance struct_paddingR_strict_valid_observe q cls : Observe svalidR (struct_paddingR q cls).
  Proof. rewrite -type_ptrR_svalidR; apply _. Qed.
  #[global] Instance struct_paddingR_valid_observe q cls : Observe validR (struct_paddingR q cls).
  Proof. rewrite -svalidR_validR; apply _. Qed.

  #[global] Declare Instance union_paddingR_type_ptr_observe : forall q cls i, Observe (type_ptrR (Tnamed cls)) (union_paddingR q cls i).
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
    anyR ty (cQp.mut 1) |-- |={↑pred_ns}=> tblockR ty (cQp.mut 1).

  (** implicit destruction of a primitive *)
  Axiom implicit_destruct_int : forall sz sgn, Reduce (implicit_destruct_ty (Tnum sz sgn)).
  Axiom implicit_destruct_bool : Reduce (implicit_destruct_ty Tbool).
  Axiom implicit_destruct_nullptr : Reduce (implicit_destruct_ty Tnullptr).
  Axiom implicit_destruct_ptr : forall ty, Reduce (implicit_destruct_ty (Tptr ty)).
  Axiom implicit_destruct_member_pointer : forall cls ty, Reduce (implicit_destruct_ty (Tmember_pointer cls ty)).

  (** [mut_type m q] is the ownership [cQp.t] and the type used for a [Member] *)
  Definition mut_type (m : Member) (q : cQp.t) : cQp.t * type :=
    let '(cv, ty) := decompose_type m.(mem_type) in
    let q := if q_const cv && negb m.(mem_mutable) then cQp.c q else q in
    (q, erase_qualifiers ty).

  (** [struct_def R cls st q] is the ownership of the class where [R ty q] is
      owned for each field and base class *)
  Definition struct_def (R : type -> cQp.t -> Rep) (cls : globname) (st : Struct) (q : cQp.t) : Rep :=
    ([** list] base ∈ st.(s_bases),
       let '(gn,_) := base in
       _base cls gn |-> R (Tnamed gn) q) **
    ([** list] fld ∈ st.(s_fields),
      let f := {| f_name := fld.(mem_name) ; f_type := cls |} in
      let qt := mut_type fld q in
      _field f |-> R qt.2 qt.1) **
    (if has_vtable st then identityR cls nil q else emp) **
    struct_paddingR q cls.

  (** implicit destruction of an aggregate *)
  Axiom implicit_destruct_struct
  : forall cls st q,
      glob_def σ cls = Some (Gstruct st) ->
      st.(s_trivially_destructible) ->
      cQp.frac q = 1%Qp ->
          type_ptrR (Tnamed cls)
      |-- (Reduce (struct_def tblockR cls st q)) -*
          |={↑pred_ns}=> tblockR (Tnamed cls) q.

  (** decompose a struct into its constituent fields and base classes. *)
  Axiom anyR_struct : forall cls st q,
    glob_def σ cls = Some (Gstruct st) ->
        anyR (Tnamed cls) q
    -|- Reduce (struct_def anyR cls st q).

  (** [union_def R cls st q] is the ownership of the union where [R ty q] is
      owned for each field and base class *)
  Definition union_def (R : type -> cQp.t -> Rep) (cls : globname) (st : translation_unit.Union) (q : cQp.t) : Rep :=
    union_paddingR q cls None \\//
    ([\/ list] idx |-> m ∈ st.(u_fields),
      let f := _field {| f_name := m.(mem_name) ; f_type := cls |} in
      let qt := mut_type m q in
      f |-> R qt.2 qt.1 **
      union_paddingR q cls (Some idx)).

  (** implicit destruction of a union. *)
  Axiom implicit_destruct_union : forall (cls : globname) un q,
      glob_def σ cls = Some (Gunion un) ->
      un.(u_trivially_destructible) ->
      cQp.frac q = 1%Qp ->
          type_ptrR (Tnamed cls)
      |-- (Reduce (union_def tblockR cls un q)) -* |={↑pred_ns}=> tblockR (Tnamed cls) q.

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
      |-- (union_def (fun ty => tblockR ty (cQp.mut 1)) cls un)
      -* [∧ list] idx ↦ it ∈ un.(u_fields),
          let f := _field {| f_name := it.(mem_name) ; f_type := cls |} in
          |={↑pred_ns}=> f |-> tblockR (erase_qualifiers it.(mem_type)) (cQp.mut 1) **
               union_paddingR resolve (cQp.mut 1) cls (Some idx).
*)

  (** decompose a union into the classical disjunction of the alternatives
   *)
  Axiom anyR_union : forall (cls : globname) un q,
    glob_def σ cls = Some (Gunion un) ->
        anyR (Tnamed cls) q
    -|- Reduce (union_def anyR cls un q).

  (** Proof requires the generalization of [anyR] to support aggregates (and arrays) *)
  Lemma anyR_array_0 t q :
    anyR (Tarray t 0) q -|- validR ** [| is_Some (size_of σ t) |].
  Proof. Admitted.

  Lemma anyR_array_succ t n q :
    anyR (Tarray t (N.succ n)) q -|-
    type_ptrR t ** anyR t q ** .[ t ! 1 ] |-> anyR (Tarray t n) q.
  Proof. Admitted.

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
    -|- _sub t (Z.of_N n) |-> validR **
        [∗list] i ↦ _ ∈ repeat () (BinNatDef.N.to_nat n),
           _sub t (Z.of_nat i) |-> tblockR t q.
  Proof. Admitted.

  #[global] Instance struct_paddingR_nonnull q cls : Observe nonnullR (struct_paddingR q cls).
  Proof.
    iIntros "H".
    iDestruct (observe (type_ptrR _) with "H") as "#T".
    iApply (observe with "T").
  Qed.
End with_Σ.
