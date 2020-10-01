(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import iris.proofmode.tactics.
From iris.bi.lib Require Import fractional.

Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred translation_unit.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.logic.z_to_bytes.

Section array.
  Context `{Σ : cpp_logic} {resolve:genv}.
  Context {T : Type}.
  Variable sz : Z.
  Variable (P : T -> Rep).

  Fixpoint array' (ls : list T) (p : ptr) : mpred :=
    match ls with
    | nil => valid_ptr p
    | l :: ls =>
      _at (_eq p) (P l) ** array' ls (offset_ptr_ sz p)
    end.
End array.

Section with_Σ.
  Context `{Σ : cpp_logic} {resolve:genv}.

  Local Notation _super := (_super (resolve:=resolve)) (only parsing).
  Local Notation _field := (_field (resolve:=resolve)) (only parsing).
  Local Notation _sub := (_sub (resolve:=resolve)) (only parsing).
  Local Notation anyR := (anyR (resolve:=resolve)) (only parsing).
  Local Notation primR := (primR (resolve:=resolve)) (only parsing).

  Axiom struct_padding : genv -> Qp -> globname -> Rep.
  Axiom union_padding : genv -> Qp -> globname -> nat -> Rep.

  Axiom struct_padding_fractional : forall cls, Fractional (fun q => struct_padding resolve q cls).
  Axiom struct_padding_timeless : forall q cls, Timeless  (struct_padding resolve q cls).
  Axiom union_padding_fractional : forall cls idx, Fractional (fun q => union_padding resolve q cls idx).
  Axiom union_padding_timeless : forall q cls idx, Timeless (union_padding resolve q cls idx).

  Global Instance struct_padding_as_fractional q cls :
    AsFractional (struct_padding resolve q cls) (λ q, struct_padding resolve q cls) q.
  Proof. constructor. done. apply struct_padding_fractional. Qed.
  Global Instance union_padding_as_fractional q cls idx :
    AsFractional (union_padding resolve q cls idx) (λ q, union_padding resolve q cls idx) q.
  Proof. constructor. done. apply union_padding_fractional. Qed.

  (** [raw_values_of_val σ ty v rs] states that the value [v] of type
  [ty] is represented by the raw bytes in [rs]. WHat this means
  depends on the type [ty]. *)
  Axiom raw_bytes_of_val : genv -> type -> val -> list raw_byte -> Prop.

  (** [raw_bytes_of_struct σ cls rss rs] states that the struct
  consisting of fields of the raw bytes [rss] is represented by the
  raw bytes in [rs]. [rs] should agree with [rss] on the offsets of
  the fields. It might be possible to make some assumptions about the
  parts of [rs] that represent padding based on the ABI. *)
  Axiom raw_bytes_of_struct : genv -> globname -> gmap ident (list raw_byte) -> list raw_byte -> Prop.

  Axiom raw_bytes_of_sizeof : forall ty v rs,
     raw_bytes_of_val resolve ty v rs -> size_of resolve ty = Some (N.of_nat $ length rs).

  Definition rawR (rs : list raw_byte) (q : Qp) : Rep :=
    as_Rep (array' 1 (fun r => primR T_uchar q (Vraw r)) rs).

  Axiom primR_to_rawR: forall ty q v,
    primR ty q v -|- Exists rs, rawR rs q ** [| raw_bytes_of_val resolve ty v rs |] ** _type_ptr resolve ty.

  (* TODO: Do we need _type_ptr here? *)
  Axiom struct_to_raw : forall cls st rss q,
    glob_def resolve cls = Some (Gstruct st) ->
    st.(s_layout) = POD ->
    ([∗ list] fld ∈ st.(s_fields), let '(n,ty,_,_) := fld in
       Exists r, [| rss !! n = Some r |] **
       _offsetR (_field {| f_name := n ; f_type := cls |}) (rawR r q))
      ** struct_padding resolve q cls -|-
      Exists rs, rawR rs q ** [| raw_bytes_of_struct resolve cls rss rs |].

  (** decompose a struct into its constituent fields and base classes.
   *)
  Axiom decompose_struct
  : forall cls st,
    glob_def resolve cls = Some (Gstruct st) ->
        anyR (Tnamed cls) 1
    -|- ([∗list] base ∈ st.(s_bases),
              let '(gn,_) := base in
              _offsetR (_super cls gn) (anyR (Tnamed gn) 1)) **
           ([∗list] fld ∈ st.(s_fields),
              let '(n,ty,_,_) := fld in
              _offsetR (_field {| f_name := n ; f_type := cls |})
                       (anyR (erase_qualifiers ty) 1)) **
           (if has_vtable st
            then _identity resolve cls None 1
            else empSP)
           ** struct_padding resolve 1 cls.

  (** decompose a union into the classical conjunction of the alternatives
   *)
  Axiom decompose_union
  : forall (cls : globname) st,
    glob_def resolve cls = Some (Gunion st) ->
        anyR (Tnamed cls) 1
    -|- [∧list] idx↦it ∈ st.(u_fields),
           let '(i, t, _, _) := it in
           let f := _field {| f_name := i ; f_type := cls |} in
           _offsetR f (anyR (erase_qualifiers t) 1) **
           union_padding resolve 1 cls idx.

  (** decompose an array into individual components
      note that one past the end of an array is a valid location, but
      it doesn't store anything.
   *)
  Axiom decompose_array : forall t n,
        anyR (Tarray t n) 1
    -|- _offsetR (_sub t (Z.of_N n)) empSP **
        (* ^ note: this is equivalent to [valid_loc (this .[ t ! n ])] *)
        [∗list] i ↦ _ ∈ repeat () (BinNatDef.N.to_nat n),
                _offsetR (_sub t (Z.of_nat i)) (anyR t 1).

  Local Notation Unfold x tm :=
    ltac:(let H := eval unfold x in tm in exact H) (only parsing).

  Definition decodes (endianness: endian) (sgn: signed) (l: list N) (z: Z) :=
    _Z_from_bytes endianness sgn l = z.

  (* JH: TODO: Deprecate the following stuff *)
  Definition decodes_uint (l : list N) (z : Z) :=
    Unfold decodes (decodes (values.byte_order resolve) Unsigned l z).

  (* JH: TODO: Determine what new axioms we should add here. *)
  Axiom raw_byte_of_int_eq : forall sz x rs,
      raw_bytes_of_val resolve (Tint sz Unsigned) (Vint x) rs <-> (exists l, decodes_uint l x /\ rs = raw_int_byte <$> l).

  Axiom raw_int_byte_primR : forall q r,
      primR T_uchar q (Vraw (raw_int_byte r)) -|- primR T_uchar q (Vint (Z.of_N r)).

  Lemma decode_uint_primR : forall q sz (x : Z),
    primR (Tint sz Unsigned) q (Vint x) -|-
    Exists l : list N,
      as_Rep (array' 1 (fun c => primR (Tint W8 Unsigned) q (Vint c))
             (Z.of_N <$> l)) **
      _type_ptr resolve (Tint sz Unsigned) **
      [| decodes_uint l x |].
  Proof.
    move => q sz x.
    rewrite primR_to_rawR. setoid_rewrite raw_byte_of_int_eq.
    iSplit.
    - iDestruct 1 as (rs) "(Hraw&H&$)". iDestruct "H" as %[l [Hdec ->]]. iExists _. iSplit => //. clear Hdec.
      rewrite /rawR. iStopProof. constructor => p /=. iIntros "Hraw".
      iInduction l as [ |b l] "IH" forall (p) => //; csimpl. rewrite raw_int_byte_primR.
      iDestruct "Hraw" as "[$ Hrs]". iApply "IH" => //; iPureIntro.
    - iDestruct 1 as (l) "(Harray&$&H)". iDestruct "H" as %Hdec.
      iExists _. iSplit => //; eauto with iFrame. rewrite /rawR. clear Hdec.
      iStopProof. constructor => p /=. iIntros "Hraw".
      iInduction l as [ |b l] "IH" forall (p) => //; csimpl. rewrite raw_int_byte_primR.
      iDestruct "Hraw" as "[$ Hrs]". iApply "IH" => //; iPureIntro.
  Qed.

  Axiom decode_uint_anyR : forall q sz,
    anyR (Tint sz Unsigned) q -|-
         anyR (Tarray T_uchar (bytesN sz)) q **
         _type_ptr resolve (Tint sz Unsigned).
End with_Σ.

Existing Instances
  struct_padding_fractional struct_padding_timeless
  union_padding_fractional union_padding_timeless
.
