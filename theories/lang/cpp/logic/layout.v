(*
 * Copyright (c) 2020 BedRock Systems, Inc.
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

Require Import bedrock.lang.cpp.heap_notations.

Section with_Σ.
  Context `{Σ : cpp_logic} {resolve:genv}.

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

  Axiom struct_padding_strict_valid_observe : forall q cls, Observe svalidR (struct_padding resolve q cls).
  #[global] Existing Instance struct_padding_strict_valid_observe.
  #[global] Instance struct_padding_valid_observe q cls : Observe validR (struct_padding resolve q cls).
  Proof. rewrite -svalidR_validR. apply _. Qed.

  Axiom union_padding_strict_valid_observe : forall q cls i, Observe svalidR (union_padding resolve q cls i).
  #[global] Existing Instance union_padding_strict_valid_observe.
  #[global] Instance union_padding_valid_observe q cls i : Observe validR (union_padding resolve q cls i).
  Proof. rewrite -svalidR_validR. apply _. Qed.

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

  (** [rawR q rs]: the argument pointer points to [raw_byte] [r] within the C++ abstract machine. *)
  Definition rawR_def (q : Qp) (r : raw_byte) : Rep :=
    as_Rep (fun p => tptsto T_uchar q p (Vraw r)).
  Definition rawR_aux : seal (@rawR_def). Proof. by eexists. Qed.
  Definition rawR := rawR_aux.(unseal).
  Definition rawR_eq : @rawR = _ := rawR_aux.(seal_eq).
  #[global] Arguments rawR q raw : rename.

  #[global] Instance rawR_proper :
    Proper ((=) ==> (=) ==> (⊣⊢)) (@rawR).
  Proof. by intros ??-> ??->. Qed.
  #[global] Instance rawR_mono :
    Proper ((=) ==> (=) ==> (⊢)) (@rawR).
  Proof. by intros ??-> ??->. Qed.

  #[global] Instance rawR_affine q raw
    : Affine (rawR q raw).
  Proof. rewrite rawR_eq. apply _. Qed.
  #[global] Instance rawR_timeless q raw
    : Timeless (rawR q raw).
  Proof. rewrite rawR_eq. apply _. Qed.

  #[global] Instance rawR_fractional raw :
    Fractional (λ q, rawR q raw).
  Proof. rewrite rawR_eq. apply _. Qed.
  #[global] Instance rawR_as_fractional q raw :
    AsFractional (rawR q raw) (λ q, rawR q raw) q.
  Proof. constructor. done. apply _. Qed.

  #[global] Instance rawR_observe_frac_valid (q : Qp) raw :
    Observe [| q ≤ 1 |]%Qp (rawR q raw).
  Proof. rewrite rawR_eq. apply _. Qed.

  #[global] Instance rawR_observe_agree q1 q2 raw1 raw2 :
    Observe2 [| raw1 = raw2 |] (rawR q1 raw1) (rawR q2 raw2).
  Proof.
    rewrite rawR_eq/rawR_def.
    apply: as_Rep_only_provable_observe_2=> p.
    iIntros "Hptsto1 Hptsto2".
    iPoseProof (tptsto_agree_raw with "Hptsto1 Hptsto2") as "%Hraws"; eauto.
    iModIntro; iPureIntro; by inversion Hraws.
  Qed.

  Definition rawsR (q : Qp) (rs : list raw_byte) : Rep := arrayR T_uchar (rawR q) rs.

  #[global] Instance rawsR_proper :
    Proper ((=) ==> (=) ==> (⊣⊢)) (@rawsR).
  Proof. by intros ??-> ??->. Qed.
  #[global] Instance rawsR_mono :
    Proper ((=) ==> (=) ==> (⊢)) (@rawsR).
  Proof. by intros ??-> ??->. Qed.

  #[global] Instance rawsR_affine q rs
    : Affine (rawsR q rs).
  Proof. apply _. Qed.
  #[global] Instance rawsR_timeless q rs
    : Timeless (rawsR q rs).
  Proof. apply _. Qed.

  #[global] Instance rawsR_fractional rs :
    Fractional (λ q, rawsR q rs).
  Proof. apply _. Qed.
  #[global] Instance rawsR_as_fractional q rs :
    AsFractional (rawsR q rs) (λ q, rawsR q rs) q.
  Proof. constructor. done. apply _. Qed.

  #[global] Instance rawsR_observe_frac_valid (q : Qp) rs :
    (0 < length rs) ->
    Observe [| q ≤ 1 |]%Qp (rawsR q rs).
  Proof.
    intros Hlen; rewrite /rawsR; induction rs;
      by [ simpl in Hlen; lia
         | rewrite arrayR_cons; apply _].
  Qed.

  #[global] Instance rawsR_observe_agree q1 q2 rs1 rs2 :
    length rs1 = length rs2 ->
    Observe2 [| rs1 = rs2 |] (rawsR q1 rs1) (rawsR q2 rs2).
  Proof.
    generalize dependent rs2; induction rs1 as [| r1 ? ?]; intros * Hlen.
    - destruct rs2; [| simpl in Hlen; lia].
      rewrite /Observe2; iIntros "? ? !>"; by iPureIntro.
    - destruct rs2 as [| r2 ?]; [simpl in Hlen; lia |].
      rewrite !cons_length in Hlen; inversion Hlen.
      rewrite /rawsR !arrayR_cons;
        fold (rawsR q1 rs1);
        fold (rawsR q2 rs2).
      iIntros "(Htype_ptrR1 & HrawR1 & HrawsR1)
               (Htype_ptrR2 & HrawR2 & HrawsR2)".
      iDestruct (observe_2 [| r1 = r2 |] with "HrawR1 HrawR2") as %->.
      specialize (IHrs1 rs2 ltac:(auto)).
      iDestruct (observe_2 [| rs1 = rs2 |] with "HrawsR1 HrawsR2") as %->.
      iModIntro; by iPureIntro.
  Qed.

  Axiom primR_to_rawsR: forall ty q v,
    primR ty q v -|- Exists rs, rawsR q rs ** [| raw_bytes_of_val resolve ty v rs |] ** type_ptrR ty.

  (* TODO: Do we need type_ptrR here? *)
  Axiom struct_to_raw : forall cls st rss q,
    glob_def resolve cls = Some (Gstruct st) ->
    st.(s_layout) = POD ->
    ([∗ list] fld ∈ st.(s_fields), let '(n,ty,_,_) := fld in
       Exists rs, [| rss !! n = Some rs |] **
       _offsetR (_field {| f_name := n ; f_type := cls |}) (rawsR q rs))
      ** struct_padding resolve q cls -|-
      Exists rs, rawsR q rs ** [| raw_bytes_of_struct resolve cls rss rs |].

  (** decompose a struct into its constituent fields and base classes.
   *)
  Axiom decompose_struct
  : forall cls st,
    glob_def resolve cls = Some (Gstruct st) ->
        anyR (Tnamed cls) 1
    -|- ([∗list] base ∈ st.(s_bases),
              let '(gn,_) := base in
              _offsetR (_base cls gn) (anyR (Tnamed gn) 1)) **
           ([∗list] fld ∈ st.(s_fields),
              let '(n,ty,_,_) := fld in
              _offsetR (_field {| f_name := n ; f_type := cls |})
                       (anyR (erase_qualifiers ty) 1)) **
           (if has_vtable st
            then identityR cls None 1
            else emp)
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
    -|- _offsetR (_sub t (Z.of_N n)) validR **
        [∗list] i ↦ _ ∈ repeat () (BinNatDef.N.to_nat n),
                _offsetR (_sub t (Z.of_nat i)) (anyR t 1).

  Definition decodes (endianness: endian) (sgn: signed) (l: list N) (z: Z) :=
    _Z_from_bytes endianness sgn l = z.

  (* JH: TODO: Deprecate the following stuff *)
  Definition decodes_uint (l : list N) (z : Z) :=
    Unfold decodes (decodes (genv_byte_order resolve) Unsigned l z).

  (* JH: TODO: Determine what new axioms we should add here. *)
  Axiom raw_byte_of_int_eq : forall sz x rs,
      raw_bytes_of_val resolve (Tint sz Unsigned) (Vint x) rs <-> (exists l, decodes_uint l x /\ rs = raw_int_byte <$> l).

  Axiom raw_int_byte_primR : forall q r,
      rawR q (raw_int_byte r) -|- primR T_uchar q (Vint (Z.of_N r)).

  (** TODO: determine whether this is correct with respect to pointers *)
  Lemma decode_uint_primR : forall q sz (x : Z),
    primR (Tint sz Unsigned) q (Vint x) -|-
    Exists l : list N,
      arrayR (Tint W8 Unsigned) (fun c => primR (Tint W8 Unsigned) q (Vint c)) (Z.of_N <$> l) **
      type_ptrR (Tint sz Unsigned) **
      [| decodes_uint l x |].
  Proof.
    move => q sz x.
    rewrite primR_to_rawsR. setoid_rewrite raw_byte_of_int_eq.
    iSplit.
    - iDestruct 1 as (rs) "(Hraw & H & $)".
      iDestruct "H" as %[l [Hdec ->]].
      iExists _; iSplit => //. clear Hdec.
      rewrite /rawsR arrayR_eq/arrayR_def. iStopProof.
      (* TODO i need to do induction here because the [Proper] instances are too weak. *)
      induction l => // /=.
      rewrite !arrR_cons; eauto.
      rewrite -IHl /=. f_equiv. f_equiv.
        by rewrite raw_int_byte_primR.
    - iDestruct 1 as (l) "(Harray & $ & H)".
      iDestruct "H" as %Hdec.
      iExists _; iSplit => //; eauto with iFrame. clear Hdec.
      rewrite /rawsR arrayR_eq/arrayR_def; iStopProof.
      induction l => // /=.
      rewrite !arrR_cons; eauto.
      rewrite -IHl /=. f_equiv. f_equiv.
        by rewrite raw_int_byte_primR.
  Qed.

  Axiom decode_uint_anyR : forall q sz,
    anyR (Tint sz Unsigned) q -|-
         anyR (Tarray T_uchar (bytesN sz)) q **
         type_ptrR (Tint sz Unsigned).
End with_Σ.
