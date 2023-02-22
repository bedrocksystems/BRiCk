(*
 * Copyright (c) 2020-2021,2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import iris.proofmode.proofmode.
From iris.bi.lib Require Import fractional.

Require Import bedrock.lang.cpp.bi.cfractional.
Require Import bedrock.lang.cpp.arith.z_to_bytes.
Require Import bedrock.lang.cpp.arith.builtins.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     arr heap_pred pred.

Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** [rawR q rs]: the argument pointer points to [raw_byte] [r] within the C++ abstract machine. *)
  Definition rawR_def (q : cQp.t) (r : raw_byte) : Rep :=
    as_Rep (fun p => tptsto Tuchar q p (Vraw r)).
  Definition rawR_aux : seal (@rawR_def). Proof. by eexists. Qed.
  Definition rawR := rawR_aux.(unseal).
  Definition rawR_eq : @rawR = _ := rawR_aux.(seal_eq).
  #[global] Arguments rawR q raw : rename.

  Lemma _at_rawR_ptr_congP_transport (p1 p2 : ptr) (q : cQp.t) (r : raw_byte) :
    ptr_congP σ p1 p2 |-- p1 |-> rawR q r -* p2 |-> rawR q r.
  Proof.
    rewrite rawR_eq/rawR_def !_at_as_Rep.
    iApply tptsto_ptr_congP_transport.
  Qed.

  Lemma _at_rawR_offset_congP_transport (p : ptr) (o1 o2 : offset) (q : cQp.t) (r : raw_byte) :
        offset_congP σ o1 o2 ** type_ptr Tu8 (p ,, o2)
    |-- p ,, o1 |-> rawR q r -* p ,, o2 |-> rawR q r.
  Proof.
    iIntros "[%cong #tptr'] raw".
    iDestruct (observe (type_ptr Tu8 (p ,, o1)) with "raw") as "#tptr". 1: {
      rewrite rawR_eq/rawR_def !_at_as_Rep; by apply: _.
    }
    iRevert "raw"; iApply _at_rawR_ptr_congP_transport.
    unfold ptr_congP; iFrame "#"; iPureIntro.
    unfold ptr_cong; exists p, o1, o2; intuition.
  Qed.

  Definition rawsR (q : cQp.t) (rs : list raw_byte) : Rep := arrayR Tuchar (rawR q) rs.

  Section Theory.
    Section primR_Axiom.
      (* TODO: improve our axiomatic support for raw values - including "shattering"
         non-raw values into their constituent raw pieces - to enable deriving
         [primR_to_rawsR].
       *)
      Axiom primR_to_rawsR: forall ty q v,
        primR ty q v -|-
        Exists rs,
          rawsR q rs **
          [| raw_bytes_of_val σ ty v rs |] **
          type_ptrR ty.

      Lemma raw_int_byte_primR : forall q r z,
        (raw_int_byte z = r)%Z ->
        rawR q r -|- primR Tuchar q (Vn z).
      Proof.
        intros * Hz; subst; rewrite primR_to_rawsR; split'.
        - iIntros "HrawR"; iExists [raw_int_byte z].
          rewrite /rawsR arrayR_singleton.
          iDestruct (observe (type_ptrR (Tnum char_bits Unsigned)) with "HrawR")
            as "#Htype_ptrR". {
            rewrite rawR_eq/rawR_def type_ptrR_eq/type_ptrR_def;
              apply as_Rep_observe=> p; apply _.
          }
          iFrame "#∗"; iPureIntro.
          (* TODO: Missing Axioms describing the behavior of raw_bytes_of_val for `uint8` *)
          admit.
        - iIntros "H"; iDestruct "H" as (rs) "(HrawsR & %Hraw_bytes_of_val & Htype_ptrR)".
          (* TODO: Missing Axioms describing the behavior of raw_bytes_of_val for `uint8` *)
          admit.
      Admitted.

      Section decodes.
        (* TODO (JH): Determine if we can axiomatize a more specific property and use it
             to derive this reasoning principle. *)
        Axiom decode_uint_anyR : forall q sz,
          anyR (Tnum sz Unsigned) q -|-
          anyR (Tarray Tuchar (bytesN sz)) q **
          type_ptrR (Tnum sz Unsigned).

        Definition decodes (endianness: endian) (sgn: signed) (l: list N) (z: Z) :=
          List.Forall (fun v => has_type (Vn v) Tu8) l /\
          _Z_from_bytes endianness sgn l = z.

        (* JH: TODO: Deprecate the following stuff *)
        Definition decodes_uint (l : list N) (z : Z) :=
          Unfold decodes (decodes (genv_byte_order σ) Unsigned l z).

        (* JH: TODO: Determine what new axioms we should add here. *)
        Axiom raw_byte_of_int_eq : forall sz x rs,
            raw_bytes_of_val σ (Tnum sz Unsigned) (Vint x) rs <->
            (exists l, decodes_uint l x /\ raw_int_byte <$> l = rs /\
                    length l = bytesNat sz).

        (** TODO: determine whether this is correct with respect to pointers *)
        Lemma decode_uint_primR : forall q sz (x : Z),
          primR (Tnum sz Unsigned) q (Vint x) -|-
          Exists (rs : list raw_byte) (l : list N),
            arrayR Tu8 (fun c => primR Tu8 q (Vint c)) (Z.of_N <$> l) **
            type_ptrR (Tnum sz Unsigned) **
            [| decodes_uint l x |] **
            [| raw_int_byte <$> l = rs |] **
            [| length l = bytesNat sz |].
        Proof.
          move => q sz x.
          rewrite primR_to_rawsR. setoid_rewrite raw_byte_of_int_eq.
          iSplit.
          - iDestruct 1 as (rs) "(Hraw & H & $)".
            iDestruct "H" as %[l [Hdec [Hrs Hlen]]].
            iExists rs, _; iSplit => //. clear Hdec.
            rewrite /rawsR arrayR_eq/arrayR_def. iStopProof.
            (* TODO i need to do induction here because the [Proper] instances are too weak. *)
            clear Hlen.
            generalize dependent rs.
            induction l => rs Hrs // /=; simpl in Hrs.
            + by subst.
            + destruct rs; inversion Hrs; subst; simpl.
              rewrite !arrR_cons; eauto.
              rewrite -IHl /=; [| auto];
              by rewrite raw_int_byte_primR.
          - iDestruct 1 as (rs l) "(Harray & $ & %Hdec & %Hbytes & %Hlen)".
            iExists rs; iSplit => //; eauto with iFrame.
            clear Hlen Hdec; rewrite -{}Hbytes.
            rewrite /rawsR arrayR_eq/arrayR_def; iStopProof.
            induction l => // /=.
            rewrite !arrR_cons; eauto.
            by rewrite -IHl /= raw_int_byte_primR.
        Qed.
      End decodes.
    End primR_Axiom.

    Section rawR.
      #[global] Instance rawR_proper :
        Proper ((=) ==> (=) ==> (⊣⊢)) (@rawR).
      Proof. by intros ??-> ??->. Qed.
      #[global] Instance rawR_mono :
        Proper ((=) ==> (=) ==> (⊢)) (@rawR).
      Proof. by intros ??-> ??->. Qed.

      #[global] Instance rawR_timeless q raw :
        Timeless (rawR q raw).
      Proof. rewrite rawR_eq. apply _. Qed.

      #[global] Instance rawR_cfractional : CFractional1 rawR.
      Proof. rewrite rawR_eq. apply _. Qed.
      #[global] Instance rawR_as_cfractional : AsCFractional1 rawR.
      Proof. solve_as_cfrac. Qed.

      #[global] Instance rawR_observe_frac_valid : CFracValid1 rawR.
      Proof. rewrite rawR_eq. solve_cfrac_valid. Qed.

      #[global] Instance rawR_observe_agree : AgreeCF1 rawR.
      Proof.
        intros. rewrite rawR_eq/rawR_def.
        apply: as_Rep_only_provable_observe_2=> p.
        iIntros "Hptsto1 Hptsto2".
        iPoseProof (tptsto_agree with "Hptsto1 Hptsto2") as "%Hraws"; eauto.
        iModIntro; iPureIntro; by inversion Hraws.
      Qed.
    End rawR.

    Section rawsR.
      #[global] Instance rawsR_proper :
        Proper ((=) ==> (=) ==> (⊣⊢)) (@rawsR).
      Proof. by intros ??-> ??->. Qed.
      #[global] Instance rawsR_mono :
        Proper ((=) ==> (=) ==> (⊢)) (@rawsR).
      Proof. by intros ??-> ??->. Qed.

      #[global] Instance rawsR_timeless q rs :
        Timeless (rawsR q rs).
      Proof. apply _. Qed.

      #[global] Instance rawsR_cfractional : CFractional1 rawsR.
      Proof. apply _. Qed.
      #[global] Instance rawsR_as_fractional : AsCFractional1 rawsR.
      Proof. solve_as_cfrac. Qed.

      Lemma rawsR_observe_frac_valid q rs :
        (0 < length rs) ->
        Observe [| cQp.frac q ≤ 1 |]%Qp (rawsR q rs).
      Proof.
        intros Hlen; rewrite /rawsR; induction rs;
          by [ simpl in Hlen; lia
             | rewrite arrayR_cons; apply _].
      Qed.

      Lemma rawsR_observe_agree q1 q2 rs1 rs2 :
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
    End rawsR.
  End Theory.

End with_Σ.

Module Endian.
  Section with_Σ.
    Context `{Σ : cpp_logic} {σ : genv}.
    Definition to_big_end (sz : bitsize) : Z -> Z :=
      match genv_byte_order σ with
      | Little => bswap sz
      | Big => fun x => x
      end.

    Definition to_little_end (sz : bitsize) : Z -> Z :=
      match genv_byte_order σ with
      | Big => bswap sz
      | Little => fun x => x
      end.

    Definition to_end (endianness: endian) (sz: bitsize) : Z -> Z :=
      match endianness with
      | Big    => to_big_end sz
      | Little => to_little_end sz
      end.

    Definition of_big_end := @to_big_end.
    (** move to builtins.v *)
    Definition of_little_end := @to_little_end.
    (** move to builtins.v *)
    Definition of_end := @to_end.

    (** move to raw.v *)
    Lemma decodes_uint_to_end :
      forall endianness sz l v,
        length l = bytesNat sz ->
        decodes endianness Unsigned l v ->
        decodes_uint l (to_end endianness sz v).
    Proof.
      move=> endianness sz l v Hsz [Hbyte Hdecode].
      rewrite /decodes in Hdecode.
      rewrite /decodes_uint/to_end/to_little_end/to_big_end.
      split; first assumption.
      repeat case_match; eauto;
        rewrite z_to_bytes._Z_from_bytes_eq/z_to_bytes._Z_from_bytes_def;
        rewrite z_to_bytes._Z_from_bytes_eq/z_to_bytes._Z_from_bytes_def in Hdecode;
        [ | replace l with (rev (rev l)) by (apply rev_involutive)];
        erewrite z_to_bytes._Z_from_bytes_unsigned_le_bswap; eauto;
        now rewrite rev_length.
    Qed.

    Lemma decodes_Z_to_bytes_Unsigned:
      forall (sz : bitsize) (n : nat)  (endianness : endian) (z : Z),
        (bytesNat sz = n)%nat ->
        has_type z (Tnum sz Unsigned) ->
        decodes endianness Unsigned (_Z_to_bytes n endianness Unsigned z) z.
    Proof.
      intros * Hsz Hty; subst.
      rewrite /decodes.
      split.
      2: {
        erewrite _Z_from_to_bytes_roundtrip; try reflexivity.
        move: Hty.
        rewrite -has_int_type.
        rewrite/bound/min_val/max_val.
        destruct sz; rewrite/bytesNat; split; lia.
      }
      exact: _Z_to_bytes_has_type.
    Qed.

    (** move to raws.v? if it knows about has_type *)
    Lemma raw_bytes_of_val_raw_int_byte (z : Z) :
      has_type z Tu16 ->
      raw_bytes_of_val σ Tu16 (to_big_end W16 z) (map raw_int_byte (_Z_to_bytes 2 Big Unsigned z)).
    Proof.
      rewrite raw_byte_of_int_eq.
      exists (_Z_to_bytes 2 Big Unsigned z).
      intuition.
      2: by rewrite _Z_to_bytes_length //.
      have -> : to_big_end W16 z = to_end Big W16 z.
      { reflexivity. }
      apply: decodes_uint_to_end.
      { rewrite _Z_to_bytes_length; reflexivity. }
      apply: (decodes_Z_to_bytes_Unsigned W16); try reflexivity.
      assumption.
    Qed.
  End with_Σ.
End Endian.
