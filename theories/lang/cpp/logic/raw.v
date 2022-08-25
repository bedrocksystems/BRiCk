(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import iris.proofmode.proofmode.
From iris.bi.lib Require Import fractional.

Require Import bedrock.lang.cpp.arith.z_to_bytes.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     arr heap_pred pred.

Require Import bedrock.lang.cpp.heap_notations.

Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** [rawR q rs]: the argument pointer points to [raw_byte] [r] within the C++ abstract machine. *)
  Definition rawR_def (q : Qp) (r : raw_byte) : Rep :=
    as_Rep (fun p => tptsto Tuchar q p (Vraw r)).
  Definition rawR_aux : seal (@rawR_def). Proof. by eexists. Qed.
  Definition rawR := rawR_aux.(unseal).
  Definition rawR_eq : @rawR = _ := rawR_aux.(seal_eq).
  #[global] Arguments rawR q raw : rename.

  Lemma _at_rawR_ptr_congP_transport (p1 p2 : ptr) (q : Qp) (r : raw_byte) :
    ptr_congP σ p1 p2 |-- p1 |-> rawR q r -* p2 |-> rawR q r.
  Proof.
    rewrite rawR_eq/rawR_def !_at_as_Rep.
    iApply tptsto_ptr_congP_transport.
  Qed.

  Lemma _at_rawR_offset_congP_transport (p : ptr) (o1 o2 : offset) (q : Qp) (r : raw_byte) :
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

  Definition rawsR (q : Qp) (rs : list raw_byte) : Rep := arrayR Tuchar (rawR q) rs.

  Lemma _at_rawsR_ptr_congP_transport (p1 p2 : ptr) (q : Qp) (rs : list raw_byte) :
    ptr_congP σ p1 p2 ** p2 |-> arrayR Tu8 (const emp) rs |-- p1 |-> rawsR q rs -* p2 |-> rawsR q rs.
  Proof.
    generalize dependent p2; generalize dependent p1; induction rs;
      iIntros (p1 p2) "[#congP tptrs]"; iAssert (ptr_congP σ p1 p2) as "(% & #tptr1 & #tptr2)"=> //.
    - rewrite /rawsR !arrayR_nil !_at_sep !_at_only_provable !_at_validR.
      iIntros "[_ %]"; iFrame "%"; iApply (type_ptr_valid with "tptr2").
    - rewrite /rawsR !arrayR_cons !_at_sep !_at_type_ptrR !_at_offsetR; fold (rawsR q rs).
      iIntros "[_ [raw raws]]"; iFrame "#"; iSplitL "raw".
      + iApply (_at_rawR_ptr_congP_transport with "congP"); iFrame "∗".
      + destruct rs.
        * rewrite /rawsR !arrayR_nil !_at_sep !_at_only_provable !_at_validR.
          iDestruct "raws" as "[#valid %]"; iFrame "%".
          iApply type_ptr_valid_plus_one; iFrame "#".
        * specialize (IHrs (p1 .[ Tu8 ! 1 ]) (p2 .[ Tu8 ! 1 ])).

          iDestruct (observe (type_ptr Tu8 (p1 .[ Tu8 ! 1 ])) with "raws") as "#tptr1'". 1: {
            rewrite /rawsR arrayR_cons; apply: _.
          }

          iDestruct "tptrs" as "(_ & _ & tptrs)".
          iDestruct (observe (type_ptr Tu8 (p2 .[ Tu8 ! 1 ])) with "tptrs") as "#tptr2'". 1: {
            rewrite /rawsR arrayR_cons; apply: _.
          }

          iApply (IHrs with "[tptrs]"); iFrame "∗".
          unfold ptr_congP, ptr_cong; iFrame "#"; iPureIntro.
          destruct H as [p [o1 [o2 [Ho1 [Ho2 Hoffset_cong]]]]]; subst.
          exists p, (o1 .[ Tu8 ! 1 ]), (o2 .[ Tu8 ! 1 ]).
          rewrite ?offset_ptr_dot; intuition.
          unfold offset_cong in *.
          by rewrite !eval_offset_dot Hoffset_cong.
  Qed.

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

      #[global] Instance rawsR_fractional rs :
        Fractional (λ q, rawsR q rs).
      Proof. apply _. Qed.
      #[global] Instance rawsR_as_fractional q rs :
        AsFractional (rawsR q rs) (λ q, rawsR q rs) q.
      Proof. constructor. done. apply _. Qed.

      Lemma rawsR_observe_frac_valid (q : Qp) rs :
        (0 < length rs) ->
        Observe [| q ≤ 1 |]%Qp (rawsR q rs).
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
