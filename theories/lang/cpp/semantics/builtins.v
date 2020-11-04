(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.operator.

Local Open Scope Z_scope.
(* see
 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
 *)

(* Returns one plus the index of the least significant 1-bit of x,
   or if x is zero, returns zero. *)
Definition first_set (sz : bitsize) (n : Z) : Z :=
  let n := trim (bitsN sz) n in
  if Z.eqb n 0 then 0
  else
    (fix get ls : Z :=
       match ls with
       | nil => 64
       | l :: ls =>
         if Z.testbit n l
         then 1 + l
         else get ls
       end)%Z (List.map Z.of_nat (seq 0 (N.to_nat (bitsN sz)))).

(* Returns the number of trailing 0-bits in x, starting at the least
   significant bit position. If x is 0, the result is undefined. *)
Definition trailing_zeros (sz : bitsize) (n : Z) : Z :=
  (fix get ls : Z :=
     match ls with
     | nil => 64
     | l :: ls =>
       if Z.testbit n l
       then l
       else get ls
     end)%Z (List.map Z.of_nat (seq 0 (N.to_nat (bitsN sz)))).

(* Returns the number of leading 0-bits in x, starting at the most significant
   bit position. If x is 0, the result is undefined. *)
Definition leading_zeros (sz : bitsize) (l : Z) : Z :=
  bitsZ sz - Z.log2 (l mod (2^64)).

(* TODO: using bool_decide would simplify this reasoning. *)
#[local] Ltac churn_bits :=
  repeat match goal with
  | |- context[(?l <=? ?r)%Z] =>
    let Hnb := fresh "Hnb" in
    let Hn := fresh "Hn" in
    destruct (l <=? r)%Z eqn:Hnb;
      set (Hn := Hnb);
      [ apply Z.leb_le in Hn
      | apply Z.leb_gt in Hn]
  | |- context[(?l <? ?r)%Z] =>
    let Hnb := fresh "Hnb" in
    let Hn := fresh "Hn" in
    destruct (l <? r)%Z eqn:Hnb;
      set (Hn := Hnb);
      [ apply Z.ltb_lt in Hn
      | apply Z.ltb_ge in Hn]
  end; rewrite ?andb_false_l ?andb_false_r ?andb_true_l ?andb_true_r
               ?orb_false_l ?orb_false_r ?orb_true_l ?orb_true_r ?Z.bits_0 //=;
               try lia.

Section Byte.
  Definition _get_byte (x: Z) (n: nat): Z := Z.land (x ≫ (8 * n)) (Z.ones 8).
  Definition _set_byte (x: Z) (n: nat): Z := (Z.land (Z.ones 8) x) ≪ (8 * n).

  Section Theory.
    Lemma _get_byte_0:
      forall (idx: nat),
        _get_byte 0 idx = 0.
    Proof. intros; by rewrite /_get_byte Z.shiftr_0_l Z.land_0_l. Qed.

    Lemma _set_byte_0:
      forall (idx: nat),
        _set_byte 0 idx = 0.
    Proof. intros; by rewrite /_set_byte Z.shiftl_0_l. Qed.

    #[local] Lemma Z_mul_of_nat_S (z : Z) (n : nat) : (z * S n)%Z = (z + z * n)%Z.
    Proof. lia. Qed.

    Lemma _get_byte_S_idx:
      forall (v: Z) (idx: nat),
        _get_byte v (S idx) = _get_byte (v ≫ 8) idx.
    Proof.
      intros; rewrite /_get_byte.
      by rewrite Z.shiftr_shiftr ?Z_mul_of_nat_S; lia.
    Qed.

    Lemma _get_byte_lor:
      forall (v v': Z) (idx: nat),
        _get_byte (Z.lor v v') idx =
        Z.lor (_get_byte v idx) (_get_byte v' idx).
    Proof.
      move=> v v' idx;
        generalize dependent v;
        generalize dependent v';
        induction idx; intros.
      - rewrite /_get_byte/=.
        cbv [Z.of_nat Z.mul]; rewrite !Z.shiftr_0_r.
        by rewrite -Z.land_lor_distr_l.
      - by rewrite !_get_byte_S_idx Z.shiftr_lor IHidx.
    Qed.

    Lemma _set_byte_S_idx:
      forall (v: Z) (idx: nat),
        _set_byte v (S idx) = ((_set_byte v idx) ≪ 8)%Z.
    Proof.
      intros; rewrite /_set_byte.
      by rewrite Z.shiftl_shiftl ?Z_mul_of_nat_S ?(Z.add_comm 8); lia.
    Qed.

    Lemma _set_byte_lor:
      forall (v v': Z) (idx: nat),
        _set_byte (Z.lor v v') idx =
        Z.lor (_set_byte v idx) (_set_byte v' idx).
    Proof.
      move=> v v' idx;
        generalize dependent v;
        generalize dependent v';
        induction idx; intros.
      - rewrite /_set_byte/=.
        cbv [Z.of_nat Z.mul]; rewrite !Z.shiftl_0_r.
        by rewrite -Z.land_lor_distr_r.
      - by rewrite !_set_byte_S_idx IHidx Z.shiftl_lor.
    Qed.

    Lemma _set_byte_shiftl_idx:
      forall (idx idx': nat) shift v,
        idx' <= idx ->
        (shift = 8 * Z.of_nat idx')%Z ->
        (_set_byte v idx ≫ shift)%Z = _set_byte v (idx - idx').
    Proof.
      induction idx; move=> idx' shift v Hidx Hshift.
      - assert (idx' = 0)%nat by lia; subst.
        by rewrite Z.shiftr_0_r.
      - rewrite _set_byte_S_idx; subst.
        specialize (IHidx (idx' - 1)%nat (8 * Z.of_nat (idx' - 1))%Z v ltac:(lia) eq_refl).
        destruct idx'.
        + by rewrite -minus_n_O Z.shiftr_0_r _set_byte_S_idx.
        + rewrite Z.shiftr_shiftl_r; try lia.
          rewrite Nat.sub_succ Nat.sub_0_r in IHidx.
          rewrite Nat.sub_succ -IHidx.
          repeat f_equal.
          lia.
    Qed.

    Lemma _get_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _get_byte v idx)%Z.
    Proof.
      intros; rewrite /_get_byte/Z.ones.
      apply Z.land_nonneg.
      by right.
    Qed.

    Lemma _set_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _set_byte v idx)%Z.
    Proof.
      intros; rewrite /_set_byte/Z.ones Z.shiftl_nonneg.
      apply Z.land_nonneg.
      by left.
    Qed.

    Lemma _set_byte_land_no_overlap:
      forall (idx idx': nat) mask v,
        idx <> idx' ->
        (mask = Z.ones 8 ≪ (8 * Z.of_nat idx'))%Z ->
        Z.land (_set_byte v idx) mask = 0.
    Proof.
      intros; subst; generalize dependent idx';
        induction idx; move=> idx' Hidx.
      - rewrite /_set_byte.
        apply Z.bits_inj'=> n ?.
        repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
        rewrite Z.bits_0 !Z.testbit_ones; try lia.
        churn_bits.
      - rewrite /_set_byte.
        apply Z.bits_inj'=> n ?.
        repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
        rewrite Z.bits_0 !Z.testbit_ones; try lia.
        churn_bits.
    Qed.

    Lemma _set_byte_land_useless:
      forall idx mask v,
        (mask = Z.ones 8 ≪ (8 * Z.of_nat idx))%Z ->
        Z.land (_set_byte v idx) mask =
        _set_byte v idx.
    Proof.
      intros; subst; induction idx.
      - rewrite /_set_byte.
        apply Z.bits_inj'=> n ?.
        repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
        rewrite !Z.testbit_ones; try lia.
        churn_bits.
        by (replace (n - 8 * Z.of_nat 0)%Z with n by lia).
      - rewrite /_set_byte.
        apply Z.bits_inj'=> n ?.
        repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
        rewrite !Z.testbit_ones; try lia.
        churn_bits.
    Qed.

    Lemma _set_byte_shiftr_big:
      forall (idx: nat) (idx': Z) v,
        Z.of_nat idx < idx' ->
        (_set_byte v idx ≫ (8 * idx'))%Z = 0.
    Proof.
      move=> idx idx' v Hidx; generalize dependent idx';
        induction idx; intros; try lia.
      - rewrite /_set_byte.
        apply Z.bits_inj'=> n ?.
        repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
        rewrite !Z.testbit_ones; try lia.
        churn_bits.
      - rewrite _set_byte_S_idx.
        rewrite Z.shiftr_shiftl_r; try lia.
        specialize (IHidx (idx' - 1) ltac:(lia)).
        by replace (8 * idx' - 8)%Z with (8 * (idx' - 1))%Z by lia.
    Qed.

    Lemma _get_set_byte_roundtrip:
      forall (v: Z) (idx idx': nat),
        idx >= idx' ->
        _get_byte (_set_byte v idx) idx' = _get_byte v (idx - idx').
    Proof.
      move=> v idx idx' Hidx;
        generalize dependent v;
        generalize dependent idx';
        induction idx; intros.
      - assert (idx' = 0)%nat by lia; subst.
        rewrite Nat.sub_diag.
        rewrite /_get_byte/_set_byte/=.
        cbv [Z.of_nat Z.mul];
          rewrite ?Z.shiftr_0_r ?Z.shiftl_0_r;
          try lia.
        by rewrite Z.land_comm Z.land_assoc Z.land_diag Z.land_comm.
      - destruct idx'.
        + rewrite _get_byte_S_idx _set_byte_S_idx -{2}(Nat.sub_0_r idx).
          rewrite -IHidx; try lia.
          f_equal.
          rewrite /_set_byte.
          rewrite !Z.shiftl_land.
          apply Z.bits_inj'=> n ?.
        +

    Lemma _get_set_byte_roundtrip:
      forall (v: Z) (idx: nat),
        _get_byte (_set_byte v idx) idx = _get_byte v 0.
    Proof.
      move=> v idx; generalize dependent v;
        induction idx; intros.
      - rewrite /_get_byte/_set_byte/=.
        cbv [Z.of_nat Z.mul];
          rewrite ?Z.shiftr_0_r ?Z.shiftl_0_r;
          try lia.
        by rewrite Z.land_comm Z.land_assoc Z.land_diag Z.land_comm.
      - rewrite _set_byte_S_idx _get_byte_S_idx
                Z.shiftr_shiftl_r ?Z.sub_diag ?Z.shiftr_0_r;
          try lia; apply IHidx.
    Qed.

    Lemma _set_get_byte_roundtrip:
      forall (v: Z) (idx: nat),
        _set_byte (_get_byte v idx) idx =
        Z.land (Z.ones 8 ≪ (8 * idx)) v.
    Proof.
      rewrite /_get_byte/_set_byte=> v idx //=.
      rewrite !Z.shiftl_land -Z.ldiff_ones_r; try lia.
      apply Z.bits_inj' => n ?.
      rewrite !Z.land_spec Z.ldiff_spec Z.shiftl_spec; try lia.
      rewrite [Z.testbit (Z.ones (8 * idx)) n]Z.testbit_ones_nonneg; try lia.
      destruct (n <? 8 * idx)%Z eqn:Hn;
        rewrite ?andb_false_l ?andb_false_r
                ?andb_true_l ?andb_true_r //.
      - rewrite [Z.testbit (Z.ones 8) _]Z.testbit_neg_r
                ?andb_false_l //.
        apply Z.ltb_lt in Hn; lia.
      - rewrite Z.testbit_ones_nonneg; try lia.
        2: apply Z.ltb_ge in Hn; lia.
        destruct (n - 8 * idx <? 8)%Z eqn:Hn';
          rewrite ?andb_false_l ?andb_false_r
                  ?andb_true_l ?andb_true_r //.
    Qed.
  End Theory.
End Byte.

Section Bswap.
  #[local] Definition bswap_idxs (bytes: nat) :=
    let idxs := seq 0 bytes in
    zip idxs (rev idxs).

  #[local] Definition bswap_ (bytes: nat) (n: Z): Z :=
    fold_left (fun acc '(getIdx, setIdx) =>
                 Z.lor acc (_set_byte (_get_byte n getIdx) setIdx))
              (bswap_idxs bytes)
              0.

  #[local] Definition bswap16  (n: Z): Z := bswap_ 2 n.
  #[local] Definition bswap32  (n: Z): Z := bswap_ 4 n.
  #[local] Definition bswap64  (n: Z): Z := bswap_ 8 n.
  #[local] Definition bswap128 (n: Z): Z := bswap_ 16 n.

  Definition bswap (sz : bitsize) : Z -> Z :=
    match sz with
    | W8 => id
    | W16 => bswap16
    | W32 => bswap32
    | W64 => bswap64
    | W128 => bswap128
    end.

  Section Theory.
    Section useless_lor.
      Arguments Z.of_nat !_ /.
      Arguments Z.opp !_ /.
      Arguments Z.sub !_ !_ /.
      Arguments Z.add !_ !_ /.
      Arguments Z.mul !_ !_ /.
      Arguments Pos.mul !_ !_ /.

      Lemma bswap16_useless_lor:
        forall v v' idx,
          (idx >= 2)%nat ->
          bswap16 (Z.lor v (_set_byte v' idx)) =
          bswap16 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /bswap16/bswap_/_get_byte/=.
        rewrite !Z.lor_0_l !Z.shiftr_0_r.
        1: f_equal; [ | do 1 (destruct idx; try lia)].
        all: rewrite ?_set_byte_S_idx ?Z.shiftr_lor
                     ?[Z.shiftl (Z.shiftl (_set_byte _ _) _) _]Z.shiftl_shiftl
                     ?Z.shiftr_shiftl_l ?Z.land_lor_distr_l
                     ?Z.sub_diag ?Z.shiftl_0_r
                     ?(_set_byte_land_no_overlap idx 0) /=
                     ?Z.shiftl_0_r ?Z.lor_0_r;
          try lia.
      Qed.

      Lemma bswap32_useless_lor:
        forall v v' idx,
          (idx >= 4)%nat ->
          bswap32 (Z.lor v (_set_byte v' idx)) =
          bswap32 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /bswap32/bswap_/_get_byte/=.
        rewrite !Z.lor_0_l !Z.shiftr_0_r.
        1: f_equal; [ | do 3 (destruct idx; try lia)].
        1: f_equal; [ | do 2 (destruct idx; try lia)].
        1: f_equal; [ | do 1 (destruct idx; try lia)].
        all: rewrite ?_set_byte_S_idx ?Z.shiftr_lor
                     ?[Z.shiftl (Z.shiftl (_set_byte _ _) _) _]Z.shiftl_shiftl
                     ?Z.shiftr_shiftl_l ?Z.land_lor_distr_l
                     ?Z.sub_diag ?Z.shiftl_0_r
                     ?(_set_byte_land_no_overlap idx 0) /=
                     ?Z.shiftl_0_r ?Z.lor_0_r;
          try lia.
      Qed.

      Lemma bswap64_useless_lor:
        forall v v' idx,
          (idx >= 8)%nat ->
          bswap64 (Z.lor v (_set_byte v' idx)) =
          bswap64 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /bswap64/bswap_/_get_byte/=.
        rewrite !Z.lor_0_l !Z.shiftr_0_r.
        1: f_equal; [ | do 7 (destruct idx; try lia)].
        1: f_equal; [ | do 6 (destruct idx; try lia)].
        1: f_equal; [ | do 5 (destruct idx; try lia)].
        1: f_equal; [ | do 4 (destruct idx; try lia)].
        1: f_equal; [ | do 3 (destruct idx; try lia)].
        1: f_equal; [ | do 2 (destruct idx; try lia)].
        1: f_equal; [ | do 1 (destruct idx; try lia)].
        all: rewrite ?_set_byte_S_idx ?Z.shiftr_lor
                     ?[Z.shiftl (Z.shiftl (_set_byte _ _) _) _]Z.shiftl_shiftl
                     ?Z.shiftr_shiftl_l ?Z.land_lor_distr_l
                     ?Z.sub_diag ?Z.shiftl_0_r
                     ?(_set_byte_land_no_overlap idx 0) /=
                     ?Z.shiftl_0_r ?Z.lor_0_r;
          try lia.
      Qed.

    End useless_lor.

    Section _set_byte_reverse.
      Lemma bswap16_set_byte_reverse:
        forall x1 x2,
          bswap16 (Z.lor (_set_byte x1 0)
                   (Z.lor (_set_byte x2 1) 0)) =
          Z.lor (_set_byte x2 0)
           (Z.lor (_set_byte x1 1) 0).
      Proof.
        move=> x1 x2.
        rewrite /bswap16/bswap_/=.
        rewrite !Z.lor_0_r !Z.lor_0_l.
        rewrite {1}Z.lor_comm; f_equal.
        - rewrite _get_byte_lor _set_byte_lor.
          Set Nested Proofs Allowed.
          Lemma _get_set_byte_no_overlap:
            forall (v: Z) (idx idx': nat),
              idx <> idx' ->
              _get_byte (_set_byte v idx) idx' = 0.
          Proof. Admitted.
          rewrite _get_set_byte_no_overlap ?_set_byte_0 ?Z.lor_0_l; try lia.

        - rewrite /_get_byte/_set_byte/=.
          cbv [Z.of_nat Z.mul Pos.of_succ_nat Pos.mul]; rewrite !Z.shiftl_0_r.
          rewrite ?Z.shiftl_land. rewrite ?Z.shiftr_land.
          rewrite ?_set_byte_S_idx ?Z.shiftr_lor
                  ?[Z.shiftl (Z.shiftl (_set_byte _ _) _) _]Z.shiftl_shiftl
                  ?[Z.shiftr (Z.shiftl (_set_byte _ _) _) _]Z.shiftr_shiftl_l
                  ?Z.land_lor_distr_l
                  ?Z.sub_diag ?Z.shiftl_0_r
                  ?(_set_byte_land_no_overlap idx 0) /=
                  ?Z.shiftl_0_r ?Z.lor_0_r;
            try lia.

          rewrite Z.shiftr_shiftl_l.


          apply Z.bits_inj' => n ?.
          rewrite ?Z.land_spec ?Z.ldiff_spec ?Z.shiftl_spec; try lia.
          rewrite [Z.testbit (Z.ones (8 * idx)) n]Z.testbit_ones_nonneg; try lia.
          churn_bits.
        -



        rewrite _get_set_byte_roundtrip

        rewrite /bswap16/bswap_/_get_byte/=.
        cbv [Z.of_nat Z.mul Pos.of_succ_nat Pos.mul].
        rewrite !Z.lor_0_r !Z.shiftr_0_r Z.lor_comm.
        f_equal.
        - rewrite ?_set_byte_S_idx ?Z.shiftr_lor
                  ?[Z.shiftl (Z.shiftl (_set_byte _ _) _) _]Z.shiftl_shiftl
                  ?[Z.shiftr (Z.shiftl (_set_byte _ _) _) _]Z.shiftr_shiftl_l
                  ?Z.land_lor_distr_l
                  ?Z.sub_diag ?Z.shiftl_0_r
                  ?(_set_byte_land_no_overlap idx 0) /=
                  ?Z.shiftl_0_r ?Z.lor_0_r;
            try lia.
          rewrite {1}[8]Zred_factor0 _set_byte_shiftr_big; try lia.
          rewrite Z.land_0_l Z.lor_0_l.
          rewrite _set_byte_land_useless;
            [ | cbv [Z.of_nat Z.mul]; by rewrite Z.shiftl_0_r].
          rewrite /_set_byte; cbv [Z.of_nat Z.mul]; rewrite !Z.shiftl_0_r.
        -


        - rewrite Z.shiftr_lor Z.land_lor_distr_l _set_byte_S_idx
                  Z.shiftr_shiftl_l; try lia.
          replace (8 - 8)%Z with 0%Z by lia.
          rewrite Z.shiftl_0_r.
          rewrite (_Z_set_byte_shiftr_big 0 1) ?Z.land_0_l ?Z.lor_0_l; try lia.
          apply _Z_set_byte_land_useless.
          by rewrite Z.shiftl_0_r.
        - rewrite Z.land_lor_distr_l.
          rewrite (_Z_set_byte_land_no_overlap 1 0);
            [
            | by lia
            | by rewrite Z.shiftl_0_r];
            rewrite Z.lor_0_r.
          rewrite _Z_set_byte_land_useless;
            [
            | by rewrite Z.shiftl_0_r].
          by rewrite -_Z_set_byte_S_idx.
      Qed.

    End _set_byte_reverse.

  End Theory.

  Section test.
    Local Definition bytes (ls : list Z) :=
      fold_left (fun a b => a * 256 + b)%Z ls 0%Z.
    Arguments bytes _%Z.

    Local Definition _bswap16_test : bswap W16 (bytes (1::2::nil)%Z) = bytes (2::1::nil)%Z := eq_refl.
    Local Definition _bswap32_test :
      bswap W32 (bytes (1::2::3::4::nil)%Z) = bytes (4::3::2::1::nil)%Z := eq_refl.
    Local Definition _bswap64_test :
      bswap W64 (bytes (1::2::3::4::5::6::7::8::nil)%Z) = bytes (8::7::6::5::4::3::2::1::nil)%Z := eq_refl.
  End test.
End bswap.
