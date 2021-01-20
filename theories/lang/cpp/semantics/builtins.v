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

(* NOTE (JH): `churn_bits'` and `churn_bits` are used here, and in z_to_bytes.v; we should
     find a better common home.
 *)
(* TODO: using bool_decide would simplify this reasoning. *)
#[local] Ltac churn_bits' :=
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

#[local] Ltac churn_bits :=
  apply Z.bits_inj'=> n ?;
  repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia);
  rewrite !Z.testbit_ones; try lia;
  churn_bits'.

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
    Proof. intros *; rewrite /_get_byte; churn_bits. Qed.

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
    Proof. intros *; rewrite /_set_byte; churn_bits. Qed.

    Lemma _set_byte_shiftl_idx:
      forall (idx idx': nat) shift v,
        idx' <= idx ->
        (shift = 8 * Z.of_nat idx')%Z ->
        (_set_byte v idx ≫ shift)%Z = _set_byte v (idx - idx').
    Proof.
      intros * Hidx Hshift; rewrite /_set_byte; subst; churn_bits.
      f_equal; lia.
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
    Proof. intros * Hidx Hmask; rewrite /_set_byte; subst; churn_bits. Qed.

    Lemma _set_byte_land_useless:
      forall idx mask v,
        (mask = Z.ones 8 ≪ (8 * Z.of_nat idx))%Z ->
        Z.land (_set_byte v idx) mask =
        _set_byte v idx.
    Proof. intros * Hmask; rewrite /_set_byte; subst; churn_bits. Qed.

    Lemma _set_byte_shiftr_big:
      forall (idx: nat) (idx': Z) v,
        (Z.of_nat idx < idx')%Z ->
        (_set_byte v idx ≫ (8 * idx'))%Z = 0.
    Proof. intros * Hidx; rewrite /_set_byte; churn_bits. Qed.

    Lemma _get_0_set_0_eq:
      forall v,
        _get_byte v 0 = _set_byte v 0.
    Proof. intros *; rewrite /_get_byte/_set_byte; churn_bits. Qed.

    Lemma _set_get_0:
      forall v idx,
        _set_byte (_get_byte v 0) idx = _set_byte v idx.
    Proof.
      intros *; rewrite /_get_byte/_set_byte.
      apply Z.bits_inj'=> n ?.
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      repeat (rewrite ?Z.shiftl_spec; try lia).
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      assert (n < 8 * idx \/ 8 * idx <= n) as [Hn | Hn] by lia.
      - rewrite !Z.testbit_neg_r; [reflexivity | lia.. ].
      - rewrite !Z.shiftr_spec; try lia.
        rewrite !Z.testbit_ones; try lia.
        churn_bits'.
    Qed.

    Lemma _get_set_byte_no_overlap:
      forall (v: Z) (idx idx': nat),
        idx <> idx' ->
        _get_byte (_set_byte v idx) idx' = 0.
    Proof. intros * Hidx; rewrite /_get_byte/_set_byte; churn_bits. Qed.

    Lemma _get_set_byte_roundtrip:
      forall (v: Z) (idx: nat),
        _get_byte (_set_byte v idx) idx = _get_byte v 0.
    Proof.
      intros *; rewrite /_get_byte/_set_byte; churn_bits.
      f_equal; lia.
    Qed.

    Lemma _set_get_byte_roundtrip:
      forall (v: Z) (idx: nat),
        _set_byte (_get_byte v idx) idx =
        _get_byte v idx ≪ (8 * idx).
    Proof.
      intros *; rewrite /_get_byte/_set_byte.

      apply Z.bits_inj' => n ?.
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      repeat (rewrite ?Z.shiftl_spec; try lia).
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      assert (n < 8 * idx \/ 8 * idx <= n) as [Hn | Hn] by lia.
      - rewrite !Z.testbit_neg_r; [reflexivity | lia.. ].
      - rewrite !Z.shiftr_spec; try lia.
        rewrite !Z.testbit_ones; try lia.
        churn_bits'.
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

      Lemma bswap128_useless_lor:
        forall v v' idx,
          (idx >= 16)%nat ->
          bswap128 (Z.lor v (_set_byte v' idx)) =
          bswap128 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /bswap128/bswap_/_get_byte/=.
        rewrite !Z.lor_0_l !Z.shiftr_0_r.
        1: f_equal; [ | do 15 (destruct idx; try lia)].
        1: f_equal; [ | do 14 (destruct idx; try lia)].
        1: f_equal; [ | do 13 (destruct idx; try lia)].
        1: f_equal; [ | do 12 (destruct idx; try lia)].
        1: f_equal; [ | do 11 (destruct idx; try lia)].
        1: f_equal; [ | do 10 (destruct idx; try lia)].
        1: f_equal; [ | do 9  (destruct idx; try lia)].
        1: f_equal; [ | do 8  (destruct idx; try lia)].
        1: f_equal; [ | do 7  (destruct idx; try lia)].
        1: f_equal; [ | do 6  (destruct idx; try lia)].
        1: f_equal; [ | do 5  (destruct idx; try lia)].
        1: f_equal; [ | do 4  (destruct idx; try lia)].
        1: f_equal; [ | do 3  (destruct idx; try lia)].
        1: f_equal; [ | do 2  (destruct idx; try lia)].
        1: f_equal; [ | do 1  (destruct idx; try lia)].
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
        intros *.
        rewrite /bswap16/bswap_/=.
        rewrite !Z.lor_0_r !Z.lor_0_l.
        rewrite !_get_byte_lor !_set_byte_lor.
        rewrite !_get_set_byte_roundtrip !_set_get_byte_roundtrip.
        rewrite Z.shiftl_0_r.
        rewrite !_get_set_byte_no_overlap ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l; try lia.
        rewrite !_set_get_0 !_get_0_set_0_eq.
        repeat (rewrite Z.lor_comm; f_equal).
      Qed.

      Lemma bswap32_set_byte_reverse:
        forall x1 x2 x3 x4,
          bswap32 (Z.lor (_set_byte x1 0)
                   (Z.lor (_set_byte x2 1)
                    (Z.lor (_set_byte x3 2)
                     (Z.lor (_set_byte x4 3) 0)))) =
          Z.lor (_set_byte x4 0)
          (Z.lor (_set_byte x3 1)
           (Z.lor (_set_byte x2 2)
            (Z.lor (_set_byte x1 3) 0))).
      Proof.
        intros *.
        rewrite /bswap32/bswap_/=.
        rewrite !Z.lor_0_r !Z.lor_0_l.
        rewrite !_get_byte_lor !_set_byte_lor.
        rewrite !_get_set_byte_roundtrip !_set_get_byte_roundtrip.
        rewrite Z.shiftl_0_r.
        rewrite !_get_set_byte_no_overlap ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l; try lia.
        rewrite !_set_get_0 !_get_0_set_0_eq.
        repeat (rewrite Z.lor_comm; f_equal).
      Qed.

      Lemma bswap64_set_byte_reverse:
        forall x1 x2 x3 x4 x5 x6 x7 x8,
          bswap64 (Z.lor (_set_byte x1 0)
                   (Z.lor (_set_byte x2 1)
                    (Z.lor (_set_byte x3 2)
                     (Z.lor (_set_byte x4 3)
                      (Z.lor (_set_byte x5 4)
                       (Z.lor (_set_byte x6 5)
                        (Z.lor (_set_byte x7 6)
                         (Z.lor (_set_byte x8 7) 0)))))))) =
          Z.lor (_set_byte x8 0)
          (Z.lor (_set_byte x7 1)
           (Z.lor (_set_byte x6 2)
            (Z.lor (_set_byte x5 3)
             (Z.lor (_set_byte x4 4)
              (Z.lor (_set_byte x3 5)
               (Z.lor (_set_byte x2 6)
                (Z.lor (_set_byte x1 7) 0))))))).
      Proof.
        intros *.
        rewrite /bswap64/bswap_/=.
        rewrite !Z.lor_0_r !Z.lor_0_l.
        rewrite !_get_byte_lor !_set_byte_lor.
        rewrite !_get_set_byte_roundtrip !_set_get_byte_roundtrip.
        rewrite Z.shiftl_0_r.
        rewrite !_get_set_byte_no_overlap ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l; try lia.
        rewrite !_set_get_0 !_get_0_set_0_eq.
        repeat (rewrite Z.lor_comm; f_equal).
      Qed.

      Lemma bswap128_set_byte_reverse:
        forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16,
          bswap128 (Z.lor (_set_byte x1 0)
                    (Z.lor (_set_byte x2 1)
                     (Z.lor (_set_byte x3 2)
                      (Z.lor (_set_byte x4 3)
                       (Z.lor (_set_byte x5 4)
                        (Z.lor (_set_byte x6 5)
                         (Z.lor (_set_byte x7 6)
                          (Z.lor (_set_byte x8 7)
                           (Z.lor (_set_byte x9 8)
                            (Z.lor (_set_byte x10 9)
                             (Z.lor (_set_byte x11 10)
                              (Z.lor (_set_byte x12 11)
                               (Z.lor (_set_byte x13 12)
                                (Z.lor (_set_byte x14 13)
                                 (Z.lor (_set_byte x15 14)
                                  (Z.lor (_set_byte x16 15) 0)))))))))))))))) =
          Z.lor (_set_byte x16 0)
           (Z.lor (_set_byte x15 1)
            (Z.lor (_set_byte x14 2)
             (Z.lor (_set_byte x13 3)
              (Z.lor (_set_byte x12 4)
               (Z.lor (_set_byte x11 5)
                (Z.lor (_set_byte x10 6)
                 (Z.lor (_set_byte x9 7)
                  (Z.lor (_set_byte x8 8)
                   (Z.lor (_set_byte x7 9)
                    (Z.lor (_set_byte x6 10)
                     (Z.lor (_set_byte x5 11)
                      (Z.lor (_set_byte x4 12)
                       (Z.lor (_set_byte x3 13)
                        (Z.lor (_set_byte x2 14)
                         (Z.lor (_set_byte x1 15) 0))))))))))))))).
      Proof.
        intros *.
        rewrite /bswap128/bswap_/=.
        rewrite !Z.lor_0_r !Z.lor_0_l.
        rewrite !_get_byte_lor !_set_byte_lor.
        rewrite !_get_set_byte_roundtrip !_set_get_byte_roundtrip.
        rewrite Z.shiftl_0_r.
        rewrite !_get_set_byte_no_overlap ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l; try lia.
        rewrite !_set_get_0 !_get_0_set_0_eq.
        repeat (rewrite Z.lor_comm; f_equal).
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
End Bswap.
