(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License. 
 * See the LICENSE-BedRock file in the repository root for details. 
 *)

Require Import bedrock.lang.prelude.base.
From bedrock.lang.cpp.semantics Require Import builtins operator values.
From bedrock.lang.cpp Require Import ast.

Section FromToBytes.

  (* TODO: using bool_decide would simplify this reasoning. *)
  Local Ltac churn_bits :=
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

    Definition _Z_get_byte (x: Z) (n: nat): Z := Z.land (x ≫ (8 * n)) (Z.ones 8).
    Definition _Z_set_byte (x: Z) (n: nat): Z := (Z.land (Z.ones 8) x) ≪ (8 * n).

    Lemma _Z_get_byte_0:
      forall (idx: nat),
        _Z_get_byte 0 idx = 0.
    Proof. intros; by rewrite /_Z_get_byte Z.shiftr_0_l Z.land_0_l. Qed.

    Lemma _Z_set_byte_0:
      forall (idx: nat),
        _Z_set_byte 0 idx = 0.
    Proof. intros; by rewrite /_Z_set_byte Z.shiftl_0_l. Qed.

    Lemma Z_mul_of_nat_S (z : Z) (n : nat) : (z * S n)%Z = (z + z * n)%Z.
    Proof. lia. Qed.

    Lemma _Z_get_byte_S_idx:
      forall (v: Z) (idx: nat),
        _Z_get_byte v (S idx) = _Z_get_byte (v ≫ 8) idx.
    Proof.
      intros; rewrite /_Z_get_byte.
      by rewrite Z.shiftr_shiftr ?Z_mul_of_nat_S; lia.
    Qed.

    Lemma _Z_set_byte_S_idx:
      forall (v: Z) (idx: nat),
        _Z_set_byte v (S idx) = ((_Z_set_byte v idx) ≪ 8)%Z.
    Proof.
      intros; rewrite /_Z_set_byte.
      by rewrite Z.shiftl_shiftl ?Z_mul_of_nat_S ?(Z.add_comm 8); lia.
    Qed.

    Lemma _Z_set_byte_shiftl_idx:
      forall (idx idx': nat) shift v,
        idx' <= idx ->
        (shift = 8 * Z.of_nat idx')%Z ->
        (_Z_set_byte v idx ≫ shift)%Z = _Z_set_byte v (idx - idx').
    Proof.
      induction idx; move=> idx' shift v Hidx Hshift.
      - assert (idx' = 0) by lia; subst.
        by rewrite Z.shiftr_0_r.
      - rewrite _Z_set_byte_S_idx; subst.
        specialize (IHidx (idx' - 1) (8 * Z.of_nat (idx' - 1))%Z v ltac:(lia) eq_refl).
        destruct idx'.
        + by rewrite -minus_n_O Z.shiftr_0_r _Z_set_byte_S_idx.
        + rewrite Z.shiftr_shiftl_r; try lia.
          rewrite Nat.sub_succ Nat.sub_0_r in IHidx.
          rewrite Nat.sub_succ -IHidx.
          repeat f_equal.
          lia.
    Qed.

    Lemma _Z_get_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _Z_get_byte v idx)%Z.
    Proof.
      intros; rewrite /_Z_get_byte /Z.ones.
      apply Z.land_nonneg.
      by right.
    Qed.

    Lemma _Z_set_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _Z_set_byte v idx)%Z.
    Proof.
      intros; rewrite /_Z_set_byte /Z.ones Z.shiftl_nonneg.
      apply Z.land_nonneg.
      by left.
    Qed.

    Lemma _Z_get_set_byte_roundtrip:
      forall (v: Z) (idx: nat),
        _Z_set_byte (_Z_get_byte v idx) idx =
        Z.land (Z.ones 8 ≪ (8 * idx)) v.
    Proof.
      rewrite /_Z_get_byte /_Z_set_byte=> v idx //=.
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

    Section bswap.

      Lemma _Z_set_byte_land_no_overlap:
        forall (idx idx': nat) mask v,
          idx <> idx' ->
          (mask = Z.ones 8 ≪ (8 * Z.of_nat idx'))%Z ->
          Z.land (_Z_set_byte v idx) mask = 0.
      Proof.
        intros; subst; generalize dependent idx';
          induction idx; move=> idx' Hidx.
        - rewrite /_Z_set_byte.
          apply Z.bits_inj'=> n ?.
          repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
          rewrite Z.bits_0 !Z.testbit_ones; try lia.
          churn_bits.
        - rewrite /_Z_set_byte.
          apply Z.bits_inj'=> n ?.
          repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
          rewrite Z.bits_0 !Z.testbit_ones; try lia.
          churn_bits.
      Qed.

      Lemma _Z_set_byte_land_useless:
        forall idx mask v,
          (mask = Z.ones 8 ≪ (8 * Z.of_nat idx))%Z ->
          Z.land (_Z_set_byte v idx) mask =
          _Z_set_byte v idx.
      Proof.
        intros; subst; induction idx.
        - rewrite /_Z_set_byte.
          apply Z.bits_inj'=> n ?.
          repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
          rewrite !Z.testbit_ones; try lia.
          churn_bits.
          by (replace (n - 8 * Z.of_nat 0)%Z with n by lia).
        - rewrite /_Z_set_byte.
          apply Z.bits_inj'=> n ?.
          repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
          rewrite !Z.testbit_ones; try lia.
          churn_bits.
      Qed.

      Lemma _Z_set_byte_shiftr_big:
        forall (idx idx': nat) v,
          idx < idx' ->
          (_Z_set_byte v idx ≫ (8 * Z.of_nat idx'))%Z = 0.
      Proof.
        move=> idx idx' v Hidx; generalize dependent idx';
          induction idx; intros; try lia.
        - rewrite /_Z_set_byte.
          apply Z.bits_inj'=> n ?.
          repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
          rewrite !Z.testbit_ones; try lia.
          churn_bits.
        - rewrite _Z_set_byte_S_idx.
          rewrite Z.shiftr_shiftl_r; try lia.
          specialize (IHidx (idx' - 1) ltac:(lia)).
          by replace (8 * idx' - 8)%Z with (8 * (idx' - 1)%nat)%Z by lia.
      Qed.

      Lemma bswap16_useless_lor:
        forall v v' idx,
          idx >= 2 ->
          builtins.bswap16 (Z.lor v (_Z_set_byte v' idx)) =
          builtins.bswap16 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /builtins.bswap16.
        rewrite Z.land_lor_distr_l.
        rewrite Z.shiftl_lor.
        rewrite (_Z_set_byte_land_no_overlap idx 0);
          [
          | by lia
          | by (replace (8 * Z.of_nat 0)%Z with 0%Z by lia;
                rewrite Z.shiftl_0_r; reflexivity)];
          rewrite Z.shiftl_0_l Z.lor_0_r.
        rewrite Z.shiftr_lor.
        destruct idx; try lia.
        rewrite _Z_set_byte_S_idx.
        rewrite Z.shiftr_shiftl_l; try lia.
        replace (8 - 8)%Z with 0%Z by lia.
        rewrite Z.shiftl_0_r.
        rewrite Z.land_lor_distr_l.
        rewrite (_Z_set_byte_land_no_overlap idx 0) //;
          [
          | by lia ].
        by rewrite Z.lor_0_r.
      Qed.

      Lemma bswap32_useless_lor:
        forall v v' idx,
          idx >= 4 ->
          builtins.bswap32 (Z.lor v (_Z_set_byte v' idx)) =
          builtins.bswap32 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /builtins.bswap32.
        f_equal.
        - rewrite bswap16_useless_lor; lia.
        - do 2 (destruct idx; try lia).
          rewrite !_Z_set_byte_S_idx Z.shiftr_lor
                  Z.shiftl_shiftl; try lia.
          rewrite Z.shiftr_shiftl_l; try lia.
          rewrite Z.shiftl_0_r.
          rewrite bswap16_useless_lor; lia.
      Qed.

      Lemma bswap64_useless_lor:
        forall v v' idx,
          idx >= 8 ->
          builtins.bswap64 (Z.lor v (_Z_set_byte v' idx)) =
          builtins.bswap64 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /builtins.bswap64.
        f_equal.
        - rewrite bswap32_useless_lor; lia.
        - do 4 (destruct idx; try lia).
          rewrite !_Z_set_byte_S_idx Z.shiftr_lor.
          do 3 (rewrite Z.shiftl_shiftl; try lia).
          rewrite Z.shiftr_shiftl_l; try lia.
          rewrite Z.shiftl_0_r.
          rewrite bswap32_useless_lor; lia.
      Qed.

      Lemma bswap16_set_byte_reverse:
        forall x1 x2,
          builtins.bswap16 (Z.lor (_Z_set_byte x1 0)
                            (Z.lor (_Z_set_byte x2 1) 0)) =
          Z.lor (_Z_set_byte x2 0)
           (Z.lor (_Z_set_byte x1 1) 0).
      Proof.
        move=> x1 x2.
        rewrite /builtins.bswap16.
        rewrite !Z.lor_0_r Z.lor_comm.
        f_equal.
        - rewrite Z.shiftr_lor Z.land_lor_distr_l _Z_set_byte_S_idx
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

      Lemma bswap32_set_byte_reverse:
        forall x1 x2 x3 x4,
          builtins.bswap32 (Z.lor (_Z_set_byte x1 0)
                            (Z.lor (_Z_set_byte x2 1)
                             (Z.lor (_Z_set_byte x3 2)
                              (Z.lor (_Z_set_byte x4 3) 0)))) =
          Z.lor (_Z_set_byte x4 0)
          (Z.lor (_Z_set_byte x3 1)
           (Z.lor (_Z_set_byte x2 2)
            (Z.lor (_Z_set_byte x1 3) 0))).
      Proof.
        move=> x1 x2 x3 x4.
        rewrite /builtins.bswap32.
        replace (builtins.bswap16
                   (Z.lor (_Z_set_byte x1 0)
                    (Z.lor (_Z_set_byte x2 1)
                     (Z.lor (_Z_set_byte x3 2)
                      (Z.lor (_Z_set_byte x4 3) 0)))) ≪ 16)%Z
          with (builtins.bswap16
                  (Z.lor (_Z_set_byte x1 0)
                   (Z.lor (_Z_set_byte x2 1) 0)) ≪ 16)%Z. 2: {
          f_equal.
          rewrite !Z.lor_assoc !Z.lor_0_r.
          rewrite (bswap16_useless_lor _ x4 3); try lia.
          rewrite (bswap16_useless_lor _ x3 2); lia.
        }

        replace (builtins.bswap16
                   (Z.lor (_Z_set_byte x1 0)
                    (Z.lor (_Z_set_byte x2 1)
                     (Z.lor (_Z_set_byte x3 2)
                      (Z.lor (_Z_set_byte x4 3) 0))) ≫ 16))
          with (builtins.bswap16
                  (Z.lor (_Z_set_byte x3 2)
                   (Z.lor (_Z_set_byte x4 3) 0) ≫ 16)). 2: {
          rewrite !Z.lor_0_r !Z.shiftr_lor.
          rewrite (_Z_set_byte_shiftr_big 0 2 x1); try lia.
          rewrite (_Z_set_byte_shiftr_big 1 2 x2); try lia.
          by rewrite !Z.lor_0_l.
        }

        rewrite !Z.shiftr_lor.
        rewrite (_Z_set_byte_shiftl_idx 2 2 16 _ ltac:(lia) ltac:(lia));
          change (2 - 2) with 0%nat.
        rewrite (_Z_set_byte_shiftl_idx 3 2 16 _ ltac:(lia) ltac:(lia));
          change (3 - 2) with 1%nat.
        rewrite !bswap16_set_byte_reverse.
        rewrite !Z.lor_0_r !Z.shiftl_lor.
        replace 16%Z with (8 + 8)%Z by lia.
        rewrite -!Z.shiftl_shiftl; try lia.
        rewrite -!_Z_set_byte_S_idx.
        rewrite Z.lor_comm.
        by rewrite !Z.lor_assoc.
      Qed.

      Lemma bswap64_set_byte_reverse:
        forall x1 x2 x3 x4 x5 x6 x7 x8,
          builtins.bswap64 (Z.lor (_Z_set_byte x1 0)
                            (Z.lor (_Z_set_byte x2 1)
                             (Z.lor (_Z_set_byte x3 2)
                              (Z.lor (_Z_set_byte x4 3)
                               (Z.lor (_Z_set_byte x5 4)
                                (Z.lor (_Z_set_byte x6 5)
                                 (Z.lor (_Z_set_byte x7 6)
                                  (Z.lor (_Z_set_byte x8 7) 0)))))))) =
          Z.lor (_Z_set_byte x8 0)
          (Z.lor (_Z_set_byte x7 1)
           (Z.lor (_Z_set_byte x6 2)
            (Z.lor (_Z_set_byte x5 3)
             (Z.lor (_Z_set_byte x4 4)
              (Z.lor (_Z_set_byte x3 5)
               (Z.lor (_Z_set_byte x2 6)
                (Z.lor (_Z_set_byte x1 7) 0))))))).
      Proof.
        move=> x1 x2 x3 x4 x5 x6 x7 x8.
        rewrite /builtins.bswap64.
        replace (builtins.bswap32
                   (Z.lor (_Z_set_byte x1 0)
                    (Z.lor (_Z_set_byte x2 1)
                     (Z.lor (_Z_set_byte x3 2)
                      (Z.lor (_Z_set_byte x4 3)
                       (Z.lor (_Z_set_byte x5 4)
                        (Z.lor (_Z_set_byte x6 5)
                         (Z.lor (_Z_set_byte x7 6)
                          (Z.lor (_Z_set_byte x8 7) 0)))))))) ≪ 32)%Z
          with (builtins.bswap32
                  (Z.lor (_Z_set_byte x1 0)
                   (Z.lor (_Z_set_byte x2 1)
                    (Z.lor (_Z_set_byte x3 2)
                     (Z.lor (_Z_set_byte x4 3) 0)))) ≪ 32)%Z. 2: {
          f_equal.
          rewrite !Z.lor_assoc !Z.lor_0_r.
          rewrite (bswap32_useless_lor _ x8 7); try lia.
          rewrite (bswap32_useless_lor _ x7 6); try lia.
          rewrite (bswap32_useless_lor _ x6 5); try lia.
          rewrite (bswap32_useless_lor _ x5 4); by lia.
        }

        replace (builtins.bswap32
                   (Z.lor (_Z_set_byte x1 0)
                    (Z.lor (_Z_set_byte x2 1)
                     (Z.lor (_Z_set_byte x3 2)
                      (Z.lor (_Z_set_byte x4 3)
                       (Z.lor (_Z_set_byte x5 4)
                        (Z.lor (_Z_set_byte x6 5)
                         (Z.lor (_Z_set_byte x7 6)
                          (Z.lor (_Z_set_byte x8 7) 0))))))) ≫ 32))%Z
          with (builtins.bswap32
                  (Z.lor (_Z_set_byte x5 4)
                   (Z.lor (_Z_set_byte x6 5)
                    (Z.lor (_Z_set_byte x7 6)
                     (Z.lor (_Z_set_byte x8 7) 0))) ≫ 32))%Z. 2: {
          rewrite !Z.lor_0_r !Z.shiftr_lor.
          replace 32%Z with (8 * 4)%Z by lia.
          rewrite (_Z_set_byte_shiftr_big 0 4 x1); try lia.
          rewrite (_Z_set_byte_shiftr_big 1 4 x2); try lia.
          rewrite (_Z_set_byte_shiftr_big 2 4 x3); try lia.
          rewrite (_Z_set_byte_shiftr_big 3 4 x4); try lia.
          by rewrite !Z.lor_0_l.
        }

        rewrite !Z.shiftr_lor.
        rewrite (_Z_set_byte_shiftl_idx 4 4 32 _ ltac:(lia) ltac:(lia));
          replace (4 - 4) with 0%nat by lia.
        rewrite (_Z_set_byte_shiftl_idx 5 4 32 _ ltac:(lia) ltac:(lia));
          replace (5 - 4) with 1%nat by lia.
        rewrite (_Z_set_byte_shiftl_idx 6 4 32 _ ltac:(lia) ltac:(lia));
          replace (6 - 4) with 2%nat by lia.
        rewrite (_Z_set_byte_shiftl_idx 7 4 32 _ ltac:(lia) ltac:(lia));
          replace (7 - 4) with 3%nat by lia.
        rewrite !bswap32_set_byte_reverse.
        rewrite !Z.lor_0_r !Z.shiftl_lor.
        replace 32%Z with (8 + (8 + (8 + 8)))%Z by lia.
        rewrite -!Z.shiftl_shiftl; try lia.
        rewrite -!_Z_set_byte_S_idx.
        rewrite Z.lor_comm.
        by rewrite !Z.lor_assoc.
      Qed.

      Lemma bswap128_set_byte_reverse:
        forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16,
          builtins.bswap128 (Z.lor (_Z_set_byte x1 0)
                             (Z.lor (_Z_set_byte x2 1)
                              (Z.lor (_Z_set_byte x3 2)
                               (Z.lor (_Z_set_byte x4 3)
                                (Z.lor (_Z_set_byte x5 4)
                                 (Z.lor (_Z_set_byte x6 5)
                                  (Z.lor (_Z_set_byte x7 6)
                                   (Z.lor (_Z_set_byte x8 7)
                                    (Z.lor (_Z_set_byte x9 8)
                                     (Z.lor (_Z_set_byte x10 9)
                                      (Z.lor (_Z_set_byte x11 10)
                                       (Z.lor (_Z_set_byte x12 11)
                                        (Z.lor (_Z_set_byte x13 12)
                                         (Z.lor (_Z_set_byte x14 13)
                                          (Z.lor (_Z_set_byte x15 14)
                                           (Z.lor (_Z_set_byte x16 15) 0)))))))))))))))) =
          Z.lor (_Z_set_byte x16 0)
           (Z.lor (_Z_set_byte x15 1)
            (Z.lor (_Z_set_byte x14 2)
             (Z.lor (_Z_set_byte x13 3)
              (Z.lor (_Z_set_byte x12 4)
               (Z.lor (_Z_set_byte x11 5)
                (Z.lor (_Z_set_byte x10 6)
                 (Z.lor (_Z_set_byte x9 7)
                  (Z.lor (_Z_set_byte x8 8)
                   (Z.lor (_Z_set_byte x7 9)
                    (Z.lor (_Z_set_byte x6 10)
                     (Z.lor (_Z_set_byte x5 11)
                      (Z.lor (_Z_set_byte x4 12)
                       (Z.lor (_Z_set_byte x3 13)
                        (Z.lor (_Z_set_byte x2 14)
                         (Z.lor (_Z_set_byte x1 15) 0))))))))))))))).
      Proof.
        move=> x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
        rewrite /builtins.bswap128.

        replace (builtins.bswap64
                   (Z.lor (_Z_set_byte x1 0)
                    (Z.lor (_Z_set_byte x2 1)
                     (Z.lor (_Z_set_byte x3 2)
                      (Z.lor (_Z_set_byte x4 3)
                       (Z.lor (_Z_set_byte x5 4)
                        (Z.lor (_Z_set_byte x6 5)
                         (Z.lor (_Z_set_byte x7 6)
                          (Z.lor (_Z_set_byte x8 7)
                           (Z.lor (_Z_set_byte x9 8)
                            (Z.lor (_Z_set_byte x10 9)
                             (Z.lor (_Z_set_byte x11 10)
                              (Z.lor (_Z_set_byte x12 11)
                               (Z.lor (_Z_set_byte x13 12)
                                (Z.lor (_Z_set_byte x14 13)
                                 (Z.lor (_Z_set_byte x15 14)
                                  (Z.lor (_Z_set_byte x16 15) 0)))))))))))))))) ≪ 64)%Z
          with (builtins.bswap64
                  (Z.lor (_Z_set_byte x1 0)
                   (Z.lor (_Z_set_byte x2 1)
                    (Z.lor (_Z_set_byte x3 2)
                     (Z.lor (_Z_set_byte x4 3)
                      (Z.lor (_Z_set_byte x5 4)
                       (Z.lor (_Z_set_byte x6 5)
                        (Z.lor (_Z_set_byte x7 6)
                         (Z.lor (_Z_set_byte x8 7)  0)))))))) ≪ 64)%Z. 2: {
          f_equal.
          rewrite !Z.lor_assoc !Z.lor_0_r.
          rewrite (bswap64_useless_lor _ x16 15); try lia.
          rewrite (bswap64_useless_lor _ x15 14); try lia.
          rewrite (bswap64_useless_lor _ x14 13); try lia.
          rewrite (bswap64_useless_lor _ x13 12); try lia.
          rewrite (bswap64_useless_lor _ x12 11); try lia.
          rewrite (bswap64_useless_lor _ x11 10); try lia.
          rewrite (bswap64_useless_lor _ x10 9); try lia.
          rewrite (bswap64_useless_lor _ x9 8); lia.
        }

        replace (builtins.bswap64
                   (Z.lor (_Z_set_byte x1 0)
                    (Z.lor (_Z_set_byte x2 1)
                     (Z.lor (_Z_set_byte x3 2)
                      (Z.lor (_Z_set_byte x4 3)
                       (Z.lor (_Z_set_byte x5 4)
                        (Z.lor (_Z_set_byte x6 5)
                         (Z.lor (_Z_set_byte x7 6)
                          (Z.lor (_Z_set_byte x8 7)
                           (Z.lor (_Z_set_byte x9 8)
                            (Z.lor (_Z_set_byte x10 9)
                             (Z.lor (_Z_set_byte x11 10)
                              (Z.lor (_Z_set_byte x12 11)
                               (Z.lor (_Z_set_byte x13 12)
                                (Z.lor (_Z_set_byte x14 13)
                                 (Z.lor (_Z_set_byte x15 14)
                                  (Z.lor (_Z_set_byte x16 15) 0))))))))))))))) ≫ 64))%Z
          with (builtins.bswap64
                  (Z.lor (_Z_set_byte x9 8)
                   (Z.lor (_Z_set_byte x10 9)
                    (Z.lor (_Z_set_byte x11 10)
                     (Z.lor (_Z_set_byte x12 11)
                      (Z.lor (_Z_set_byte x13 12)
                       (Z.lor (_Z_set_byte x14 13)
                        (Z.lor (_Z_set_byte x15 14)
                         (Z.lor (_Z_set_byte x16 15) 0))))))) ≫ 64))%Z. 2: {
          rewrite !Z.lor_0_r !Z.shiftr_lor.
          replace 64%Z with (8 * 8)%Z by lia.
          rewrite (_Z_set_byte_shiftr_big 0 8 x1); try lia.
          rewrite (_Z_set_byte_shiftr_big 1 8 x2); try lia.
          rewrite (_Z_set_byte_shiftr_big 2 8 x3); try lia.
          rewrite (_Z_set_byte_shiftr_big 3 8 x4); try lia.
          rewrite (_Z_set_byte_shiftr_big 4 8 x5); try lia.
          rewrite (_Z_set_byte_shiftr_big 5 8 x6); try lia.
          rewrite (_Z_set_byte_shiftr_big 6 8 x7); try lia.
          rewrite (_Z_set_byte_shiftr_big 7 8 x8); try lia.
          by rewrite !Z.lor_0_l.
        }

        rewrite !Z.shiftr_lor.
        rewrite (_Z_set_byte_shiftl_idx 8 8 64 _ ltac:(lia) ltac:(lia)).
        rewrite (_Z_set_byte_shiftl_idx 9 8 64 _ ltac:(lia) ltac:(lia)).
        rewrite (_Z_set_byte_shiftl_idx 10 8 64 _ ltac:(lia) ltac:(lia)).
        rewrite (_Z_set_byte_shiftl_idx 11 8 64 _ ltac:(lia) ltac:(lia)).
        rewrite (_Z_set_byte_shiftl_idx 12 8 64 _ ltac:(lia) ltac:(lia)).
        rewrite (_Z_set_byte_shiftl_idx 13 8 64 _ ltac:(lia) ltac:(lia)).
        rewrite (_Z_set_byte_shiftl_idx 14 8 64 _ ltac:(lia) ltac:(lia)).
        rewrite (_Z_set_byte_shiftl_idx 15 8 64 _ ltac:(lia) ltac:(lia)).
        cbv [minus].
        rewrite !bswap64_set_byte_reverse.
        rewrite !Z.lor_0_r !Z.shiftl_lor.
        change 64%Z with (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))%Z.
        have ?: (0 <= 8)%Z by lia.
        rewrite -!Z.shiftl_shiftl; try assumption.
        rewrite -!_Z_set_byte_S_idx.
        rewrite Z.lor_comm.
        by rewrite !Z.lor_assoc.
      Qed.
    End bswap.

  End Byte.

  Section ExtraFacts.

    Lemma repeat_cons_app:
      forall (A: Type) (a: A) (cnt: nat),
        (a :: repeat a cnt) = repeat a cnt ++ [a].
    Proof.
      induction cnt => //=.
      by rewrite IHcnt.
    Qed.

    Lemma rev_repeat:
      forall (A: Type) (a: A) (cnt: nat),
        rev (repeat a cnt) = repeat a cnt.
    Proof.
      induction cnt => //=.
      by rewrite IHcnt repeat_cons_app.
    Qed.

    Lemma Z_shiftr_small:
      forall v e,
        (0 <= e)%Z ->
        (0 <= v)%Z ->
        (v < 2 ^ e)%Z ->
        (v ≫ e = 0)%Z.
    Proof.
      intros; rewrite Z.shiftr_div_pow2; try lia.
      rewrite Z.div_small; lia.
    Qed.

    Lemma Z_pow2_trans_nat_l:
      forall v (a b: nat),
        (v < 2 ^ (8 * b))%Z ->
        (v < 2 ^ (8 * (a + b)%nat))%Z.
    Proof.
      intros; destruct a.
      - by replace (8 * (0%nat + b))%Z with (8 * b)%Z by lia.
      - eapply Z.lt_trans; eauto; apply Z.pow_lt_mono_r; lia.
    Qed.

    Lemma Z_pow2_trans_nat_r:
      forall v (a b: nat),
        (v < 2 ^ (8 * a))%Z ->
        (v < 2 ^ (8 * (a + b)%nat))%Z.
    Proof.
      intros; destruct b.
      - by rewrite -plus_n_O.
      - eapply Z.lt_trans; eauto; apply Z.pow_lt_mono_r; lia.
    Qed.

    Lemma Z_land_ldiff_no_overlap (mask offset v: Z) :
        (0 < mask)%Z ->
        (0 <= offset)%Z ->
        (0 <= v)%Z ->
        Z.land (mask ≪ offset) (Z.ldiff v (Z.ones offset)) = Z.land (mask ≪ offset) v.
    Proof.
    (* Intuition: the ldiff is going to remove the lowest
         (idx+cnt) bytes, but the `255 ≪ (8 * (idx+cnt))`
         mask doesn't overlap with any of those bits
         so it is effectively a no-op.
     *)
      intros.
      apply Z.bits_inj' => n ?.
      rewrite !Z.land_spec Z.ldiff_spec Z.shiftl_spec // Z.testbit_ones_nonneg; try lia.
      destruct (n <? offset)%Z eqn:Hn => /=; rewrite ?andb_true_r //.
      move: Hn => /Z.ltb_lt?.
      rewrite !andb_false_r Z.testbit_neg_r //. lia.
    Qed.

    Lemma Z_land_ldiff_upper_byte (offset v: Z) :
        (0 <= offset)%Z ->
        (2^(8*offset) <= v)%Z ->
        (v < 2^(8*Z.succ offset))%Z ->
        Z.ldiff v (Z.ones (8 * offset)) = Z.land (255 ≪ (8 * offset)) v.
    Proof.
    (* Intuition: since `v < 2^(8*(idx+S cnt))`, we know
         that there aren't going to be any bits
         beyond the `255 ≪ (8 * (idx+cnt))` mask
         which will be introduced by the change to ldiff.
     *)
      intros.
      apply Z.bits_inj' => n ?.
      rewrite !Z.land_spec Z.ldiff_spec Z.shiftl_spec // Z.testbit_ones_nonneg; try lia.
      destruct (n <? 8*offset)%Z eqn:Hn => //=; rewrite ?andb_true_r ?andb_false_r //.
      - apply Z.ltb_lt in Hn; rewrite Z.testbit_neg_r ?andb_false_l //=; lia.
      - apply Z.ltb_ge in Hn.
        replace (8 * Z.succ offset)%Z with (8 + (8 * offset))%Z in H1 by lia.
        change (255)%Z with (Z.ones 8).
        destruct (8 + (8 * offset) <? n)%Z eqn:Hn' => //=.
        + rewrite Z.bits_above_log2 ?andb_false_r //.
          * apply Z.le_trans with (m := (2^(8*offset))%Z); try apply Z.pow_nonneg; lia.
          * apply Z.log2_lt_pow2.
            -- eapply Z.lt_le_trans; eauto; apply Z.pow_pos_nonneg; lia.
            -- eapply Z.lt_trans; eauto.
               apply Z.ltb_lt in Hn'.
               apply Z.pow_lt_mono_r; try lia.
        + apply Z.ltb_ge in Hn'.
          destruct (8 + (8 * offset) =? n)%Z eqn:Hn'' => //=.
          * apply Z.eqb_eq in Hn''; subst.
            rewrite Z.bits_above_log2 ?andb_false_l ?andb_false_r //.
            -- apply Z.le_trans with (m := (2^(8*offset))%Z);
                 eauto; apply Z.pow_nonneg; lia.
            -- apply Z.log2_lt_pow2; try lia.
               eapply Z.lt_le_trans; eauto; apply Z.pow_pos_nonneg; lia.
          * apply Z.eqb_neq in Hn''.
            assert (n < 8 + 8 * offset)%Z as Hn''' by lia.
            rewrite Z.ones_spec_low ?andb_true_l //; lia.
    Qed.

    Lemma Z_ldiff_split:
      forall (cnt idx: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*(idx+S cnt)))%Z ->
        Z.ldiff v (Z.ones (8 * idx)) =
        Z.lor (Z.land (Z.ones (8 * cnt) ≪ (8 * idx)) v)
              (Z.land (Z.ones 8 ≪ (8 * (idx + cnt)%nat)) v).
    Proof.
      intros cnt idx v Hlower Hupper.
      assert (v = 0 \/ 0 < v)%Z as [Hlower' | Hlower'] by lia;
        [subst; by rewrite !Z.land_0_r Z.lor_diag Z.ldiff_0_l | clear Hlower].
      apply Z.bits_inj'=> n ?.
      rewrite Z.lor_spec Z.ldiff_spec !Z.land_spec !Z.shiftl_spec; try lia.
      rewrite !Z.testbit_ones; try lia.
      churn_bits.
      apply Z.bits_above_log2; try lia.
      assert (8 * (idx+S cnt)%nat <= n)%Z by lia.
      eapply Z.lt_le_trans; eauto.
      apply Z.log2_lt_pow2; try lia.
      (* XXX No more needed since Coq 8.12. *)
      all: by replace (8 * (idx+S cnt)%nat)%Z
        with (8 * (idx+S cnt))%Z by lia.
    Qed.

  End ExtraFacts.

  Section ToBytes_internal.

    Definition _Z_to_bytes_unsigned_le' (idx: nat) (cnt: nat) (v: Z): list N :=
      map (Z.to_N ∘ _Z_get_byte v) $ seq idx cnt.

    Definition _Z_to_bytes_unsigned_le (cnt: nat) (v: Z): list N :=
      _Z_to_bytes_unsigned_le' 0 cnt v.

    Definition _Z_to_bytes_le (cnt: nat) (sgn: signed) (v: Z): list N :=
      _Z_to_bytes_unsigned_le
        cnt (match sgn with
             | Signed   => to_unsigned_bits (8 * N.of_nat cnt) v
             | Unsigned => v
             end).

    (* NOTE: This will be sealed once we finish the proofs for this section. *)
    Definition _Z_to_bytes_def (cnt: nat) (endianness: endian) (sgn: signed) (v: Z): list N :=
      let little := _Z_to_bytes_le cnt sgn v in
      match endianness with
      | Little => little
      | Big => List.rev little
      end.

  End ToBytes_internal.

  Section ToBytesFacts_internal.

    Lemma _Z_to_bytes_unsigned_le'_length:
      forall idx cnt v,
        length (_Z_to_bytes_unsigned_le' idx cnt v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_unsigned_le' => idx cnt v //=;
        by rewrite map_length seq_length.
    Qed.

    Definition _Z_to_bytes_unsigned_le_length:
      forall cnt v,
        length (_Z_to_bytes_unsigned_le cnt v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_unsigned_le => * //=;
        by apply _Z_to_bytes_unsigned_le'_length.
    Qed.

    Lemma _Z_to_bytes_le_length:
      forall cnt sgn v,
        length (_Z_to_bytes_le cnt sgn v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_le => * //=;
        by apply _Z_to_bytes_unsigned_le_length.
    Qed.

    Lemma _Z_to_bytes_def_length:
      forall cnt endianness sgn v,
        length (_Z_to_bytes_def cnt endianness sgn v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_def => cnt [ | ] sgn v //=;
        try rewrite rev_length;
        by apply _Z_to_bytes_le_length.
    Qed.

    Lemma _Z_to_bytes_unsigned_le'_0_bytes:
      forall (idx: nat) (v: Z),
        _Z_to_bytes_unsigned_le' idx 0 v = [].
    Proof. done. Qed.

    Lemma _Z_to_bytes_unsigned_le_0_bytes:
      forall (v: Z),
        _Z_to_bytes_unsigned_le 0 v = [].
    Proof. apply (_Z_to_bytes_unsigned_le'_0_bytes 0). Qed.

    Lemma _Z_to_bytes_le_0_bytes:
      forall sgn (v: Z),
        _Z_to_bytes_le 0 sgn v = [].
    Proof.
      move=> [ | ] v; rewrite /_Z_to_bytes_le;
        [rewrite N.mul_0_r trim_0_l | ];
        apply _Z_to_bytes_unsigned_le_0_bytes.
    Qed.

    Lemma _Z_to_bytes_def_0_bytes:
      forall endianness sgn (v: Z),
        _Z_to_bytes_def 0 endianness sgn v = [].
    Proof.
      move=> [ | ] sgn v;
        by rewrite /_Z_to_bytes_def _Z_to_bytes_le_0_bytes //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le'_0_value:
      forall (idx cnt: nat),
        _Z_to_bytes_unsigned_le' idx cnt 0 = repeat 0%N cnt.
    Proof.
      induction cnt => //=.
      rewrite /_Z_to_bytes_unsigned_le'.
      rewrite seq_S_end_app map_app repeat_cons_app //=.
      rewrite _Z_get_byte_0; f_equal=> //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le_0_value:
      forall (cnt: nat),
        _Z_to_bytes_unsigned_le cnt 0 = repeat 0%N cnt.
    Proof. apply _Z_to_bytes_unsigned_le'_0_value. Qed.

    Lemma _Z_to_bytes_le_0_value:
      forall (cnt: nat) sgn,
        _Z_to_bytes_le cnt sgn 0 = repeat 0%N cnt.
    Proof.
      move=> cnt [ | ]; rewrite /_Z_to_bytes_le;
        [rewrite trim_0_r | ];
        apply _Z_to_bytes_unsigned_le_0_value.
    Qed.

    Lemma _Z_to_bytes_def_0_value:
      forall sgn endianness (cnt: nat),
        _Z_to_bytes_def cnt endianness sgn 0 = repeat 0%N cnt.
    Proof.
      move=> sgn [ | ] cnt;
        rewrite /_Z_to_bytes_def
                _Z_to_bytes_le_0_value //=;
        by rewrite rev_repeat.
    Qed.

    Lemma _Z_to_bytes_unsigned_le'_S_cnt:
      forall (idx cnt: nat) (v: Z),
        _Z_to_bytes_unsigned_le' idx (S cnt) v =
        _Z_to_bytes_unsigned_le' idx cnt v ++
        _Z_to_bytes_unsigned_le' (idx+cnt) 1 v.
    Proof.
      intros; generalize dependent idx;
        induction cnt; intros=> //=.
      - by rewrite Nat.add_0_r.
      - rewrite /_Z_to_bytes_unsigned_le'.
        rewrite seq_S_end_app map_app //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le_S_cnt:
      forall (cnt: nat) (v: Z),
        _Z_to_bytes_unsigned_le (S cnt) v =
        _Z_to_bytes_unsigned_le' 0 cnt v ++
        _Z_to_bytes_unsigned_le' cnt 1 v.
    Proof. apply _Z_to_bytes_unsigned_le'_S_cnt. Qed.

    Lemma _Z_to_bytes_unsigned_le'_small:
      forall (idx cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*idx))%Z ->
        _Z_to_bytes_unsigned_le' idx cnt v =
        repeat 0%N cnt.
    Proof.
      intros; generalize dependent idx;
        induction cnt ; intros=> //=.
      rewrite _Z_to_bytes_unsigned_le'_S_cnt
              /_Z_to_bytes_unsigned_le'
              repeat_cons_app //=; f_equal.
      - erewrite <- IHcnt; eauto.
      - rewrite /_Z_get_byte Z_shiftr_small; try lia;
          [ rewrite Z.land_0_l
          | apply Z_pow2_trans_nat_r]=> //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le'_shrink_cnt:
      forall (idx cnt cnt': nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        cnt < cnt' ->
        _Z_to_bytes_unsigned_le' idx cnt' v =
        _Z_to_bytes_unsigned_le' idx cnt v ++ repeat 0%N (cnt' - cnt).
    Proof.
      intros; generalize dependent idx; generalize dependent cnt;
        induction cnt'; intros=> //=; [lia | ].
      replace (S cnt' - cnt) with (S (cnt' - cnt)) by lia; simpl.
      assert (cnt = cnt' \/ cnt < cnt') as [Hcnt | Hcnt] by lia.
      - subst; rewrite _Z_to_bytes_unsigned_le'_S_cnt; f_equal.
        rewrite Nat.sub_diag /_Z_to_bytes_unsigned_le' //=.
        rewrite /_Z_get_byte Z_shiftr_small; try lia;
          [ rewrite Z.land_0_l
          | apply Z_pow2_trans_nat_l]=> //=.
      - rewrite repeat_cons_app app_assoc.
        rewrite -IHcnt'; try lia.
        rewrite _Z_to_bytes_unsigned_le'_S_cnt //=; f_equal.
        rewrite /_Z_to_bytes_unsigned_le' //=.
        rewrite /_Z_get_byte Z_shiftr_small; try lia;
          [ rewrite Z.land_0_l
          | eapply Z.lt_trans; eauto; apply Z.pow_lt_mono_r; lia]=> //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le_shrink_cnt:
      forall (cnt cnt': nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        cnt < cnt' ->
        _Z_to_bytes_unsigned_le cnt' v =
        _Z_to_bytes_unsigned_le cnt v ++ repeat 0%N (cnt' - cnt).
    Proof. apply _Z_to_bytes_unsigned_le'_shrink_cnt. Qed.

    Lemma _Z_to_bytes_unsigned_le'_S_idx:
      forall (idx cnt: nat) (v: Z),
        (0 <= v)%Z ->
        _Z_to_bytes_unsigned_le' (S idx) cnt v =
        _Z_to_bytes_unsigned_le' idx cnt (v ≫ 8).
    Proof.
      intros idx cnt v Hlower; generalize dependent idx;
        induction cnt; intros=> //=.
      rewrite /_Z_to_bytes_unsigned_le' //=; f_equal.
      - rewrite /_Z_get_byte Z.shiftr_shiftr; try lia.
        by replace (8 + 8 * idx)%Z with (8 * S idx)%Z by lia.
      - fold (_Z_to_bytes_unsigned_le' (S (S idx)) cnt v).
        fold (_Z_to_bytes_unsigned_le' (S idx) cnt (v ≫ 8)).
        assert (v < 2^(8*cnt) \/ 2^(8*cnt) <= v)%Z as [Hv | Hv] by lia.
        + by apply IHcnt.
        + rewrite /_Z_to_bytes_unsigned_le' //=.
          rewrite -seq_shift map_map.
          generalize (seq (S idx) cnt); induction l=> //=; f_equal.
          * rewrite /_Z_get_byte Z.shiftr_shiftr; try lia.
            by replace (8 + 8 * a)%Z with (8 * S a)%Z by lia.
          * apply IHl.
    Qed.

  End ToBytesFacts_internal.

  Section FromBytes_internal.

    Definition _Z_from_bytes_unsigned_le' (idx: nat) (bytes: list N): Z :=
      foldr (fun '(idx, byte) acc => Z.lor (_Z_set_byte (Z.of_N byte) idx) acc)
            0%Z (zip (seq idx (length bytes)) bytes).

    Definition _Z_from_bytes_unsigned_le (bytes: list N): Z :=
      _Z_from_bytes_unsigned_le' 0 bytes.

    Definition _Z_from_bytes_le (sgn: signed) (bytes: list N): Z :=
      let unsigned := _Z_from_bytes_unsigned_le bytes in
      match sgn with
      | Signed => to_signed_bits (8 * N.of_nat (length bytes)) unsigned
      | Unsigned => unsigned
      end.

    (* NOTE: This will be sealed once we finish the proofs for this section. *)
    Definition _Z_from_bytes_def (endianness: endian) (sgn: signed) (bytes: list N): Z :=
      _Z_from_bytes_le
        sgn match endianness with
            | Little => bytes
            | Big    => List.rev bytes
            end.

  End FromBytes_internal.

  Section FromBytesFacts_internal.

    Lemma _Z_from_bytes_unsigned_le'_nil:
      forall (idx: nat),
        _Z_from_bytes_unsigned_le' idx [] = 0%Z.
    Proof. rewrite /_Z_from_bytes_unsigned_le' //=. Qed.

    Lemma _Z_from_bytes_unsigned_le_nil:
      _Z_from_bytes_unsigned_le [] = 0%Z.
    Proof. apply _Z_from_bytes_unsigned_le'_nil. Qed.

    Lemma _Z_from_bytes_le_nil:
      forall sgn,
      _Z_from_bytes_le sgn [] = 0%Z.
    Proof.
      move=> [ | ];
        rewrite /_Z_from_bytes_le
                _Z_from_bytes_unsigned_le_nil //=.
    Qed.

    Lemma _Z_from_bytes_def_nil:
      forall endianness sgn,
        _Z_from_bytes_def endianness sgn [] = 0%Z.
    Proof.
      move=> [ | ] sgn;
        by rewrite /_Z_from_bytes_def /rev
                   _Z_from_bytes_le_nil.
    Qed.

    Lemma _Z_from_bytes_unsigned_le'_cons:
      forall (idx: nat) (byte: N) (bytes: list N),
        _Z_from_bytes_unsigned_le' idx (byte :: bytes) =
        Z.lor (_Z_from_bytes_unsigned_le' idx [byte])
              (_Z_from_bytes_unsigned_le' (S idx) bytes).
    Proof.
      intros; generalize dependent idx; generalize dependent byte;
        induction bytes => //=; intros.
      - rewrite _Z_from_bytes_unsigned_le'_nil Z.lor_0_r; lia.
      - rewrite /_Z_from_bytes_unsigned_le' //=.
        by rewrite Z.lor_0_r.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_cons:
      forall (byte: N) (bytes: list N),
        _Z_from_bytes_unsigned_le (byte :: bytes) =
        Z.lor (_Z_from_bytes_unsigned_le' 0 [byte])
              (_Z_from_bytes_unsigned_le' 1 bytes).
    Proof. apply _Z_from_bytes_unsigned_le'_cons. Qed.

    Lemma _Z_from_bytes_unsigned_le'_app:
      forall (idx: nat) (bs1 bs2: list N),
        _Z_from_bytes_unsigned_le' idx (bs1 ++ bs2) =
        Z.lor (_Z_from_bytes_unsigned_le' idx bs1)
              (_Z_from_bytes_unsigned_le' (idx + length bs1) bs2).
    Proof.
      intros; generalize dependent idx; generalize dependent bs2;
        induction bs1 => //=; intros.
      - repeat rewrite _Z_from_bytes_unsigned_le'_nil.
        replace (idx + 0) with idx by lia.
        by rewrite Z.lor_0_l.
      - rewrite _Z_from_bytes_unsigned_le'_cons.
        rewrite (_Z_from_bytes_unsigned_le'_cons idx a bs1).
        rewrite IHbs1.
        rewrite plus_Snm_nSm.
        by rewrite Z.lor_assoc.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_app:
      forall (bs1 bs2: list N),
        _Z_from_bytes_unsigned_le (bs1 ++ bs2) =
        Z.lor (_Z_from_bytes_unsigned_le' 0 bs1)
              (_Z_from_bytes_unsigned_le' (length bs1) bs2).
    Proof. apply _Z_from_bytes_unsigned_le'_app. Qed.

    Lemma _Z_from_bytes_unsigned_le'_0s:
      forall (idx cnt: nat),
        _Z_from_bytes_unsigned_le' idx (repeat 0%N cnt) = 0%Z.
    Proof.
      intros; generalize dependent idx.
      induction cnt => idx //=.
      rewrite _Z_from_bytes_unsigned_le'_cons.
      rewrite IHcnt.
      rewrite /_Z_from_bytes_unsigned_le' //=.
      by rewrite _Z_set_byte_0 !Z.lor_0_r.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_0s:
      forall (cnt: nat),
        _Z_from_bytes_unsigned_le (repeat 0%N cnt) = 0%Z.
    Proof. apply _Z_from_bytes_unsigned_le'_0s. Qed.

    Lemma _Z_from_bytes_le_0s:
      forall sgn (cnt: nat),
        _Z_from_bytes_le sgn (repeat 0%N cnt) = 0%Z.
    Proof.
      move=> [ | ] cnt; rewrite /_Z_from_bytes_le.
      - rewrite repeat_length _Z_from_bytes_unsigned_le_0s.
        assert (8 * N.of_nat cnt = 0 \/ 0 < 8 * N.of_nat cnt)%N as [Hcnt | Hcnt] by lia.
        + rewrite /to_signed_bits bool_decide_eq_true_2; by lia.
        + rewrite to_signed_bits_id; intuition; [by reflexivity | ].
          apply Z.pow_pos_nonneg; lia.
      - apply _Z_from_bytes_unsigned_le_0s.
    Qed.

    Lemma _Z_from_bytes_def_0s:
      forall endianness sgn (cnt: nat),
        _Z_from_bytes_def endianness sgn (repeat 0%N cnt) = 0%Z.
    Proof.
      move=> [ | ] sgn cnt; rewrite /_Z_from_bytes_def ?rev_repeat;
        apply _Z_from_bytes_le_0s.
    Qed.

    Lemma _Z_from_bytes_unsigned_le'_S_idx:
      forall (idx: nat) (bytes: list N),
        (_Z_from_bytes_unsigned_le' (S idx) (bytes) =
         _Z_from_bytes_unsigned_le' idx bytes ≪ 8)%Z.
    Proof.
      intros idx bytes; generalize dependent idx;
        induction bytes; intros=> //=.
      rewrite /_Z_from_bytes_unsigned_le' //=.
      fold (_Z_from_bytes_unsigned_le' (S (S idx)) bytes).
      fold (_Z_from_bytes_unsigned_le' (S idx) bytes).
      rewrite Z.shiftl_lor.
      by rewrite IHbytes _Z_set_byte_S_idx.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_bswap:
      forall bsz sz (bytes: list N) v,
        Datatypes.length bytes = sz ->
        bytesNat bsz = sz ->
        _Z_from_bytes_unsigned_le bytes = v ->
        _Z_from_bytes_unsigned_le (rev bytes) = builtins.bswap bsz v.
    Proof.
      rewrite /_Z_from_bytes_unsigned_le/_Z_from_bytes_unsigned_le';
        move=> bsz sz bytes v Hlen Hsz Hdecodes; destruct bsz;
        simpl in *; subst.
      - f_equal; do 2 destruct bytes=> //=.
      - do 3 destruct bytes=> //=.
        by rewrite bswap16_set_byte_reverse.
      - do 5 destruct bytes=> //=.
        by rewrite bswap32_set_byte_reverse.
      - do 9 destruct bytes=> //=.
        by rewrite bswap64_set_byte_reverse.
      - do 17 destruct bytes=> //=.
        by rewrite bswap128_set_byte_reverse.
    Qed.

  End FromBytesFacts_internal.

  Section FromToFacts_internal.

    Lemma _Z_from_to_bytes_unsigned_le'_overflow:
      forall (idx cnt: nat) (v: Z),
        (2^(8*(idx+cnt)) <= v)%Z ->
        _Z_from_bytes_unsigned_le' idx (_Z_to_bytes_unsigned_le' idx cnt v) =
        Z.land ((Z.ones (8*cnt)) ≪ (8*idx)) v.
    Proof.
      intros idx cnt v Hlower;
        generalize dependent idx;
        generalize dependent v;
        induction cnt; intros=> //=.
      - rewrite /Z.ones Z.mul_0_r Z.shiftl_0_r
                _Z_to_bytes_unsigned_le'_0_bytes
                _Z_from_bytes_unsigned_le'_nil.
        by rewrite Z.shiftl_0_l Z.land_0_l.
      - rewrite _Z_to_bytes_unsigned_le'_S_cnt
                _Z_from_bytes_unsigned_le'_app
                _Z_to_bytes_unsigned_le'_length.
        rewrite [_Z_to_bytes_unsigned_le' _ 1 _]/_Z_to_bytes_unsigned_le' //=.
        rewrite [_Z_from_bytes_unsigned_le' _ [_]]/_Z_from_bytes_unsigned_le' //=.
        rewrite Z.lor_0_r.
        rewrite Z2N.id; [ | apply _Z_get_byte_nonneg].
        rewrite _Z_get_set_byte_roundtrip.
        assert (2^(8*(idx+cnt)) <= v)%Z as Hlower'. {
          etrans; last eapply Hlower;
            apply Z.pow_le_mono_r; lia.
        }
        specialize (IHcnt v idx Hlower'); rewrite IHcnt //=.
        apply Z.bits_inj'=> n ?.
        rewrite Z.lor_spec !Z.land_spec !Z.shiftl_spec; try lia.
        rewrite !Z.testbit_ones; try lia.
        churn_bits.
    Qed.

    Lemma _Z_from_to_bytes_unsigned_le'_roundtrip:
      forall (idx cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*(idx+cnt)))%Z ->
        _Z_from_bytes_unsigned_le' idx (_Z_to_bytes_unsigned_le' idx cnt v) =
        (v - v `mod` 2^(8*idx))%Z.
    Proof.
      intros idx cnt v Hlower Hupper;
        generalize dependent idx;
        generalize dependent v;
        induction cnt; intros=> //=.
      - rewrite Z.add_0_r in Hupper.
        rewrite _Z_to_bytes_unsigned_le'_0_bytes
                _Z_from_bytes_unsigned_le'_nil.
        rewrite Zmod_small; try intuition; lia.
      - assert (v < 2^(8*(idx+cnt)) \/ 2^(8*(idx+cnt)) <= v)%Z as [Hv | Hv] by lia.
        + rewrite _Z_to_bytes_unsigned_le'_S_cnt
                  _Z_from_bytes_unsigned_le'_app
                  _Z_to_bytes_unsigned_le'_length
                  IHcnt; try lia.
          rewrite _Z_to_bytes_unsigned_le'_small; try lia.
          1: by rewrite _Z_from_bytes_unsigned_le'_0s Z.lor_0_r.
          (* XXX no more needed in 8.12. *)
          all: replace (8 * (idx + cnt)%nat)%Z with (8 * (idx + cnt))%Z; lia.
        + clear IHcnt.
          rewrite Zmod_eq_full.
          2: pose proof (Z.pow_pos_nonneg
                           2 (8 * idx)
                           ltac:(lia) ltac:(lia)); lia.
          rewrite -Z.shiftr_div_pow2; try lia.
          rewrite -Z.shiftl_mul_pow2; try lia.
          rewrite -Z.ldiff_ones_r; try lia.
          rewrite _Z_to_bytes_unsigned_le'_S_cnt
                  _Z_from_bytes_unsigned_le'_app
                  _Z_to_bytes_unsigned_le'_length.
          rewrite Z.sub_sub_distr Z.sub_diag Z.add_0_l.
          rewrite [_Z_to_bytes_unsigned_le' _ 1 _]/_Z_to_bytes_unsigned_le' //=.
          rewrite [_Z_from_bytes_unsigned_le' _ [_]]/_Z_from_bytes_unsigned_le' //=.
          rewrite Z.lor_0_r.
          rewrite Z2N.id; [ | apply _Z_get_byte_nonneg].
          rewrite _Z_get_set_byte_roundtrip.
          rewrite _Z_from_to_bytes_unsigned_le'_overflow; try lia.
          symmetry; apply Z_ldiff_split; lia.
    Qed.

    Lemma _Z_from_to_bytes_unsigned_le_roundtrip:
      forall (cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes_unsigned_le (_Z_to_bytes_unsigned_le cnt v) = v.
    Proof.
      intros cnt v Hlower Hupper.
      pose proof (_Z_from_to_bytes_unsigned_le'_roundtrip 0 cnt v Hlower) as Hpf.
      rewrite Z.add_0_l in Hpf.
      specialize (Hpf Hupper).
      rewrite /_Z_from_bytes_unsigned_le
              /_Z_to_bytes_unsigned_le Hpf.
      rewrite Z.mul_0_r Z.pow_0_r Zmod_1_r; lia.
    Qed.

    Lemma _Z_from_to_bytes_le_roundtrip:
      forall (cnt: nat) (sgn: signed) (v: Z),
        match sgn with
        | Signed   => -2^((8*cnt)-1) <= v /\ v <= 2^((8*cnt)-1) - 1
        | Unsigned => 0 <= v /\ v < 2^(8*cnt)
        end%Z ->
        _Z_from_bytes_le sgn (_Z_to_bytes_le cnt sgn v) = v.
    Proof.
      destruct sgn; intros v [Hlower Hupper];
        [ | by apply _Z_from_to_bytes_unsigned_le_roundtrip].
      rewrite /_Z_from_bytes_le /_Z_to_bytes_le _Z_to_bytes_unsigned_le_length.
      assert (v < 0 \/ 0 <= v)%Z as [Hv | Hv] by lia.
      - rewrite _Z_from_to_bytes_unsigned_le_roundtrip.
        + apply to_signed_unsigned_bits_roundtrip; intuition;
            replace (Z.of_N (8 * N.of_nat cnt) - 1)%Z
              with (8 * cnt - 1)%Z; lia.
        + rewrite /trim; apply Z_mod_pos;
            apply Z.pow_pos_nonneg; lia.
        + rewrite /trim.
          replace (Z.of_N (8 * N.of_nat cnt))
            with (8 * cnt)%Z by lia.
          by pose proof (Z_mod_lt v (2^(8*cnt))%Z
                                   ltac:(apply Z.lt_gt; apply Z.pow_pos_nonneg; lia))
            as [? ?].
      - rewrite /trim Zmod_small; intuition; try lia.
        + rewrite _Z_from_to_bytes_unsigned_le_roundtrip; try lia.
          * apply to_signed_bits_id; intuition.
            eapply Z.le_lt_trans; eauto.
            replace (Z.of_N (8 * N.of_nat cnt) - 1)%Z
              with (8 * cnt - 1)%Z; lia.
          * eapply Z.le_lt_trans; eauto.
            match goal with
            | |- (_ < ?r)%Z => replace r with (r - 0)%Z by lia
            end.
            apply Z.sub_lt_le_mono; try apply Z.pow_lt_mono_r; lia.
        + eapply Z.le_lt_trans; eauto.
          match goal with
          | |- (_ < ?r)%Z => replace r with (r - 0)%Z by lia
          end.
          apply Z.sub_lt_le_mono; try apply Z.pow_lt_mono_r; lia.
    Qed.

    Lemma _Z_from_unsigned_to_signed_bytes_le:
      forall (cnt: nat) (v: Z),
        (-2^((8*cnt)-1) <= v)%Z ->
        (v <= 2^((8*cnt)-1) - 1)%Z ->
        _Z_from_bytes_le Unsigned (_Z_to_bytes_le cnt Signed v) =
        to_unsigned_bits (8*N.of_nat cnt) v.
    Proof.
      move=> cnt v Hlower Hupper.
      rewrite /trim /_Z_from_bytes_le /_Z_to_bytes_le.
      rewrite _Z_from_to_bytes_unsigned_le_roundtrip /trim //.
      - apply Z_mod_lt; rewrite Z.gt_lt_iff;
          apply Z.pow_pos_nonneg; lia.
      - replace (Z.of_N (8 * N.of_nat cnt)) with (8 * cnt)%Z by lia;
          apply Z_mod_lt; rewrite Z.gt_lt_iff;
          apply Z.pow_pos_nonneg; lia.
    Qed.

    Lemma _Z_from_signed_to_unsigned_bytes_le:
      forall (cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes_le Signed (_Z_to_bytes_le cnt Unsigned v) =
        to_signed_bits (8*N.of_nat cnt) v.
    Proof.
      move=> cnt v Hlower Hupper.
      rewrite /_Z_from_bytes_le /_Z_to_bytes_le
              _Z_to_bytes_unsigned_le_length
              _Z_from_to_bytes_unsigned_le_roundtrip //.
    Qed.

    Lemma _Z_from_to_bytes_def_roundtrip:
      forall (cnt: nat) (endianness: endian) (sgn: signed) (v: Z),
        match sgn with
        | Signed   => -2^((8*cnt)-1) <= v /\ v <= 2^((8*cnt)-1) - 1
        | Unsigned => 0 <= v /\ v < 2^(8*cnt)
        end%Z ->
        _Z_from_bytes_def endianness sgn (_Z_to_bytes_def cnt endianness sgn v) = v.
    Proof.
      rewrite /_Z_from_bytes_def /_Z_to_bytes_def;
        intros cnt [ | ] sgn v H;
        try rewrite rev_involutive;
        by apply _Z_from_to_bytes_le_roundtrip.
    Qed.

    Lemma _Z_from_unsigned_to_signed_bytes_def:
      forall (cnt: nat) (endianness: endian) (v: Z),
        (-2^((8*cnt)-1) <= v)%Z ->
        (v <= 2^((8*cnt)-1) - 1)%Z ->
        _Z_from_bytes_def endianness Unsigned (_Z_to_bytes_def cnt endianness Signed v) =
        to_unsigned_bits (8*N.of_nat cnt) v.
    Proof.
      rewrite /_Z_from_bytes_def /_Z_to_bytes_def;
        intros cnt [ | ] v Hlower Hupper;
        try rewrite rev_involutive;
        by apply _Z_from_unsigned_to_signed_bytes_le.
    Qed.

    Lemma _Z_from_signed_to_unsigned_bytes_def:
      forall (cnt: nat) (endianness: endian) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes_def endianness Signed (_Z_to_bytes_def cnt endianness Unsigned v) =
        to_signed_bits (8*N.of_nat cnt) v.
    Proof.
      rewrite /_Z_from_bytes_def /_Z_to_bytes_def;
        intros cnt [ | ] v Hlower Hupper;
        try rewrite rev_involutive;
        by apply _Z_from_signed_to_unsigned_bytes_le.
    Qed.

  End FromToFacts_internal.

  Section ToBytes_external.

    Definition _Z_to_bytes_aux : seal (_Z_to_bytes_def). Proof. by eexists. Qed.
    Definition _Z_to_bytes := _Z_to_bytes_aux.(unseal).
    Definition _Z_to_bytes_eq: _Z_to_bytes = _ := _Z_to_bytes_aux.(seal_eq).

  End ToBytes_external.

  Section ToBytesFacts_external.

    Lemma _Z_to_bytes_length:
      forall (cnt: nat) endianness sgn v,
        length (_Z_to_bytes cnt endianness sgn v) = cnt.
    Proof. move=> *; rewrite _Z_to_bytes_eq; apply _Z_to_bytes_def_length. Qed.

    Lemma _Z_to_bytes_0_bytes:
      forall sgn endianness v,
        _Z_to_bytes 0 endianness sgn v = [].
    Proof. move=> *; rewrite _Z_to_bytes_eq; apply _Z_to_bytes_def_0_bytes. Qed.

    Lemma _Z_to_bytes_0_value:
      forall (cnt: nat) endianness sgn,
        _Z_to_bytes cnt endianness sgn 0%Z = repeat 0%N cnt.
    Proof. move=> *; rewrite _Z_to_bytes_eq; apply _Z_to_bytes_def_0_value. Qed.

  End ToBytesFacts_external.

  Section FromBytes_external.

    Definition _Z_from_bytes_aux: seal _Z_from_bytes_def. Proof. by eexists. Qed.
    Definition _Z_from_bytes := _Z_from_bytes_aux.(unseal).
    Definition _Z_from_bytes_eq: @_Z_from_bytes = _ := _Z_from_bytes_aux.(seal_eq).

  End FromBytes_external.

  Section FromBytesFacts_external.

    Lemma _Z_from_bytes_nil:
      forall endianness sgn,
        _Z_from_bytes endianness sgn [] = 0%Z.
    Proof. move=> *; rewrite _Z_from_bytes_eq; apply _Z_from_bytes_def_nil. Qed.

    Lemma _Z_from_bytes_0s:
      forall endianness sgn (cnt: nat),
        _Z_from_bytes endianness sgn (repeat 0%N cnt) = 0%Z.
    Proof. move=> *; rewrite _Z_from_bytes_eq; apply _Z_from_bytes_def_0s. Qed.

  End FromBytesFacts_external.

  Section FromToFacts_external.

    Lemma _Z_from_to_bytes_roundtrip:
      forall (cnt: nat) (endianness: endian) (sgn: signed) (v: Z),
        match sgn with
        | Signed   => -2^((8*cnt)-1) <= v /\ v <= 2^((8*cnt)-1) - 1
        | Unsigned => 0 <= v /\ v < 2^(8*cnt)
        end%Z ->
        _Z_from_bytes endianness sgn (_Z_to_bytes cnt endianness sgn v) = v.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        by apply _Z_from_to_bytes_def_roundtrip.
    Qed.

    Lemma _Z_from_unsigned_to_signed_bytes:
      forall (cnt: nat) (endianness: endian) (v: Z),
        (-2^((8*cnt)-1) <= v)%Z ->
        (v <= 2^((8*cnt)-1) - 1)%Z ->
        _Z_from_bytes endianness Unsigned (_Z_to_bytes cnt endianness Signed v) =
        to_unsigned_bits (8*N.of_nat cnt) v.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        by apply _Z_from_unsigned_to_signed_bytes_def.
    Qed.

    Lemma _Z_from_signed_to_unsigned_bytes:
      forall (cnt: nat) (endianness: endian) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes endianness Signed (_Z_to_bytes cnt endianness Unsigned v) =
        to_signed_bits (8*N.of_nat cnt) v.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        by apply _Z_from_signed_to_unsigned_bytes_def.
    Qed.

  End FromToFacts_external.

End FromToBytes.
