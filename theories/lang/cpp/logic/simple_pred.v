(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.algebra Require Import excl gmap.
From iris.algebra.lib Require Import frac_auth.
From iris.bi Require Import monpred.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export iprop.
From iris.base_logic.lib Require Import fancy_updates own.
From iris.base_logic.lib Require Import cancelable_invariants.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import pred.

Set Default Proof Using "Type".

(* todo: does this not exist as a library somewhere? *)
Definition fractionalR (o : ofeT) : cmraT :=
  prodR fracR (agreeR o).
Definition frac {o: ofeT} (q : Qp) (v : o) : fractionalR o :=
  (q, to_agree v).

Lemma Some_valid:
  forall M (A : cmraT) (x : cmra_car A),
    (@uPred_cmra_valid (iResUR M) (optionR A) (@Some (cmra_car A) x)) -|-
    (@uPred_cmra_valid (iResUR M) A x).
Proof.
  intros M A x.
  rewrite (@uPred_primitive.option_validI (iResUR M) _ (Some x)). reflexivity.
Qed.
Lemma None_valid:
  forall M (A : cmraT) (x : cmra_car A),
    (@uPred_cmra_valid (iResUR M) (optionR A) None) -|- True.
Proof.
  intros M A x.
  rewrite (@uPred_primitive.option_validI (iResUR M) _ None). reflexivity.
Qed.

Lemma join_singleton_eq : forall `{Countable K, EqDecision K} {V : cmraT} (k : K) (v1 v2 : V),
    {[ k := v1 ]} ⋅ {[ k := v2 ]} =@{gmap K V} {[ k := v1 ⋅ v2 ]}.
Proof. intros. by apply (merge_singleton _ _ _ v1 v2). Qed.

Lemma singleton_valid_norm :
  ltac:(match type of @singleton_valid with
        | ?T => let X := eval simpl in T in exact X
        end).
Proof. exact @singleton_valid. Defined.

Lemma frac_op {A : ofeT} (l : A)  (p q : Qp) :
  frac p l ⋅ frac q l ≡ frac (p + q) l.
Proof. by rewrite -pair_op agree_idemp. Qed.

Section FromToBytes.

  Section Byte.

    Definition _Z_get_byte (x: Z) (n: nat): Z := Z.land (x ≫ (8 * n)) (Z.ones 8).
    Definition _Z_set_byte (x: Z) (n: nat): Z := (Z.land (Z.ones 8) x) ≪ (8 * n).

    Lemma _Z_get_byte_0:
      forall (idx: nat),
        _Z_get_byte 0 idx = 0.
    Proof. intros; now rewrite /_Z_get_byte Z.shiftr_0_l Z.land_0_l. Qed.

    Lemma _Z_set_byte_0:
      forall (idx: nat),
        _Z_set_byte 0 idx = 0.
    Proof. intros; now rewrite /_Z_set_byte Z.shiftl_0_l. Qed.

    Lemma _Z_get_byte_S_idx:
      forall (v: Z) (idx: nat),
        _Z_get_byte v (S idx) = _Z_get_byte (v ≫ 8) idx.
    Proof.
      intros; rewrite /_Z_get_byte.
      rewrite Z.shiftr_shiftr; try lia.
      now replace (8 + 8 * idx)%Z
        with (8 * S idx)%Z
        by lia.
    Qed.

    Lemma _Z_set_byte_S_idx:
      forall (v: Z) (idx: nat),
        _Z_set_byte v (S idx) = ((_Z_set_byte v idx) ≪ 8)%Z.
    Proof.
      intros; rewrite /_Z_set_byte.
      rewrite Z.shiftl_shiftl; try lia.
      now replace (8 * idx + 8)%Z
        with (8 * S idx)%Z
        by lia.
    Qed.

    Lemma _Z_get_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _Z_get_byte v idx)%Z.
    Proof.
      intros; rewrite /_Z_get_byte /Z.ones.
      apply Z.land_nonneg.
      replace (Z.pred (1 ≪ 8)) with (255)%Z by reflexivity; lia.
    Qed.

    Lemma _Z_set_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _Z_set_byte v idx)%Z.
    Proof.
      intros; rewrite /_Z_set_byte /Z.ones Z.shiftl_nonneg.
      apply Z.land_nonneg.
      replace (Z.pred (1 ≪ 8)) with (255)%Z by reflexivity; lia.
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

  End Byte.

  Section ExtraFacts.

    Lemma repeat_cons_app:
      forall (A: Type) (a: A) (cnt: nat),
        (a :: repeat a cnt) = repeat a cnt ++ [a].
    Proof.
      induction cnt => //=.
      now rewrite IHcnt.
    Qed.

    Lemma rev_repeat:
      forall (A: Type) (a: A) (cnt: nat),
        rev (repeat a cnt) = repeat a cnt.
    Proof.
      induction cnt => //=.
      now rewrite IHcnt repeat_cons_app.
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
      - now replace (8 * (0%nat + b))%Z with (8 * b)%Z by lia.
      - eapply Z.lt_trans; eauto; apply Z.pow_lt_mono_r; lia.
    Qed.

    Lemma Z_pow2_trans_nat_r:
      forall v (a b: nat),
        (v < 2 ^ (8 * a))%Z ->
        (v < 2 ^ (8 * (a + b)%nat))%Z.
    Proof.
      intros; destruct b.
      - now replace (8 * (a + 0)%nat)%Z with (8 * a)%Z by lia.
      - eapply Z.lt_trans; eauto; apply Z.pow_lt_mono_r; lia.
    Qed.

    Lemma Z_land_ldiff_no_overlap:
      forall (mask offset v: Z),
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
      rewrite !andb_false_r Z.testbit_neg_r //.  lia.
    Qed.

    Lemma Z_land_ldiff_upper_byte:
      forall (offset v: Z),
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
        replace (255)%Z with (Z.ones 8) by reflexivity.
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
        [subst; now rewrite !Z.land_0_r Z.lor_diag Z.ldiff_0_l | clear Hlower].
      apply Z.bits_inj'=> n ?.
      rewrite Z.lor_spec Z.ldiff_spec !Z.land_spec !Z.shiftl_spec; try lia.
      rewrite !Z.testbit_ones; try lia.
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
                   ?orb_false_l ?orb_false_r ?orb_true_l ?orb_true_r //=;
                   try lia.
      apply Z.bits_above_log2; try lia.
      assert (8 * (idx+S cnt)%nat <= n)%Z by lia.
      eapply Z.lt_le_trans; eauto.
      apply Z.log2_lt_pow2; try lia.
      now replace (8 * (idx+S cnt)%nat)%Z
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
    Definition _Z_to_bytes_def {σ: genv} (cnt: nat) (sgn: signed) (v: Z): list N :=
      let little := _Z_to_bytes_le cnt sgn v in
      match byte_order σ with
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
        now rewrite map_length seq_length.
    Qed.

    Definition _Z_to_bytes_unsigned_le_length:
      forall cnt v,
        length (_Z_to_bytes_unsigned_le cnt v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_unsigned_le => * //=;
        now apply _Z_to_bytes_unsigned_le'_length.
    Qed.

    Lemma _Z_to_bytes_le_length:
      forall cnt sgn v,
        length (_Z_to_bytes_le cnt sgn v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_le => * //=;
        now apply _Z_to_bytes_unsigned_le_length.
    Qed.

    Lemma _Z_to_bytes_def_length:
      forall σ cnt sgn v,
        length (@_Z_to_bytes_def σ cnt sgn v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_def => σ cnt sgn v //=;
        destruct (byte_order σ);
        try rewrite rev_length;
        now apply _Z_to_bytes_le_length.
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
      forall σ sgn (v: Z),
        _Z_to_bytes_def (σ:=σ) 0 sgn v = [].
    Proof.
      move=> σ [ | ] v;
        rewrite /_Z_to_bytes_def
                _Z_to_bytes_le_0_bytes;
        by case_match.
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
      forall σ (cnt: nat) sgn,
        _Z_to_bytes_def (σ:=σ) cnt sgn 0 = repeat 0%N cnt.
    Proof.
      move=> σ cnt [ | ];
        rewrite /_Z_to_bytes_def
                _Z_to_bytes_le_0_value
                rev_repeat;
        by case_match.
    Qed.

    Lemma _Z_to_bytes_unsigned_le'_S_cnt:
      forall (idx cnt: nat) (v: Z),
        _Z_to_bytes_unsigned_le' idx (S cnt) v =
        _Z_to_bytes_unsigned_le' idx cnt v ++
        _Z_to_bytes_unsigned_le' (idx+cnt) 1 v.
    Proof.
      intros; generalize dependent idx;
        induction cnt; intros=> //=.
      - now rewrite Nat.add_0_r.
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
        now replace (8 + 8 * idx)%Z with (8 * S idx)%Z by lia.
      - fold (_Z_to_bytes_unsigned_le' (S (S idx)) cnt v).
        fold (_Z_to_bytes_unsigned_le' (S idx) cnt (v ≫ 8)).
        assert (v < 2^(8*cnt) \/ 2^(8*cnt) <= v)%Z as [Hv | Hv] by lia.
        + now apply IHcnt.
        + rewrite /_Z_to_bytes_unsigned_le' //=.
          rewrite -seq_shift map_map.
          generalize (seq (S idx) cnt); induction l=> //=; f_equal.
          * rewrite /_Z_get_byte Z.shiftr_shiftr; try lia.
            now replace (8 + 8 * a)%Z with (8 * S a)%Z by lia.
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
    Definition _Z_from_bytes_def {σ: genv} (sgn: signed) (bytes: list N): Z :=
      _Z_from_bytes_le
        sgn match byte_order σ with
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
      forall σ sgn,
        _Z_from_bytes_def (σ:=σ) sgn [] = 0%Z.
    Proof.
      move=> σ [ | ];
        rewrite /_Z_from_bytes_def /rev;
        case_match; now rewrite _Z_from_bytes_le_nil.
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
        now rewrite Z.lor_0_r.
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
        now rewrite Z.lor_0_l.
      - rewrite _Z_from_bytes_unsigned_le'_cons.
        rewrite (_Z_from_bytes_unsigned_le'_cons idx a bs1).
        rewrite IHbs1.
        replace (S idx + length bs1)
          with (idx + S (length bs1))
          by lia.
        now rewrite Z.lor_assoc.
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
      now rewrite _Z_set_byte_0 !Z.lor_0_r.
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
      forall σ sgn (cnt: nat),
        _Z_from_bytes_def (σ:=σ) sgn (repeat 0%N cnt) = 0%Z.
    Proof.
      move=> σ [ | ] cnt; rewrite /_Z_from_bytes_def rev_repeat;
        case_match; apply _Z_from_bytes_le_0s.
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
      now rewrite IHbytes _Z_set_byte_S_idx.
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
        replace (Z.pred 1) with 0%Z by lia.
        now rewrite Z.shiftl_0_l Z.land_0_l.
      - rewrite _Z_to_bytes_unsigned_le'_S_cnt
                _Z_from_bytes_unsigned_le'_app
                _Z_to_bytes_unsigned_le'_length.
        rewrite [_Z_to_bytes_unsigned_le' _ 1 _]/_Z_to_bytes_unsigned_le' //=.
        rewrite [_Z_from_bytes_unsigned_le' _ [_]]/_Z_from_bytes_unsigned_le' //=.
        rewrite Z.lor_0_r.
        rewrite Z2N.id; [ | apply _Z_get_byte_nonneg].
        rewrite _Z_get_set_byte_roundtrip.
        assert (2^(8*(idx+cnt)) <= v)%Z as Hlower'. {
          eapply Z.le_trans; eauto;
            apply Z.pow_le_mono_r; lia.
        }
        specialize (IHcnt v idx Hlower'); rewrite IHcnt //=.
        apply Z.bits_inj'=> n ?.
        rewrite Z.lor_spec !Z.land_spec !Z.shiftl_spec; try lia.
        rewrite !Z.testbit_ones; try lia.
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
                     ?orb_false_l ?orb_false_r ?orb_true_l ?orb_true_r //=;
                     try lia.
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
      - replace (8 * (idx+0%nat))%Z
          with (8*idx)%Z
          in Hupper by lia.
        rewrite _Z_to_bytes_unsigned_le'_0_bytes
                _Z_from_bytes_unsigned_le'_nil.
        rewrite Zmod_small; try intuition; lia.
      - assert (v < 2^(8*(idx+cnt)) \/ 2^(8*(idx+cnt)) <= v)%Z as [Hv | Hv] by lia.
        + rewrite _Z_to_bytes_unsigned_le'_S_cnt
                  _Z_from_bytes_unsigned_le'_app
                  _Z_to_bytes_unsigned_le'_length
                  IHcnt; try lia.
          rewrite _Z_to_bytes_unsigned_le'_small; try lia.
          2: replace (8 * (idx + cnt)%nat)%Z with (8 * (idx + cnt))%Z; lia.
          now rewrite _Z_from_bytes_unsigned_le'_0s Z.lor_0_r.
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
        [ | now apply _Z_from_to_bytes_unsigned_le_roundtrip].
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
          now pose proof (Z_mod_lt v (2^(8*cnt))%Z
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
      forall (σ: genv) (cnt: nat) (sgn: signed) (v: Z),
        match sgn with
        | Signed   => -2^((8*cnt)-1) <= v /\ v <= 2^((8*cnt)-1) - 1
        | Unsigned => 0 <= v /\ v < 2^(8*cnt)
        end%Z ->
        _Z_from_bytes_def (σ:=σ) sgn (_Z_to_bytes_def (σ:=σ) cnt sgn v) = v.
    Proof.
      rewrite /_Z_from_bytes_def /_Z_to_bytes_def;
        intros σ cnt sgn v H; destruct (byte_order σ);
        try rewrite rev_involutive;
        now apply _Z_from_to_bytes_le_roundtrip.
    Qed.

    Lemma _Z_from_unsigned_to_signed_bytes_def:
      forall (σ: genv) (cnt: nat) (v: Z),
        (-2^((8*cnt)-1) <= v)%Z ->
        (v <= 2^((8*cnt)-1) - 1)%Z ->
        _Z_from_bytes_def (σ:=σ) Unsigned (_Z_to_bytes_def (σ:=σ) cnt Signed v) =
        to_unsigned_bits (8*N.of_nat cnt) v.
    Proof.
      rewrite /_Z_from_bytes_def /_Z_to_bytes_def;
        intros σ cnt v Hlower Hupper; destruct (byte_order σ);
        try rewrite rev_involutive;
        now apply _Z_from_unsigned_to_signed_bytes_le.
    Qed.

    Lemma _Z_from_signed_to_unsigned_bytes_def:
      forall (σ: genv) (cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes_def (σ:=σ) Signed (_Z_to_bytes_def (σ:=σ) cnt Unsigned v) =
        to_signed_bits (8*N.of_nat cnt) v.
    Proof.
      rewrite /_Z_from_bytes_def /_Z_to_bytes_def;
        intros σ cnt v Hlower Hupper; destruct (byte_order σ);
        try rewrite rev_involutive;
        now apply _Z_from_signed_to_unsigned_bytes_le.
    Qed.

  End FromToFacts_internal.

  Section ToBytes_external.

    Definition _Z_to_bytes_aux {σ: genv} : seal (@_Z_to_bytes_def σ). by eexists. Qed.
    Definition _Z_to_bytes {σ: genv} := (_Z_to_bytes_aux (σ:=σ)).(unseal).
    Definition _Z_to_bytes_eq {σ: genv}: @_Z_to_bytes σ = _ :=
      (_Z_to_bytes_aux (σ:=σ)).(seal_eq).

  End ToBytes_external.

  Section ToBytesFacts_external.

    Lemma _Z_to_bytes_length:
      forall σ (cnt: nat) sgn v,
        length (_Z_to_bytes (σ:=σ) cnt sgn v) = cnt.
    Proof. move=> *; rewrite _Z_to_bytes_eq; apply _Z_to_bytes_def_length. Qed.

    Lemma _Z_to_bytes_0_bytes:
      forall σ sgn v,
        _Z_to_bytes (σ:=σ) 0 sgn v = [].
    Proof. move=> *; rewrite _Z_to_bytes_eq; apply _Z_to_bytes_def_0_bytes. Qed.

    Lemma _Z_to_bytes_0_value:
      forall σ (cnt: nat) sgn,
        _Z_to_bytes (σ:=σ) cnt sgn 0%Z = repeat 0%N cnt.
    Proof. move=> *; rewrite _Z_to_bytes_eq; apply _Z_to_bytes_def_0_value. Qed.

  End ToBytesFacts_external.

  Section FromBytes_external.

    Definition _Z_from_bytes_aux {σ: genv} : seal (@_Z_from_bytes_def σ). by eexists. Qed.
    Definition _Z_from_bytes {σ: genv} := (_Z_from_bytes_aux (σ:=σ)).(unseal).
    Definition _Z_from_bytes_eq {σ: genv} : @_Z_from_bytes σ = _ :=
      (_Z_from_bytes_aux (σ:=σ)).(seal_eq).

  End FromBytes_external.

  Section FromBytesFacts_external.

    Lemma _Z_from_bytes_nil:
      forall σ sgn,
        _Z_from_bytes (σ:=σ) sgn [] = 0%Z.
    Proof. move=> *; rewrite _Z_from_bytes_eq; apply _Z_from_bytes_def_nil. Qed.

    Lemma _Z_from_bytes_0s:
      forall σ sgn (cnt: nat),
        _Z_from_bytes (σ:=σ) sgn (repeat 0%N cnt) = 0%Z.
    Proof. move=> *; rewrite _Z_from_bytes_eq; apply _Z_from_bytes_def_0s. Qed.

  End FromBytesFacts_external.

  Section FromToFacts_external.

    Lemma _Z_from_to_bytes_roundtrip:
      forall (σ: genv) (cnt: nat) (sgn: signed) (v: Z),
        match sgn with
        | Signed   => -2^((8*cnt)-1) <= v /\ v <= 2^((8*cnt)-1) - 1
        | Unsigned => 0 <= v /\ v < 2^(8*cnt)
        end%Z ->
        _Z_from_bytes (σ:=σ) sgn (_Z_to_bytes (σ:=σ) cnt sgn v) = v.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        now apply _Z_from_to_bytes_def_roundtrip.
    Qed.

    Lemma _Z_from_unsigned_to_signed_bytes:
      forall (σ: genv) (cnt: nat) (v: Z),
        (-2^((8*cnt)-1) <= v)%Z ->
        (v <= 2^((8*cnt)-1) - 1)%Z ->
        _Z_from_bytes (σ:=σ) Unsigned (_Z_to_bytes (σ:=σ) cnt Signed v) =
        to_unsigned_bits (8*N.of_nat cnt) v.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        now apply _Z_from_unsigned_to_signed_bytes_def.
    Qed.

    Lemma _Z_from_signed_to_unsigned_bytes:
      forall (σ: genv) (cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes (σ:=σ) Signed (_Z_to_bytes (σ:=σ) cnt Unsigned v) =
        to_signed_bits (8*N.of_nat cnt) v.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        now apply _Z_from_signed_to_unsigned_bytes_def.
    Qed.

  End FromToFacts_external.

End FromToBytes.

Local Lemma length__Z_to_bytes_le n sgn v :
  length (_Z_to_bytes_le n sgn v) = n.
Proof. apply _Z_to_bytes_le_length. Qed.

Local Lemma length__Z_to_bytes {σ} n sgn v :
  length (_Z_to_bytes (σ:=σ) n sgn v) = n.
Proof. apply _Z_to_bytes_length. Qed.

(** soundness proof *)

Module SimpleCPP_BASE <: CPP_LOGIC_CLASS.

  Definition addr : Set := N.
  Definition byte : Set := N.
  Variant runtime_val : Set :=
  | Rundef
    (* ^ undefined value, semantically, it means "any value" *)
  | Rval (_ : byte)
    (* ^ machine level byte *)
  | Rpointer_chunk (_ : ptr) (index : nat).
    (* ^ you need the same pointer and consecutive integers to "have" a pointer.
     *)

  Definition Z_to_bytes {σ:genv} (n : nat) (sgn: signed) (v : Z) : list runtime_val :=
    Rval <$> _Z_to_bytes (σ:=σ) n sgn v.

  Lemma length_Z_to_bytes {σ} n sgn v : length (Z_to_bytes (σ:=σ) n sgn v) = n.
  Proof. by rewrite/Z_to_bytes fmap_length length__Z_to_bytes. Qed.

  Class cppG' (Σ : gFunctors) : Type :=
    { memG : inG Σ (gmapR addr (fractionalR (leibnizO runtime_val)))
      (* ^ this represents the contents of physical memory *)
    ; ghost_memG : inG Σ (gmapR ptr (fractionalR (leibnizO val)))
      (* ^ this represents the contents of the C++ runtime that might
         not be represented in physical memory, e.g. values stored in
         registers or temporaries on the stack *)
    ; mem_injG : inG Σ (gmapUR ptr (agreeR (leibnizO (option addr))))
      (* ^ this carries the (compiler-supplied) mapping from C++ locations
         (represented as pointers) to physical memory addresses. Locations that
         are not stored in physical memory (e.g. because they are register
         allocated) are mapped to [None] *)
    ; blocksG : inG Σ (gmapUR ptr (agreeR (leibnizO (Z * Z))))
      (* ^ this represents the minimum and maximum offset of the block *)
    ; codeG : inG Σ (gmapUR ptr (agreeR (leibnizO (Func + Method + Ctor + Dtor))))
      (* ^ this carries the (compiler-supplied) mapping from C++ locations
         to the code stored at that location *)
    ; has_inv' :> invG Σ
    ; has_cinv' :> cinvG Σ
    }.

  Definition cppG : gFunctors -> Type := cppG'.
  Definition has_inv : forall Σ, cppG Σ -> invG Σ := @has_inv'.
  Definition has_cinv : forall Σ, cppG Σ -> cinvG Σ := @has_cinv'.
  Existing Class cppG.

  Record cpp_ghost : Type :=
    { heap_name : gname
    ; ghost_heap_name : gname
    ; mem_inj_name : gname
    ; blocks_name : gname
    ; code_name : gname
    }.
  Definition _cpp_ghost := cpp_ghost.

  Include CPP_LOGIC_CLASS_MIXIN.
End SimpleCPP_BASE.

Module SimpleCPP.
  Include SimpleCPP_BASE.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    Existing Instances memG ghost_memG mem_injG blocksG codeG.

    Definition mpred := iProp Σ.
    Definition mpredI : bi :=
      {| bi_car := mpred
       ; bi_later := bi_later
       ; bi_ofe_mixin := (iPropI Σ).(bi_ofe_mixin)
       ; bi_bi_mixin := (iPropI Σ).(bi_bi_mixin)
       ; bi_bi_later_mixin := (iPropI Σ).(bi_bi_later_mixin)
       |}.
    (* todo: Fix the warning generated from this definition *)


    Lemma singleton_valid_at_norm :
      ∀ `{Countable K} (A : cmraT) (i : K) (x : A),
        ✓ ({[i := x]} : gmap K A) ⊣⊢@{mpredI} ✓ x.
    Proof.
      intros. rewrite gmap_validI. split'; iIntros "Hv".
      - iSpecialize ("Hv" $! i). by rewrite lookup_singleton Some_valid.
      - iIntros (i'). destruct (decide (i = i')) as [->|?].
        + by rewrite lookup_singleton Some_valid.
        + by rewrite lookup_singleton_ne.
    Qed.

    (** pointer validity *)
    (** Pointers past the end of an object/array can be valid; see
    https://eel.is/c++draft/expr.add#4 *)
    Definition valid_ptr (p : ptr) : mpred.
    refine ([| p = nullptr |] \\//
            (Exists base l h o,
                own _ghost.(blocks_name) {[ base := to_agree (l, h) ]} **
                [| (l <= o <= h)%Z |] ** [| p = offset_ptr_ o base |])).
    unshelve eapply blocksG; apply has_cppG. refine _.
    Defined.

    Theorem valid_ptr_persistent : forall p, Persistent (valid_ptr p).
    Proof. apply _. Qed.
    Theorem valid_ptr_affine : forall p, Affine (valid_ptr p).
    Proof. apply _. Qed.
    Theorem valid_ptr_timeless : forall p, Timeless (valid_ptr p).
    Proof. apply _. Qed.
    Existing Instance valid_ptr_persistent.
    Existing Instance valid_ptr_affine.
    Existing Instance valid_ptr_timeless.

    Theorem valid_ptr_nullptr : |-- valid_ptr nullptr.
    Proof. by iLeft. Qed.

    Definition size_to_bytes (s : bitsize) : nat :=
      match s with
      | W8 => 1
      | W16 => 2
      | W32 => 4
      | W64 => 8
      | W128 => 16
      end.

    Section with_genv.
      Variable σ : genv.

      Let POINTER_BYTES : nat := N.to_nat σ.(pointer_size).

      Definition aptr (p : ptr) : list runtime_val :=
        List.map (Rpointer_chunk p) (seq 0 POINTER_BYTES).

      Notation Z_to_bytes := (Z_to_bytes (σ:=σ)).

      Definition cptr (a : N) : list runtime_val :=
        Z_to_bytes POINTER_BYTES Unsigned (Z.of_N a).

      Lemma length_aptr p : length (aptr p) = POINTER_BYTES.
      Proof. by rewrite/aptr fmap_length seq_length. Qed.
      Lemma length_cptr a : length (cptr a) = POINTER_BYTES.
      Proof. by rewrite /cptr length_Z_to_bytes. Qed.

      (** WRT pointer equality, see https://eel.is/c++draft/expr.eq#3 *)
      Definition encodes (t : type) (v : val) (vs : list runtime_val) : mpred.
      refine
        match erase_qualifiers t with
        | Tint sz sgn =>
          match v with
          | Vint v => [| vs = Z_to_bytes (size_to_bytes sz) sgn v |]
          | Vundef => [| length vs = size_to_bytes sz |]
          | _ => lfalse
          end
        | Tmember_pointer _ _ =>
          match v with
          | Vint v =>
            (* note: this is really an offset *)
            [| vs = Z_to_bytes POINTER_BYTES Unsigned v |]
          | Vundef => [| length vs = POINTER_BYTES |]
          | _ => lfalse
          end

        | Tbool =>
          if decide (v = Vint 0) then [| vs = [Rval 0%N] |]
          else if decide (v = Vint 1) then [| vs = [Rval 1%N] |]
          else lfalse
        | Tnullptr =>
          [| vs = cptr 0 |]
        | Tfloat _ => lfalse
        | Tarch _ _ => lfalse
        | Tpointer _ =>
          match v with
          | Vptr p =>
            if decide (p = nullptr) then
              [| vs = cptr 0 |]
            else
              [| vs = aptr p |]
          | _ => lfalse
          end
        | Tfunction _ _
        | Treference _
        | Trv_reference _ =>
          match v with
          | Vptr p =>
            [| p <> nullptr |] **
            [| vs = aptr p |]
          | Vundef => [| length vs = POINTER_BYTES |]
          | _ => lfalse
          end
        | Tqualified _ _ => lfalse (* unreachable *)
        | Tvoid
        | Tarray _ _
        | Tnamed _ => lfalse (* not directly encoded in memory *)
        end.
      all: try (unshelve eapply mem_injG; apply has_cppG).
      all: refine _.
      Defined.

      Global Instance encodes_persistent : forall t v vs, Persistent (encodes t v vs).
      Proof.
        unfold encodes.
        intros; destruct (erase_qualifiers t); intros;
          destruct v; try refine _.
        - case_decide; refine _.
        - destruct z; refine _.
          destruct p; refine _.
      Qed.

      Global Instance encodes_timeless : forall t v a, Timeless (encodes t v a).
      Proof.
        intros. unfold encodes. destruct (erase_qualifiers t); destruct v; refine _.
        - case_decide; refine _.
        - destruct z; refine _.
          destruct p; refine _.
      Qed.

      Local Hint Resolve bi.False_elim : core.
      Local Hint Resolve length_Z_to_bytes : core.
      Local Hint Resolve length_aptr : core.
      Local Hint Resolve length_cptr : core.

      Lemma length_encodes t v vs :
        encodes t v vs |-- [|
          length vs = match erase_qualifiers t with
          | Tbool => 1
          | Tint sz _ => size_to_bytes sz

          | Tmember_pointer _ _ | Tnullptr | Tpointer _
          | Tfunction _ _ | Treference _ | Trv_reference _ =>
            POINTER_BYTES

          | _ => 0	(* dummy *)
          end
        |].
      Proof.
        rewrite/encodes. destruct (erase_qualifiers _), v; try done; intros;
        repeat match goal with
        | |- [| _ = _ |] |-- [| _ |] => f_equiv=>->
        | |- [| _ ≠ _ |] ** [| _ = _ |] |-- [| _ |] => rewrite bi.sep_elim_r
        | |- context [@decide _ _] => case_decide
        end;
        auto.
      Qed.

      Local Hint Extern 1 =>
        match goal with
        | |- (False ∗ _ ⊢ _)%I => rewrite bi.sep_elim_l; apply bi.False_elim
        | |- (_ ∗ False ⊢ _)%I => rewrite bi.sep_elim_r; apply bi.False_elim
        end : core.
      Lemma encodes_agree t v1 v2 vs :
        encodes t v1 vs |-- encodes t v2 vs -* [| v1 = v2 |].
      Proof.
        apply bi.wand_intro_r.
        rewrite/encodes. case: (erase_qualifiers t)=>//=.
        - move=>_. case: v1; auto=>p1. case: v2; auto=>p2.
          (* PDS: I see no way to proceed when p1 null, p2 nonnull *)
      Abort.
    End with_genv.

    Instance Z_to_bytes_proper :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq) (@Z_to_bytes).
    Proof.
      intros ?? Hσ. repeat intro. subst. unfold Z_to_bytes, _Z_to_bytes.
      f_equal.
      rewrite !seal_eq /_Z_to_bytes_def.
      by setoid_rewrite Hσ.
    Qed.

    Theorem encodes_consistent σ t v1 v2 vs1 vs2 :
        encodes σ t v1 vs1 ** encodes σ t v2 vs2 |-- [| length vs1 = length vs2 |].
    Proof.
      rewrite !length_encodes.
      iDestruct 1 as "[%Ha %Hb]". iPureIntro. by rewrite Ha Hb.
    Qed.

    Instance cptr_proper :
      Proper (genv_leq ==> eq ==> eq) cptr.
    Proof.
      do 3 red; intros; subst.
      unfold cptr. setoid_rewrite H. reflexivity.
    Qed.

    Instance aptr_proper :
      Proper (genv_leq ==> eq ==> eq) aptr.
    Proof.
      do 3 red; intros; subst.
      unfold aptr. setoid_rewrite H. reflexivity.
    Qed.

    Instance encodes_proper :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> lentails) encodes.
    Proof.
      do 5 red. intros; subst.
      unfold encodes.
      destruct (erase_qualifiers y0); auto.
      all: destruct y1; auto.
      all: try (setoid_rewrite H; reflexivity).
      { destruct (decide (p = nullptr)); try setoid_rewrite H; auto. }
    Qed.

    Definition val_ (a : ptr) (v : val) (q : Qp) : mpred.
    refine (
      own _ghost.(ghost_heap_name) {[ a := frac (o:=leibnizO val) q v ]}).
    apply (@ghost_memG Σ); apply has_cppG.
    refine _.
    Defined.

    Lemma val_agree a v1 v2 q1 q2 :
      val_ a v1 q1 |-- val_ a v2 q2 -* ⌜v1 = v2⌝.
    Proof.
      apply bi.wand_intro_r.
      rewrite/val_ -own_op own_valid singleton_op.
      rewrite uPred.discrete_valid singleton_valid.
      by f_equiv=>/pair_valid [] _ /= /agree_op_invL'.
    Qed.

    Instance: Fractional (val_ a rv).
    Proof.
      unfold val_. red.
      intros.
      etransitivity; [ | eapply own_op ].
      eapply own_proper.
      by rewrite singleton_op frac_op.
    Qed.

    Instance: AsFractional (val_ a rv q) (fun q => val_ a rv q) q.
    Proof. constructor. reflexivity. refine _. Qed.

    Instance: Timeless (val_ a rv q).
    Proof. intros; refine _. Qed.


    Definition byte_ (a : addr) (rv : runtime_val) (q : Qp) : mpred.
    refine (
      own _ghost.(heap_name) {[ a := frac (o:=leibnizO _) q rv ]}).
    apply (@memG Σ); apply has_cppG.
    refine _.
    Defined.

    Lemma byte_agree a rv1 rv2 q1 q2 :
      byte_ a rv1 q1 |-- byte_ a rv2 q2 -* ⌜rv1 = rv2⌝.
    Proof.
      apply bi.wand_intro_r.
      rewrite/byte_ -own_op own_valid singleton_op.
      rewrite uPred.discrete_valid singleton_valid.
      by f_equiv=>/pair_valid [] _ /= /agree_op_invL'.
    Qed.

    Instance: Fractional (byte_ a rv).
    Proof.
      unfold byte_. red.
      intros.
      match goal with
      | |- _ -|- @own ?S ?O ?Z ?G ?L ** own _ ?R =>
        rewrite <- (@own_op S O Z G L R)
      end.
      eapply own_proper.
      red. red. red. simpl. red. intros.
      destruct (decide (a = i)); subst.
      { rewrite lookup_op.
        repeat rewrite lookup_insert.
        rewrite -Some_op.
        rewrite frac_op. reflexivity. }
      { rewrite lookup_op.
        repeat rewrite lookup_singleton_ne; eauto. }
    Qed.

    Instance: AsFractional (byte_ a rv q) (fun q => byte_ a rv q) q.
    Proof. constructor. reflexivity. refine _. Qed.

    Instance: Timeless (byte_ a rv q).
    Proof. intros; refine _. Qed.

    Lemma frac_valid {o : ofeT} q1 q2 (v1 v2 : o) :
      ✓ (frac q1 v1 ⋅ frac q2 v2) → ✓ (q1 + q2)%Qp ∧ v1 ≡ v2.
    Proof. by rewrite pair_valid/= =>-[]? /agree_op_inv/(inj_iff to_agree). Qed.

    Theorem byte_consistent a b b' q q' :
      byte_ a b q ** byte_ a b' q' |-- byte_ a b (q + q') ** [| b = b' |].
    Proof.
      iIntros "[Hb Hb']".
      iDestruct (byte_agree with "Hb Hb'") as %->. by iFrame.
    Qed.

    Definition bytes (a : addr) (vs : list runtime_val) (q : Qp) : mpred :=
      ([∗list] o ↦ v ∈ vs, (byte_ (a+N.of_nat o)%N v) q)%I.

    Lemma bytes_nil a q : bytes a [] q -|- emp.
    Proof. done. Qed.

    Lemma bytes_cons a v vs q :
      bytes a (v :: vs) q -|- byte_ a v q ** bytes (N.succ a) vs q.
    Proof.
      rewrite /bytes big_sepL_cons/=. do 2!f_equiv.
      - lia.
      - move=>o v'. f_equiv. lia.
    Qed.

    Lemma bytes_agree a vs1 vs2 q1 q2 :
      length vs1 = length vs2 →
      bytes a vs1 q1 ⊢ bytes a vs2 q2 -∗ ⌜vs1 = vs2⌝.
    Proof.
      revert a vs2. induction vs1 as [ |v vs1 IH]=>a vs2.
      { intros ->%symmetry%nil_length_inv. auto. }
      destruct vs2 as [ |v' vs2]; first done. intros [= Hlen].
      rewrite !bytes_cons.
      iIntros "[Hv Hvs1] [Hv' Hvs2] /=".
      iDestruct (byte_agree with "Hv Hv'") as %->.
      by iDestruct (IH _ _ Hlen with "Hvs1 Hvs2") as %->.
    Qed.

    Instance: Timeless (bytes a rv q).
    Proof. unfold bytes. intros; refine _. Qed.

    Instance: Fractional (bytes a vs).
    Proof. red. unfold bytes.
           intros.
           rewrite (@fractional_big_sepL _ _ vs (fun o v q => byte_ (a + N.of_nat o)%N v q)).
           reflexivity.
    Qed.

    Instance: AsFractional (bytes a vs q) (bytes a vs) q.
    Proof. constructor; refine _. reflexivity. Qed.

    Theorem bytes_consistent : forall q q' b b' a, length b = length b' ->
        bytes a b q ** bytes a b' q' |-- bytes a b (q + q') ** [| b = b' |].
    Proof.
      intros. iIntros "[Hb Hb']".
      iDestruct (bytes_agree with "Hb Hb'") as %->; auto.
      by iFrame "Hb Hb' %".
    Qed.

    (* heap points to *)
    Definition tptsto {σ:genv} (t : type) (q : Qp) (p : ptr) (v : val) : mpred.
    Proof.
      refine (Exists (a : option addr),
              [| has_type v t |] **
              own _ghost.(mem_inj_name) {[ p := to_agree a ]} **
              match a with
              | Some a =>
                Exists vs,
                encodes σ t v vs ** bytes a vs q
              | None => val_ p v q
              end).
      1: apply (@mem_injG Σ); apply has_cppG.
      refine _.
    Defined.

    Theorem tptsto_mono :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> (⊢)) (@tptsto).
    Proof. solve_proper. Qed.

    Theorem tptsto_proper :
      Proper (genv_eq ==> eq ==> eq ==> eq ==> eq ==> (≡)) (@tptsto).
    Proof.
      intros σ1 σ2 Hσ ??-> ??-> ??-> ??->.
      split'; eapply tptsto_mono; eauto; apply Hσ.
    Qed.

    Theorem tptsto_fractional :
      forall {σ} ty p v, Fractional (λ q, @tptsto σ ty q p v).
    Proof.
      red. intros. unfold tptsto.
      iSplit.
      - iIntros "H".
        iDestruct "H" as (a) "[#De [#Mi By]]".
        destruct a.
        + iDestruct "By" as (vs) "[#En By]".
          rewrite fractional.
          iDestruct "By" as "[L R]".
          iSplitL "L".
          * iExists (Some a); iFrame; iFrame "#". iExists vs. iFrame "#". eauto.
          * iExists (Some a); iFrame; iFrame "#". iExists vs. iFrame "#". eauto.
        + rewrite fractional.
          iDestruct "By" as "[L R]".
          iSplitL "L".
          * iExists None; iFrame; iFrame "#".
          * iExists None; iFrame; iFrame "#".
      - iIntros "[H1 H2]".
        iDestruct "H1" as (a) "[#De1 [#Mi1 By1]]".
        iDestruct "H2" as (a2) "[#De2 [#Mi2 By2]]".
        iExists a; iFrame "#".
        iDestruct (own_valid_2 with "Mi1 Mi2") as "X".
        rewrite join_singleton_eq.
        rewrite singleton_valid_at_norm.
        rewrite agree_validI.
        rewrite agree_equivI.
        iDestruct "X" as %[].
        destruct a.
        + iDestruct "By1" as (vs) "[#En1 By1]".
          iDestruct "By2" as (vs2) "[#En2 By2]".
          iDestruct (encodes_consistent with "[En1 En2]") as "%".
          iSplit; [ iApply "En1" | iApply "En2" ].
          iDestruct (bytes_consistent with "[By1 By2]") as "[Z %]"; eauto.
          iFrame.
          iExists vs. iFrame "#∗".
        + rewrite fractional. iFrame.
    Qed.
    Theorem tptsto_as_fractional :
      forall {σ} ty q p v, AsFractional (@tptsto σ ty q p v) (λ q, @tptsto σ ty q p v)%I q.
    Proof.
      intros. constructor. reflexivity.
      apply tptsto_fractional.
    Qed.

    Theorem tptsto_timeless :
      forall {σ} ty q p v, Timeless (@tptsto σ ty q p v).
    Proof.
      intros. unfold tptsto. apply _.
    Qed.

    Theorem tptsto_agree : forall σ t q1 q2 p v1 v2,
        @tptsto σ t q1 p v1 ** @tptsto σ t q2 p v2 |-- [| v1 = v2 |].
    Proof.
      iDestruct 1 as "[H1 H2]".
      iDestruct "H1" as (ma1) "(%Ht1 & Hp1 & Hv1)".
      iDestruct "H2" as (ma2) "(%Ht2 & Hp2 & Hv2)".
      iDestruct (own_valid_2 with "Hp1 Hp2") as "%Hv". iClear "Hp1 Hp2".
      move: Hv. rewrite singleton_op singleton_valid=>/agree_op_invL' ->.
      case: ma2=>[a| ]; last by iDestruct (val_agree with "Hv1 Hv2") as %->.
      iDestruct "Hv1" as (vs1) "[He1 Hb1]".
      iDestruct "Hv2" as (vs2) "[He2 Hb2]".
      iDestruct (encodes_consistent _ _ _ _ vs1 vs2 with "[He1 He2]") as %?; auto.
      iDestruct (bytes_agree with "Hb1 Hb2") as %->; auto. iClear "Hb1 Hb2".
      (* PDS: I see no way to proceed. The preceding lemma
      [encodes_agree] seems unsound wrt the present ghost state. *)
    Abort.

    Theorem tptsto_has_type : forall σ t q p v,
        @tptsto σ t q p v |-- @tptsto σ t q p v ** [| has_type v t |].
    Proof.
      unfold tptsto.
      intros.
      iIntros "H".
      iDestruct "H" as (a) "[#H X]".
      iFrame "#".
      iExists a. iFrame.
    Qed.

    (** the pointer points to the code

      note that in the presence of code-loading, function calls will
      require an extra side-condition that the code is loaded.
     *)
    Definition code_at (f : Func) (p : ptr) : mpred.
    refine (own _ghost.(code_name) {[ p := to_agree (inl (inl (inl f))) ]}).
    apply (@codeG Σ); apply has_cppG.
    all: refine _.
    Defined.

    Definition method_at (m : Method) (p : ptr) : mpred.
    refine (own _ghost.(code_name) {[ p := to_agree (inl (inl (inr m))) ]}).
    apply (@codeG Σ); apply has_cppG.
    all: refine _.
    Defined.

    Definition ctor_at (c : Ctor) (p : ptr) : mpred.
    refine (own _ghost.(code_name) {[ p := to_agree (inl (inr c)) ]}).
    apply (@codeG Σ); apply has_cppG.
    all: refine _.
    Defined.

    Definition dtor_at (d : Dtor) (p : ptr) : mpred.
    refine (own _ghost.(code_name) {[ p := to_agree (inr d) ]}).
    apply (@codeG Σ); apply has_cppG.
    all: refine _.
    Defined.

    Theorem code_at_persistent : forall f p, Persistent (@code_at f p).
    Proof. red. intros. iIntros "#X". iFrame "#". Qed.
    Theorem code_at_affine : forall f p, Affine (@code_at f p).
    Proof. red. intros. eauto. Qed.
    Theorem code_at_timeless : forall f p, Timeless (@code_at f p).
    Proof. unfold code_at. refine _. Qed.

    Theorem method_at_persistent : forall f p, Persistent (@method_at f p).
    Proof. red. intros. iIntros "#X". iFrame "#". Qed.
    Theorem method_at_affine : forall f p, Affine (@method_at f p).
    Proof. red. intros. eauto. Qed.
    Theorem method_at_timeless : forall f p, Timeless (@method_at f p).
    Proof. unfold method_at. refine _. Qed.

    Theorem ctor_at_persistent : forall f p, Persistent (@ctor_at f p).
    Proof. red. intros. iIntros "#X". iFrame "#". Qed.
    Theorem ctor_at_affine : forall f p, Affine (@ctor_at f p).
    Proof. red. intros. eauto. Qed.
    Theorem ctor_at_timeless : forall f p, Timeless (@ctor_at f p).
    Proof. unfold ctor_at. refine _. Qed.

    Theorem dtor_at_persistent : forall f p, Persistent (@dtor_at f p).
    Proof. red. intros. iIntros "#X". iFrame "#". Qed.
    Theorem dtor_at_affine : forall f p, Affine (@dtor_at f p).
    Proof. red. intros. eauto. Qed.
    Theorem dtor_at_timeless : forall f p, Timeless (@dtor_at f p).
    Proof. unfold dtor_at. refine _. Qed.

    (** physical representation of pointers
     *)
    Definition pinned_ptr (va : N) (p : ptr) : mpred.
    refine (([| p = nullptr /\ va = 0%N |] \\//
            ([| p <> nullptr |] **
                own _ghost.(mem_inj_name) {[ p := to_agree (Some va) ]}))).
    unshelve eapply mem_injG; apply has_cppG. refine _.
    Defined.

    Theorem pinned_ptr_persistent : forall va p, Persistent (pinned_ptr va p).
    Proof. apply _. Qed.
    Theorem pinned_ptr_affine : forall va p, Affine (pinned_ptr va p).
    Proof. apply _. Qed.
    Theorem pinned_ptr_timeless : forall va p, Timeless (pinned_ptr va p).
    Proof. apply _. Qed.
    Theorem pinned_ptr_unique : forall va va' p,
        pinned_ptr va p ** pinned_ptr va' p |-- bi_pure (va = va').
    Proof.
      intros. iIntros "[A B]".
      iDestruct "A" as "[[->->] | [% A]]"; iDestruct "B" as "[[%->] | [% B]]"; auto.
      iDestruct (own_valid_2 with "A B") as %Hp. iPureIntro.
      move: Hp. rewrite singleton_op singleton_valid=>/agree_op_invL'. by case.
    Qed.

    Definition type_ptr {resolve : genv} (c: type) (p : ptr) : mpred.
    Proof.
      refine (Exists (o : option addr) n,
               [| @align_of resolve c = Some n |] ** own _ghost.(mem_inj_name) {[ p := to_agree o ]} **
               match o with
               | None => ltrue
               | Some addr => [| N.modulo addr n = 0%N |]
               end).
      1: unshelve eapply mem_injG; apply has_cppG. refine _.
    Defined.

    Theorem type_ptr_persistent : forall σ p ty,
        Persistent (type_ptr (resolve:=σ) ty p).
    Proof. refine _. Qed.

    (* todo(gmm): this isn't accurate, but it is sufficient to show that the axioms are
    instantiatable. *)
    Definition identity {σ : genv} (this : globname) (most_derived : option globname)
               (q : Qp) (p : ptr) : mpred := ltrue.

    (** this allows you to forget an object identity, necessary for doing
        placement [new] over an existing object.
     *)
    Theorem identity_forget : forall σ mdc this p,
        @identity σ this (Some mdc) 1 p |-- @identity σ this None 1 p.
    Proof. rewrite /identity. eauto. Qed.

  End with_cpp.

End SimpleCPP.

Module Type SimpleCPP_INTF := SimpleCPP_BASE <+ CPP_LOGIC.
Module L : SimpleCPP_INTF := SimpleCPP.
