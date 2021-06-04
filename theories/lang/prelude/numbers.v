(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Export stdpp.numbers.
Require Export bedrock.lang.prelude.base.
Local Set Printing Coercions.	(** Readability *)

(** * Small extensions to [stdpp.numbers]. *)

(** Please follow stdpp conventions in this file in case any of this
code gets upstreamed. If code _is_ upstreamed, please remove or
deprecate the copy here.

Those conventions are not fully documented explicitly (other than by
example), but the Iris docs might be somewhat helpful:
https://gitlab.mpi-sws.org/iris/iris/-/wikis/style-guide
https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_guide.md
*)


(** * Natural numbers [nat] *)

Instance Nat_add_assoc : Assoc (=) Nat.add := Nat.add_assoc.
Instance Nat_add_comm : Comm (=) Nat.add := Nat.add_comm.
Instance Nat_add_left_id : LeftId (=) 0%nat Nat.add := Nat.add_0_l.
Instance Nat_add_right_id : RightId (=) 0%nat Nat.add := Nat.add_0_r.

Instance Nat_mul_assoc : Assoc (=) Nat.mul := Nat.mul_assoc.
Instance Nat_mul_comm : Comm (=) Nat.mul := Nat.mul_comm.
Instance Nat_mul_left_id : LeftId (=) 1%nat Nat.mul := Nat.mul_1_l.
Instance Nat_mul_right_id : RightId (=) 1%nat Nat.mul := Nat.mul_1_r.
Instance Nat_mul_left_absorb : LeftAbsorb (=) 0%nat Nat.mul := Nat.mul_0_l.
Instance Nat_mul_right_absorb : RightAbsorb (=) 0%nat Nat.mul := Nat.mul_0_r.
Instance Nat_trychotomyT : TrichotomyT Nat.lt := nat_lexico_trichotomy.

Instance Nat_min_comm: Comm eq Nat.min := Nat.min_comm.
Instance Nat_min_assoc: Assoc eq Nat.min := Nat.min_assoc.

Instance Nat_max_comm: Comm eq Nat.max := Nat.max_comm.
Instance Nat_max_assoc: Assoc eq Nat.max := Nat.max_assoc.

(** * Natural numbers [N] *)

Arguments N.ones _ : simpl never, assert.

(** cf [Z_scope] notation in [stdpp.numbers] *)
Infix "≫" := N.shiftr : N_scope.
Infix "≪" := N.shiftl : N_scope.

Instance N_add_assoc : Assoc (=) N.add := N.add_assoc.
Instance N_add_comm : Comm (=) N.add := N.add_comm.
Instance N_add_left_id : LeftId (=) 0%N N.add := N.add_0_l.
Instance N_add_right_id : RightId (=) 0%N N.add := N.add_0_r.

Instance N_mul_assoc : Assoc (=) N.mul := N.mul_assoc.
Instance N_mul_comm : Comm (=) N.mul := N.mul_comm.
Instance N_mul_left_id : LeftId (=) 1%N N.mul := N.mul_1_l.
Instance N_mul_right_id : RightId (=) 1%N N.mul := N.mul_1_r.
Instance N_mul_left_absorb : LeftAbsorb (=) 0%N N.mul := N.mul_0_l.
Instance N_mul_right_absorb : RightAbsorb (=) 0%N N.mul := N.mul_0_r.
Instance N_trychotomyT : TrichotomyT N.lt := N_lexico_trichotomy.

Instance N_min_comm: Comm eq N.min := N.min_comm.
Instance N_min_assoc: Assoc eq N.min := N.min_assoc.

Instance N_max_comm: Comm eq N.max := N.max_comm.
Instance N_max_assoc: Assoc eq N.max := N.max_assoc.

Instance N_succ_inj : Inj (=) (=) N.succ.
Proof. intros n1 n2. lia. Qed.

Instance N_divide_dec : RelDecision N.divide.
Proof.
  refine (λ a b, cast_if (decide (N.gcd a b = a)));
    abstract (by rewrite N.divide_gcd_iff').
Defined.

Lemma N_divide_add_cancel_l (n m p : N) : (n | m)%N → (n | p + m)%N → (n | p)%N.
Proof.
  (** It's odd that this isn't already in [N], so check. *)
  Fail apply N.divide_add_cancel_l. rewrite comm_L. apply N.divide_add_cancel_r.
Qed.

Lemma N2Z_inj_divide n m : (n | m)%N → (Z.of_N n | Z.of_N m)%Z.
Proof.
  (** It's odd that this isn't already in [N2Z], so check. *)
  Fail apply N2Z.inj_divide.
  intros [a ->]. rewrite N2Z.inj_mul. by exists (Z.of_N a).
Qed.

Lemma N_mul_divide_weaken_l (m n o : N) :
  (m * n | o)%N -> (m | o)%N.
Proof. case => q ->. exists (q * n)%N. lia. Qed.
Lemma N_mul_divide_weaken_r (m n o : N) :
  (m * n | o)%N -> (n | o)%N.
Proof. case => q ->. exists (q * m)%N. lia. Qed.

Definition replicateN {A} (x : A) (count : N) : list A :=
  repeat x (N.to_nat count).
#[global] Arguments replicateN : simpl never.
#[deprecated(since="2021-05-26",note="use [replicateN]")]
Notation repeatN := replicateN (only parsing).

Definition seqN (from count : N) : list N :=
  map N.of_nat (seq (N.to_nat from) (N.to_nat count)).
#[global] Arguments seqN : simpl never.

(** * Integers *)

Arguments Z.ones _ : simpl never, assert.

Instance Z_add_assoc : Assoc (=) Z.add := Z.add_assoc.
Instance Z_add_comm : Comm (=) Z.add := Z.add_comm.
Instance Z_add_left_id : LeftId (=) 0%Z Z.add := Z.add_0_l.
Instance Z_add_right_id : RightId (=) 0%Z Z.add := Z.add_0_r.

Instance Z_mul_assoc : Assoc (=) Z.mul := Z.mul_assoc.
Instance Z_mul_comm : Comm (=) Z.mul := Z.mul_comm.
Instance Z_mul_left_id : LeftId (=) 1%Z Z.mul := Z.mul_1_l.
Instance Z_mul_right_id : RightId (=) 1%Z Z.mul := Z.mul_1_r.
Instance Z_mul_left_absorb : LeftAbsorb (=) 0%Z Z.mul := Z.mul_0_l.
Instance Z_mul_right_absorb : RightAbsorb (=) 0%Z Z.mul := Z.mul_0_r.
Instance Z_trychotomyT : TrichotomyT Z.lt := Z_lexico_trichotomy.

Instance Z_min_comm: Comm eq Z.min := Z.min_comm.
Instance Z_min_assoc: Assoc eq Z.min := Z.min_assoc.

Instance Z_max_comm: Comm eq Z.max := Z.max_comm.
Instance Z_max_assoc: Assoc eq Z.max := Z.max_assoc.

Instance Z_succ_inj : Inj (=) (=) Z.succ.
Proof. intros n1 n2. lia. Qed.

Instance Z_pred_inj : Inj (=) (=) Z.pred.
Proof. intros n1 n2. lia. Qed.

(* Z.max and other operations *)
Lemma Z_max_add_distr_l (a b c : Z) :
  (a `max` b + c = (a + c) `max` (b + c))%Z.
Proof.
  Local Open Scope Z_scope.
  rewrite/Z.max.
  rewrite [a + c] Z_add_comm.
  rewrite [b + c] Z_add_comm.
  rewrite Zcompare_plus_compat.
  case_eq (a ?= b); lia.
  Local Close Scope Z_scope.
Qed.

Lemma Z_max_add_distr_r (a b c : Z) :
  (a + b `max` c = (a + b) `max` (a + c))%Z.
Proof.
  Local Open Scope Z_scope.
  rewrite/Z.max.
  rewrite Zcompare_plus_compat.
  case_eq (b ?= c); lia.
  Local Close Scope Z_scope.
Qed.

Lemma Z_pow_max_distr_r (a m n : Z) :
  (1 < a)%Z → (0 <= m)%Z -> (0 <= n)%Z ->
  (a ^ m `max` a ^ n)%Z = (a ^ (m `max` n))%Z.
Proof.
  move => apos n1nneg n2nneg.
  case_eq (m <? n)%Z.
  {
    move => ?.
    have ? : (a ^ m < a ^n)%Z
      by apply Z.pow_lt_mono_r; lia.
    rewrite !Zmax_right; lia.
  }
  move => ?.
  have ? : (a ^ n <= a ^ m)%Z
    by apply Z.pow_le_mono_r; lia.
  rewrite !Zmax_left; lia.
Qed.

(** ** Alignment to powers of two *)

(** Round [n] down to a multiple of [2^bits] *)
Definition align_dn (n bits : Z) : Z := ((n ≫ bits) ≪ bits)%Z.

(** Round [n] up to a multiple of [2^bits] *)
Definition align_up (n bits : Z) : Z := align_dn (n + Z.ones bits) bits.

(** [round_down n m d] means that [m] is the result of rounding [n]
    down to a multiple of [d]. *)
Definition round_down (n m d : Z) : Prop := ((d | m) ∧ m ≤ n < m + d)%Z.

(** [round_up n m d] means that [m] is the result of rounding [n] up
    to a multiple of [d]. *)
Definition round_up (n m d : Z) : Prop := ((d | m) ∧ n ≤ m < n + d)%Z.

Section with_Z.
  Local Open Scope Z_scope.

  (** Properties of [Z.divide] *)
  Lemma Z_divide_gcd_iff' a b : (a | b) ↔ Z.gcd a b = Z.abs a.
  Proof.
    rewrite -Z.divide_abs_l -Z.gcd_abs_l Z.divide_gcd_iff//. apply Z.abs_nonneg.
  Qed.

  Global Instance Z_divide_dec a b : Decision (a | b).
  Proof.
    refine (cast_if (decide (Z.gcd a b = Z.abs a)));
      abstract (by rewrite Z_divide_gcd_iff').
  Defined.

  (** Properties of [Z.ones] *)
  Lemma Z_ones_pow2 n : Z.ones n = 2 ^ n - 1.
  Proof. by rewrite Z.ones_equiv Z.sub_1_r. Qed.
  Lemma Z_ones_nonneg n : 0 ≤ n → 0 ≤ Z.ones n.
  Proof.
    intros. rewrite Z_ones_pow2 Z.sub_1_r -Z.lt_le_pred.
    by apply Z.pow_pos_nonneg.
  Qed.

  (** Properties of [align_dn] and [align_up] *)
  Lemma align_dn_pow2 n bits :
    0 ≤ bits → align_dn n bits = 2 ^ bits * n `div` 2 ^ bits.
  Proof.
    intros. rewrite/align_dn.
    rewrite Z.shiftl_mul_pow2// Z.shiftr_div_pow2//. lia.
  Qed.
  Lemma align_dn_divide n bits : 0 ≤ bits → (2 ^ bits | align_dn n bits).
  Proof. eexists. by apply Z.shiftl_mul_pow2. Qed.
  Lemma align_dn_below n bits : 0 ≤ bits → align_dn n bits ≤ n.
  Proof.
    intros. rewrite align_dn_pow2//. by apply Z.mul_div_le, Z.pow_pos_nonneg.
  Qed.
  Lemma align_dn_above n bits : 0 ≤ bits → n < align_dn n bits + 2 ^ bits.
  Proof.
    intros. rewrite align_dn_pow2//.
    rewrite {1}(Z.div_mod n (2 ^ bits)); last by apply Z.pow_nonzero.
    apply Z.add_lt_mono_l.
    destruct (Z.mod_pos_bound n (2 ^ bits)) as [_ ?]; last done.
    by apply Z.pow_pos_nonneg.
  Qed.
  Lemma align_dn_mono n m bits :
    0 ≤ bits → n ≤ m → align_dn n bits ≤ align_dn m bits.
  Proof.
    intros. do 2!rewrite align_dn_pow2//.
    apply Z.mul_le_mono_nonneg_l; first by apply Z.pow_nonneg.
    apply Z.div_le_mono. by apply Z.pow_pos_nonneg. done.
  Qed.
  Lemma round_down_align_dn n bits :
    0 ≤ bits → round_down n (align_dn n bits) (2 ^ bits).
  Proof.
    intros. rewrite/round_down.
    split_and?; auto using align_dn_divide, align_dn_below, align_dn_above.
  Qed.

  Lemma align_up_divide n bits : 0 ≤ bits → (2 ^ bits | align_up n bits).
  Proof. apply align_dn_divide. Qed.
  Lemma align_up_below n bits : 0 ≤ bits → n ≤ align_up n bits.
  Proof.
    intros Hbits. rewrite/align_up. set b := Z.ones bits.
    apply (Z.add_le_mono_r _ _ b). rewrite {3}/b Z_ones_pow2.
    have := align_dn_above (n + b) _ Hbits. lia.
  Qed.
  Lemma align_up_above n bits : 0 ≤ bits → align_up n bits < n + 2 ^ bits.
  Proof.
    intros Hbits. rewrite/align_up. have := align_dn_below (n + Z.ones bits) _ Hbits.
    rewrite Z_ones_pow2. have ? : 2 ^ bits ≠ 0 by exact: Z.pow_nonzero. lia.
  Qed.
  Lemma align_up_mono n m bits : 0 ≤ bits → n ≤ m → align_up n bits ≤ align_up m bits.
  Proof. intros. apply align_dn_mono; lia. Qed.
  Lemma round_up_align_up n bits : 0 ≤ bits → round_up n (align_up n bits) (2 ^ bits).
  Proof.
    intros. rewrite/round_up.
    split_and?; auto using align_up_divide, align_up_below, align_up_above.
  Qed.

  Lemma align_dn_le_up n bits : 0 ≤ bits → align_dn n bits ≤ align_up n bits.
  Proof.
    intros Hbits. rewrite/align_up. apply align_dn_mono; first done.
    have := Z_ones_nonneg _ Hbits. lia.
  Qed.
End with_Z.
