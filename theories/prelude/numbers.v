(*
 * Copyright (C) BedRock Systems Inc. 2021-2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.numbers.
Require Export bedrock.prelude.base.
Require Import bedrock.prelude.reserved_notation.
Require Import bedrock.prelude.bool.
#[local] Set Printing Coercions.	(** Readability *)

(** * Small extensions to [stdpp.numbers]. *)

(** Please follow stdpp conventions in this file in case any of this
code gets upstreamed. If code _is_ upstreamed, please remove or
deprecate the copy here.

Those conventions are not fully documented explicitly (other than by
example), but the Iris docs might be somewhat helpful:
https://gitlab.mpi-sws.org/iris/iris/-/wikis/style-guide
https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_guide.md
*)

(* TODO Maybe this should be removed *)
#[global] Coercion Z.of_N : N >-> Z.

(** * Natural numbers [nat] *)

#[global] Hint Resolve N.le_0_l | 0 : core.

#[global] Instance Nat_add_assoc : Assoc (=) Nat.add := Nat.add_assoc.
#[global] Instance Nat_add_comm : Comm (=) Nat.add := Nat.add_comm.
#[global] Instance Nat_add_left_id : LeftId (=) 0%nat Nat.add := Nat.add_0_l.
#[global] Instance Nat_add_right_id : RightId (=) 0%nat Nat.add := Nat.add_0_r.

#[global] Instance Nat_mul_assoc : Assoc (=) Nat.mul := Nat.mul_assoc.
#[global] Instance Nat_mul_comm : Comm (=) Nat.mul := Nat.mul_comm.
#[global] Instance Nat_mul_left_id : LeftId (=) 1%nat Nat.mul := Nat.mul_1_l.
#[global] Instance Nat_mul_right_id : RightId (=) 1%nat Nat.mul := Nat.mul_1_r.
#[global] Instance Nat_mul_left_absorb : LeftAbsorb (=) 0%nat Nat.mul := Nat.mul_0_l.
#[global] Instance Nat_mul_right_absorb : RightAbsorb (=) 0%nat Nat.mul := Nat.mul_0_r.
#[global] Instance Nat_trychotomyT : TrichotomyT Nat.lt := nat_lexico_trichotomy.

#[global] Instance Nat_min_comm: Comm eq Nat.min := Nat.min_comm.
#[global] Instance Nat_min_assoc: Assoc eq Nat.min := Nat.min_assoc.

#[global] Instance Nat_max_comm: Comm eq Nat.max := Nat.max_comm.
#[global] Instance Nat_max_assoc: Assoc eq Nat.max := Nat.max_assoc.

#[global] Instance Nat_land_comm : Comm eq Nat.land := Nat.land_comm.
#[global] Instance Nat_land_assoc : Assoc eq Nat.land := Nat.land_assoc.
#[global] Instance Nat_land_left_absorb : LeftAbsorb (=) 0 Nat.land := Nat.land_0_l.
#[global] Instance Nat_land_right_absorb : RightAbsorb (=) 0 Nat.land := Nat.land_0_r.

#[global] Instance Nat_lor_comm : Comm eq Nat.lor := Nat.lor_comm.
#[global] Instance Nat_lor_assoc : Assoc eq Nat.lor := Nat.lor_assoc.
#[global] Instance Nat_lor_left_id : LeftId (=) 0 Nat.lor := Nat.lor_0_l.
#[global] Instance Nat_lor_right_id : RightId (=) 0 Nat.lor := Nat.lor_0_r.

(* Non-symmetric *)
#[global] Instance Nat_shiftl_left_absorb : LeftAbsorb (=) 0 Nat.shiftl := Nat.shiftl_0_l.
#[global] Instance Nat_shiftl_right_id : RightId (=) 0 Nat.shiftl := Nat.shiftl_0_r.

#[global] Instance Nat_shiftr_left_absorb : LeftAbsorb (=) 0 Nat.shiftr := Nat.shiftr_0_l.
#[global] Instance Nat_shiftr_right_id : RightId (=) 0 Nat.shiftr := Nat.shiftr_0_r.

(** * Natural numbers [N] *)

Arguments N.ones _ : simpl never, assert.

Infix "`lor`" := N.lor : N_scope.
Infix "`land`" := N.land : N_scope.
Infix "`ldiff`" := N.ldiff : N_scope.

(** cf [Z_scope] notation in [stdpp.numbers] *)
Infix "≫" := N.shiftr : N_scope.
Infix "≪" := N.shiftl : N_scope.

#[global] Instance N_add_assoc : Assoc (=) N.add := N.add_assoc.
#[global] Instance N_add_comm : Comm (=) N.add := N.add_comm.
#[global] Instance N_add_left_id : LeftId (=) 0%N N.add := N.add_0_l.
#[global] Instance N_add_right_id : RightId (=) 0%N N.add := N.add_0_r.

#[global] Instance N_mul_assoc : Assoc (=) N.mul := N.mul_assoc.
#[global] Instance N_mul_comm : Comm (=) N.mul := N.mul_comm.
#[global] Instance N_mul_left_id : LeftId (=) 1%N N.mul := N.mul_1_l.
#[global] Instance N_mul_right_id : RightId (=) 1%N N.mul := N.mul_1_r.
#[global] Instance N_mul_left_absorb : LeftAbsorb (=) 0%N N.mul := N.mul_0_l.
#[global] Instance N_mul_right_absorb : RightAbsorb (=) 0%N N.mul := N.mul_0_r.
#[global] Instance N_trychotomyT : TrichotomyT N.lt := N_lexico_trichotomy.

#[global] Instance N_min_comm: Comm eq N.min := N.min_comm.
#[global] Instance N_min_assoc: Assoc eq N.min := N.min_assoc.

#[global] Instance N_max_comm: Comm eq N.max := N.max_comm.
#[global] Instance N_max_assoc: Assoc eq N.max := N.max_assoc.

#[global] Instance N_land_comm : Comm eq N.land := N.land_comm.
#[global] Instance N_land_assoc : Assoc eq N.land := N.land_assoc.
#[global] Instance N_land_left_absorb : LeftAbsorb (=) 0%N N.land := N.land_0_l.
#[global] Instance N_land_right_absorb : RightAbsorb (=) 0%N N.land := N.land_0_r.

#[global] Instance N_lor_comm : Comm eq N.lor := N.lor_comm.
#[global] Instance N_lor_assoc : Assoc eq N.lor := N.lor_assoc.
#[global] Instance N_lor_left_id : LeftId (=) 0%N N.lor := N.lor_0_l.
#[global] Instance N_lor_right_id : RightId (=) 0%N N.lor := N.lor_0_r.

(* Non-symmetric *)
#[global] Instance N_shiftl_left_absorb : LeftAbsorb (=) 0%N N.shiftl := N.shiftl_0_l.
#[global] Instance N_shiftl_right_id : RightId (=) 0%N N.shiftl := N.shiftl_0_r.

#[global] Instance N_shiftr_left_absorb : LeftAbsorb (=) 0%N N.shiftr := N.shiftr_0_l.
#[global] Instance N_shiftr_right_id : RightId (=) 0%N N.shiftr := N.shiftr_0_r.

#[global] Instance N_succ_inj : Inj (=) (=) N.succ.
Proof. intros n1 n2. lia. Qed.

Lemma N_minE {n m : N} : (n <= m)%N -> (n `min` m)%N = n.
Proof. case: (N.min_spec n m)=> [[]|[]]//. lia. Qed.

(** Shorter and more memorable name. *)
Lemma N_ext n m : (∀ i, N.testbit n i = N.testbit m i) -> n = m.
Proof. apply N.bits_inj_iff. Qed.
Lemma N_ext_iff n m : (∀ i, N.testbit n i = N.testbit m i) <-> n = m.
Proof. apply N.bits_inj_iff. Qed.

(** Misc cancellation lemmas for odd operators *)
Lemma N_succ_pos_pred p : N.succ_pos (Pos.pred_N p) = p.
Proof. rewrite /N.succ_pos. case E: Pos.pred_N=>[|p']; lia. Qed.

Lemma Pos_of_S i :
  Pos.of_nat (S i) = N.succ_pos (N.of_nat i).
Proof. case: i => [//|i]. rewrite Nat2Pos.inj_succ //= Pos.of_nat_succ //. Qed.

Lemma pred_nat_succ n :
  Nat.pred (Pos.to_nat (N.succ_pos n)) = N.to_nat n.
Proof. case: n => //= p. lia. Qed.

(** [N.of_nat] is monotone re [<]. *)
Lemma N_of_nat_lt_mono (i j : nat) :
  (i < j)%nat ↔ (N.of_nat i < N.of_nat j)%N.
Proof. rewrite /N.lt -Nat2N.inj_compare. apply nat_compare_lt. Qed.

(** [N.of_nat] is monotone re [≤]. *)
Lemma N_of_nat_le_mono (i j : nat) :
  (i ≤ j)%nat ↔ (N.of_nat i ≤ N.of_nat j)%N.
Proof. rewrite /N.le -Nat2N.inj_compare. apply nat_compare_le. Qed.

(** Adapter [N.eqb] into [bool_decide]. *)
Lemma N_eqb_bool_decide (m n : N) : N.eqb m n = bool_decide (m = n).
Proof.
  by rewrite -(bool_decide_ext _ _ (N.eqb_eq _ _)) bool_decide_bool_eq.
Qed.

Lemma N_leb_bool_decide (m n : N) : N.leb m n = bool_decide (m ≤ n)%N.
Proof.
  by rewrite -(bool_decide_ext _ _ (N.leb_le _ _)) bool_decide_bool_eq.
Qed.

(** Rephrase spec for [N.ones] using [bool_decide]. *)
Lemma N_ones_spec (n m : N) :
  N.testbit (N.ones n) m = bool_decide (m < n)%N.
Proof.
  case_bool_decide; [exact: N.ones_spec_low|].
  apply N.ones_spec_high. lia.
Qed.

Lemma N_setbit_bool_decide (a n m : N) :
  N.testbit (N.setbit a n) m = bool_decide (n = m) || N.testbit a m.
Proof. by rewrite N.setbit_eqb N_eqb_bool_decide. Qed.

(* monotonicity of land *)
Lemma N_land_mono_r (a b : N) : (a `land` b <= a)%N.
Proof.
  apply: N.ldiff_le; rewrite -N.bits_inj_iff=>n.
  rewrite N.ldiff_spec N.land_spec andb_comm.
  by case: (N.testbit a n).
Qed.

Lemma N_land_mono_l (a b : N) : (a `land` b <= b)%N.
Proof. by rewrite N.land_comm; apply: N_land_mono_r. Qed.

(* monotonicity of lor in the right arg *)
Lemma N_lor_mono_r (a b : N) :
  (a <= b)%N -> (a `lor` b <= N.ones (N.log2 b + 1))%N.
Proof.
  move=>Hle.
  apply: N.ldiff_le; rewrite -N.bits_inj_iff=>n.
  rewrite N.ldiff_spec N.lor_spec andb_comm.
  case: (N.leb_spec (N.log2 b + 1) n);
    first case: (N.eqb_spec (N.log2 b + 1) n).
  - move=><-_.
    rewrite N.ones_spec_high //= !N.bits_above_log2 //.
    by apply: N.lt_add_pos_r.
    apply: N.le_lt_trans; last by apply: N.lt_add_pos_r.
    by apply: N.log2_le_mono.

  - rewrite N.add_1_r N.le_succ_l=>??.
    rewrite N.ones_spec_high //=; last by rewrite N.le_succ_l.
    rewrite !N.bits_above_log2 //.
    by apply: N.le_lt_trans; first apply: N.log2_le_mono.
  - by move=>?; rewrite N.ones_spec_low.
Qed.

(* monotonicity of lxor in the right arg *)
Lemma N_lxor_mono_aux (a b : N) :
  (a <= b)%N -> (N.lxor a b <= N.ones (N.log2 b + 1))%N.
Proof.
  move=>Hle.
  apply: N.ldiff_le; rewrite -N.bits_inj_iff=>n.
  rewrite N.ldiff_spec N.lxor_spec andb_comm.
  case: (N.leb_spec (N.log2 b + 1) n);
    first case: (N.eqb_spec (N.log2 b + 1) n).
  - move=><-_.
    rewrite N.ones_spec_high //= !N.bits_above_log2 //.
    by apply: N.lt_add_pos_r.
    apply: N.le_lt_trans; last by apply: N.lt_add_pos_r.
    by apply: N.log2_le_mono.

  - rewrite N.add_1_r N.le_succ_l=>??.
    rewrite N.ones_spec_high //=; last by rewrite N.le_succ_l.
    rewrite !N.bits_above_log2 //.
    by apply: N.le_lt_trans; first apply: N.log2_le_mono.
  - by move=>?; rewrite N.ones_spec_low.
Qed.

Lemma N_le_pred_lt: ∀ n m : N,
    (0 < n)%N
    -> (n ≤ m)%N -> (BinNat.N.pred n < m)%N.
Proof. lia. Qed.

(* pow2 bound on lxor *)
Lemma N_lxor_lt_pow2_aux (a b c : N) :
  (a <= b)%N
  -> (0 < c)%N
  -> (b < 2 ^ c)%N -> (N.lxor a b < 2 ^ c)%N.
Proof.
  move=>? ? Hlt.
  apply: N.le_lt_trans; first by apply: N_lxor_mono_aux.
  rewrite N.ones_equiv.
  apply: N_le_pred_lt; first by lia.
  apply: N.pow_le_mono_r; first done.

  case: (N.leb_spec b 0).
  - move=>/N.le_0_r->.
    rewrite N.add_0_l; lia.
  - move=>?.
    by rewrite N.add_1_r N.le_succ_l -N.log2_lt_pow2 //.
Qed.

Lemma N_lxor_lt_pow2 (a b c : N) :
  (0 < c)%N
  -> (a < 2 ^ c)%N
  -> (b < 2 ^ c)%N -> (N.lxor a b < 2 ^ c)%N.
Proof.
  case: (N.leb_spec a b).
  - by move=>*; apply: N_lxor_lt_pow2_aux.
  - rewrite N.lxor_comm.
    by move=>/N.lt_le_incl *; apply: N_lxor_lt_pow2_aux.
Qed.

Lemma N2Z_land (a b : N) : Z.land (Z.of_N a) (Z.of_N b) = Z.of_N (N.land a b).
Proof. by case: a; case: b. Qed.

Lemma N2Z_lor (a b : N) : Z.lor (Z.of_N a) (Z.of_N b) = Z.of_N (N.lor a b).
Proof. by case: a; case: b. Qed.

Lemma N2Z_shiftl (a n : N) : Z.shiftl (Z.of_N a) (Z.of_N n) = Z.of_N (N.shiftl a n).
Proof.
  apply: Z.bits_inj'=>idx Hidx.
  rewrite Z.shiftl_spec //= -{2}(Z2N.id idx) //= Z.testbit_of_N.
  move: (Z.lt_ge_cases idx (Z.of_N n)) =>[ Hle | Hlt ].
  - rewrite N.shiftl_spec_low; last by rewrite N2Z.inj_lt Z2N.id.
    by apply: Z.testbit_neg_r; rewrite Z.lt_sub_0.
  - rewrite N.shiftl_spec_high; try by rewrite N2Z.inj_le Z2N.id.
    have->: (idx - Z.of_N n = Z.of_N (Z.to_N idx - n))%Z; last by apply: Z.testbit_of_N.
    by rewrite N2Z.inj_sub ?Z2N.id //= N2Z.inj_le Z2N.id.
Qed.

Lemma N2Z_shiftr (a n : N) : Z.shiftr (Z.of_N a) (Z.of_N n) = Z.of_N (N.shiftr a n).
Proof.
  apply: Z.bits_inj'=>idx Hidx.
  rewrite Z.shiftr_spec //= -{2}(Z2N.id idx) //= Z.testbit_of_N.
  rewrite N.shiftr_spec //= -Z.testbit_of_N.
  by f_equal; rewrite N2Z.inj_add Z2N.id.
Qed.

Lemma N2Z_lxor (a b : N) : Z.lxor (Z.of_N a) (Z.of_N b) = Z.of_N (N.lxor a b).
Proof. by case: a; case: b. Qed.

Lemma N2Z_lnot_trim (w : N) : Z.modulo (Z.lnot 0) (Z.pow 2 (Z.of_N w)) = Z.of_N (N.lnot 0 w).
Proof.
  rewrite Z.lnot_0; apply: Z.bits_inj'=>idx Hidx.
  move: (Z.lt_ge_cases idx w)=>[Hlt|Hle].
  - rewrite Z.mod_pow2_bits_low //= Z.bits_opp //= -Z.sub_1_r //= Z.bits_0.
    by rewrite Z.testbit_of_N' //= N.ones_spec_low //= N2Z.inj_lt Z2N.id.
  - rewrite Z.mod_pow2_bits_high //=; last by split=>//=; case w.
    by rewrite Z.testbit_of_N' //= N.ones_spec_high //= N2Z.inj_le Z2N.id.
Qed.

Lemma N2Z_lnot (a w : N) : (a < 2 ^ w)%N -> Z.modulo (Z.lnot a) (Z.pow 2 (Z.of_N w)) = Z.of_N (N.lnot a w).
Proof.
  move=>Hu; apply: Z.bits_inj'=>idx Hidx.
  move: (Z.lt_ge_cases idx w) =>[ Hle | Hlt ].
  - rewrite Z.mod_pow2_bits_low //= Z.testbit_of_N' //= Z.lnot_spec //=.
    rewrite N.lnot_spec_low; last by rewrite N2Z.inj_lt Z2N.id.
    by rewrite Z.testbit_of_N'.
  - move: (N.eq_0_gt_0_cases a)=>[->|Hu']; first by rewrite N2Z_lnot_trim.
    rewrite Z.mod_pow2_bits_high; last by split=>//=; apply/N2Z.is_nonneg.
    rewrite Z.testbit_of_N' //=.
    rewrite N.lnot_spec_high; last by rewrite N2Z.inj_le Z2N.id.
    rewrite N.bits_above_log2 //=.
    apply:N.lt_le_trans; last by rewrite N2Z.inj_le Z2N.id.
    by rewrite -N.log2_lt_pow2.
Qed.

#[global] Instance N_divide_dec : RelDecision N.divide.
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

#[global] Instance N_b2n_inj : Inj eq eq N.b2n := N.b2n_inj.

Lemma N_b2n_0 b : N.b2n b = 0%N <-> ~b.
Proof. case: b; naive_solver. Qed.

Lemma N_b2n_1 b : N.b2n b = 1%N <-> b.
Proof. by case: b. Qed.

(** [pow2N n]'s output term has size exponential in [n], and simplifying
callers is even worse; so we seal it. *)
Definition pow2N_def (n : N) : N := 2^n.
Definition pow2N_aux : seal pow2N_def. Proof. by eexists. Qed.
Definition pow2N := pow2N_aux.(unseal).
Definition pow2N_eq : pow2N = _ := pow2N_aux.(seal_eq).
#[global] Hint Opaque pow2N : typeclass_instances.

Lemma pow2N_spec n : pow2N n = (2 ^ n)%N.
Proof. by rewrite pow2N_eq. Qed.

(** * Integers *)

Infix "`lor`" := Z.lor : Z_scope.
Infix "`land`" := Z.land : Z_scope.
Infix "`ldiff`" := Z.ldiff : Z_scope.

Arguments Z.ones _ : simpl never, assert.

#[global] Instance Z_add_assoc : Assoc (=) Z.add := Z.add_assoc.
#[global] Instance Z_add_comm : Comm (=) Z.add := Z.add_comm.
#[global] Instance Z_add_left_id : LeftId (=) 0%Z Z.add := Z.add_0_l.
#[global] Instance Z_add_right_id : RightId (=) 0%Z Z.add := Z.add_0_r.

#[global] Instance Z_mul_assoc : Assoc (=) Z.mul := Z.mul_assoc.
#[global] Instance Z_mul_comm : Comm (=) Z.mul := Z.mul_comm.
#[global] Instance Z_mul_left_id : LeftId (=) 1%Z Z.mul := Z.mul_1_l.
#[global] Instance Z_mul_right_id : RightId (=) 1%Z Z.mul := Z.mul_1_r.
#[global] Instance Z_mul_left_absorb : LeftAbsorb (=) 0%Z Z.mul := Z.mul_0_l.
#[global] Instance Z_mul_right_absorb : RightAbsorb (=) 0%Z Z.mul := Z.mul_0_r.
#[global] Instance Z_trychotomyT : TrichotomyT Z.lt := Z_lexico_trichotomy.

#[global] Instance Z_min_comm: Comm eq Z.min := Z.min_comm.
#[global] Instance Z_min_assoc: Assoc eq Z.min := Z.min_assoc.

#[global] Instance Z_max_comm: Comm eq Z.max := Z.max_comm.
#[global] Instance Z_max_assoc: Assoc eq Z.max := Z.max_assoc.

#[global] Instance Z_land_comm : Comm eq Z.land := Z.land_comm.
#[global] Instance Z_land_assoc : Assoc eq Z.land := Z.land_assoc.
#[global] Instance Z_land_left_absorb : LeftAbsorb (=) 0%Z Z.land := Z.land_0_l.
#[global] Instance Z_land_right_absorb : RightAbsorb (=) 0%Z Z.land := Z.land_0_r.

#[global] Instance Z_lor_comm : Comm eq Z.lor := Z.lor_comm.
#[global] Instance Z_lor_assoc : Assoc eq Z.lor := Z.lor_assoc.

#[global] Instance Z_lor_left_id : LeftId (=) 0%Z Z.lor := Z.lor_0_l.
#[global] Instance Z_lor_right_id : RightId (=) 0%Z Z.lor := Z.lor_0_r.

(* Non-symmetric *)
#[global] Instance Z_shiftl_left_absorb : LeftAbsorb (=) 0%Z Z.shiftl := Z.shiftl_0_l.
#[global] Instance Z_shiftl_right_id : RightId (=) 0%Z Z.shiftl := Z.shiftl_0_r.

#[global] Instance Z_shiftr_left_absorb : LeftAbsorb (=) 0%Z Z.shiftr := Z.shiftr_0_l.
#[global] Instance Z_shiftr_right_id : RightId (=) 0%Z Z.shiftr := Z.shiftr_0_r.

#[global] Instance Z_succ_inj : Inj (=) (=) Z.succ.
Proof. intros n1 n2. lia. Qed.

#[global] Instance Z_pred_inj : Inj (=) (=) Z.pred.
Proof. intros n1 n2. lia. Qed.

(** Shorter and more memorable name. *)
Lemma Z_ext n m : (∀ i, Z.testbit n i = Z.testbit m i) -> n = m.
Proof. apply Z.bits_inj_iff. Qed.
Lemma Z_ext_iff n m : (∀ i, Z.testbit n i = Z.testbit m i) <-> n = m.
Proof. apply Z.bits_inj_iff. Qed.

(* Z.max and other operations *)
Lemma Z_max_add_distr_l (a b c : Z) :
  (a `max` b + c = (a + c) `max` (b + c))%Z.
Proof.
  #[local] Open Scope Z_scope.
  rewrite/Z.max.
  rewrite [a + c] Z_add_comm.
  rewrite [b + c] Z_add_comm.
  rewrite Zcompare_plus_compat.
  case_eq (a ?= b); lia.
  #[local] Close Scope Z_scope.
Qed.

Lemma Z_max_add_distr_r (a b c : Z) :
  (a + b `max` c = (a + b) `max` (a + c))%Z.
Proof.
  #[local] Open Scope Z_scope.
  rewrite/Z.max.
  rewrite Zcompare_plus_compat.
  case_eq (b ?= c); lia.
  #[local] Close Scope Z_scope.
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

#[global] Instance Z_b2z_inj : Inj eq eq Z.b2z := Z.b2z_inj.

Lemma Z_b2z_0 b : Z.b2z b = 0%Z <-> ~b.
Proof. case: b; naive_solver. Qed.

Lemma Z_b2z_1 b : Z.b2z b = 1%Z <-> b.
Proof. by case: b. Qed.

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
  #[local] Open Scope Z_scope.

  (** Properties of [Z.divide] *)
  Lemma Z_divide_gcd_iff' a b : (a | b) ↔ Z.gcd a b = Z.abs a.
  Proof.
    rewrite -Z.divide_abs_l -Z.gcd_abs_l Z.divide_gcd_iff//. apply Z.abs_nonneg.
  Qed.

  #[global] Instance Z_divide_dec a b : Decision (a | b).
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

(** [Qp] *)

Module Qp.
  Export stdpp.numbers.Qp.
  #[local] Open Scope Qp_scope.

  #[global] Instance mul_left_id : LeftId (=) 1 Qp.mul := Qp.mul_1_l.
  #[global] Instance mul_right_id : RightId (=) 1 Qp.mul := Qp.mul_1_r.
  #[global] Instance div_right_id : RightId (=) 1 Qp.div := Qp.div_1.

  Lemma mul_div a b c d : (a/b) * (c/d) = (a * c) / (b * d).
  Proof.
    rewrite /Qp.div. rewrite Qp.inv_mul_distr.
    rewrite -!assoc_L. f_equal. rewrite comm_L -assoc_L. f_equal.
    by rewrite comm_L.
  Qed.

  Lemma mul_2_2 : 2 * 2 = 4.
  Proof. compute_done. Qed.

  Lemma div_4 q : q / 4 + q / 4 = q / 2.
  Proof.
    rewrite -Qp.div_add_distr Qp.add_diag -Qp.mul_2_2.
    by rewrite Qp.div_mul_cancel_l.
  Qed.

  Lemma third_two_thirds : 1/3 + 2/3 = 1.
  Proof. exact: (bool_decide_unpack _). Qed.
  Lemma two_thirds_third : 2/3 + 1/3 = 1.
  Proof. compute_done. Qed.

  Lemma quarter_half : 1/4 + 1/2 = 3/4.
  Proof. compute_done. Qed.

  Lemma half_half_quarter : (1/2/2 = 1/4)%Qp.
  Proof. compute_done. Qed.

End Qp.
#[deprecated(since="20221223", note="use [Qp.mul_left_id]")]
Notation Qp_mul_left_id := Qp.mul_left_id (only parsing).
#[deprecated(since="20221223", note="use [Qp.mul_right_id]")]
Notation Qp_mul_right_id := Qp.mul_right_id (only parsing).
#[deprecated(since="20221223", note="use [Qp.div_right_id]")]
Notation Qp_div_right_id := Qp.div_right_id (only parsing).


(** ** [N_to_Qp] *)

Definition N_to_Qp (n : N) : Qp :=
  if n is Npos p
  then pos_to_Qp p
  else 1%Qp.	(** dummy *)

Section with_N_to_Qp.
  #[local] Open Scope N_scope.
  #[local] Infix "<=" := Qp.le : Qp_scope.

  Lemma N_to_Qp_1 : N_to_Qp 1 = 1%Qp.
  Proof. done. Qed.

  Lemma N_to_Qp_pos p : N_to_Qp (N.pos p) = pos_to_Qp p.
  Proof. done. Qed.

  Lemma N_to_Qp_succ n : n <> 0 -> N_to_Qp (N.succ n) = (N_to_Qp n + 1)%Qp.
  Proof.
    destruct n; [done|]=>_ /=. by rewrite -Pos.add_1_r pos_to_Qp_add.
  Qed.

  Lemma N_to_Qp_inj n m :
    n <> 0 -> m <> 0 -> N_to_Qp n = N_to_Qp m -> n = m.
  Proof.
    destruct n; [done|]. destruct m; [done|]=>_ _ ?.
    f_equal. exact: pos_to_Qp_inj.
  Qed.

  Lemma N_to_Qp_inj_iff n m :
    n <> 0 -> m <> 0 -> N_to_Qp n = N_to_Qp m <-> n = m.
  Proof. naive_solver auto using N_to_Qp_inj. Qed.

  Lemma N_to_Qp_inj_le n m :
    n <> 0 -> m <> 0 -> n <= m <-> (N_to_Qp n <= N_to_Qp m)%Qp.
  Proof.
    destruct n; [done|]. destruct m; [done|]=>_ _.
    by rewrite !N_to_Qp_pos -pos_to_Qp_inj_le.
  Qed.

  Lemma N_to_Qp_inj_lt n m :
    n <> 0 -> m <> 0 -> n < m <-> (N_to_Qp n < N_to_Qp m)%Qp.
  Proof.
    destruct n; [done|]. destruct m; [done|]=>_ _.
    by rewrite !N_to_Qp_pos -pos_to_Qp_inj_lt.
  Qed.

  Lemma N_to_Qp_add n m :
    n <> 0 -> m <> 0 -> (N_to_Qp n + N_to_Qp m)%Qp = N_to_Qp (n + m).
  Proof.
    destruct n; [done|]. destruct m; [done|]=>_ _.
    by rewrite !N_to_Qp_pos pos_to_Qp_add.
  Qed.

  Lemma N_to_Qp_mul n m :
    n <> 0 -> m <> 0 -> (N_to_Qp n * N_to_Qp m)%Qp = N_to_Qp (n * m).
  Proof.
    destruct n; [done|]. destruct m; [done|]=>_ _.
    by rewrite !N_to_Qp_pos pos_to_Qp_mul.
  Qed.
End with_N_to_Qp.
