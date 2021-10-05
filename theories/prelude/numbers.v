(*
 * Copyright (C) BedRock Systems Inc. 2021
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.numbers.
Require Export bedrock.prelude.base.
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

Instance Nat_land_comm : Comm eq Nat.land := Nat.land_comm.
Instance Nat_land_assoc : Assoc eq Nat.land := Nat.land_assoc.

Instance Nat_lor_comm : Comm eq Nat.lor := Nat.lor_comm.
Instance Nat_lor_assoc : Assoc eq Nat.lor := Nat.lor_assoc.

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

Instance N_land_comm : Comm eq N.land := N.land_comm.
Instance N_land_assoc : Assoc eq N.land := N.land_assoc.

Instance N_lor_comm : Comm eq N.lor := N.lor_comm.
Instance N_lor_assoc : Assoc eq N.lor := N.lor_assoc.

Instance N_succ_inj : Inj (=) (=) N.succ.
Proof. intros n1 n2. lia. Qed.

Lemma N_succ_pos_pred p : N.succ_pos (Pos.pred_N p) = p.
Proof. rewrite /N.succ_pos. case E: Pos.pred_N=>[|p']; lia. Qed.

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

Definition seqN (from count : N) : list N :=
  N.of_nat <$> (seq (N.to_nat from) (N.to_nat count)).
#[global] Arguments seqN : simpl never.

Section seqN.
  #[local] Open Scope N_scope.

  Lemma cons_seqN len start :
    start :: seqN (N.succ start) len = seqN start (N.succ len).
  Proof. by rewrite /seqN !N2Nat.inj_succ -cons_seq fmap_cons N2Nat.id. Qed.

  (* Lifts stdpp's [seq_S_end_app] aka stdlib's [seq_S] *)
  Lemma seqN_S_end_app j n : seqN j (N.succ n) = seqN j n ++ [j + n].
  Proof.
    rewrite /seqN !N2Nat.inj_succ seq_S_end_app fmap_app /=.
    by rewrite -N2Nat.inj_add N2Nat.id.
  Qed.

  Lemma cons_seqN' [len start] sstart :
    sstart = N.succ start ->
    start :: seqN sstart len = seqN start (N.succ len).
  Proof. move->. apply cons_seqN. Qed.

  Lemma seqN_S_end_app' [w n] sn :
    sn = N.succ n ->
    seqN w sn = seqN w n ++ [w + n].
  Proof. move->. apply seqN_S_end_app. Qed.
End seqN.

Definition replicateN {A} (count : N) (x : A) : list A :=
  replicate (N.to_nat count) x.
#[global] Arguments replicateN : simpl never.
#[deprecated(since="2021-05-26",note="use [replicateN]")]
Notation repeatN := (flip replicateN) (only parsing).

Definition dropN {A} n := drop (A := A) (N.to_nat n).
Definition takeN {A} n := take (A := A) (N.to_nat n).
Definition lengthN {A} xs := N.of_nat (length (A := A) xs).
Definition resizeN {A} n := resize (A := A) (N.to_nat n).
Definition rotateN {A} n xs :=
  dropN (A := A) (n mod lengthN xs) xs ++ takeN (A := A) (n mod lengthN xs) xs.

Section listN.
  #[local] Open Scope N_scope.
  Context {A : Type}.

  Lemma N2Nat_inj_le n m :
    n ≤ m ->
    (N.to_nat n <= N.to_nat m)%nat.
  Proof. lia. Qed.

  Implicit Type (x : A) (n m : N).

  (* TODO: extend the theory of [lengthN], we have few lemmas here. *)
  Lemma nil_lengthN :
    lengthN (A := A) [] = 0.
  Proof. done. Qed.

  Lemma cons_lengthN x xs :
    lengthN (x :: xs) = N.succ (lengthN xs).
  Proof. by rewrite /lengthN cons_length Nat2N.inj_succ. Qed.

  (* Lift all theory about [drop] and [replicate] interaction. *)
  Lemma dropN_replicateN n m x :
    dropN n (replicateN m x) = replicateN (m - n) x.
  Proof. by rewrite /dropN /replicateN drop_replicate N2Nat.inj_sub. Qed.

  Lemma dropN_replicateN_plus n m x :
    dropN n (replicateN (n + m) x) = replicateN m x.
  Proof. by rewrite /dropN /replicateN N2Nat.inj_add drop_replicate_plus. Qed.

  (* Lift all theory about [take] and [replicate] interaction. *)
  Lemma takeN_replicateN n m x :
    takeN n (replicateN m x) = replicateN (n `min` m) x.
  Proof. by rewrite /takeN /replicateN take_replicate N2Nat.inj_min. Qed.

  Lemma takeN_replicateN_plus n m x :
    takeN n (replicateN (n + m) x) = replicateN n x.
  Proof. by rewrite /takeN /replicateN N2Nat.inj_add take_replicate_plus. Qed.

  Lemma resizeN_spec l n x :
    resizeN n x l = takeN n l ++ replicateN (n - lengthN l) x.
  Proof.
    by rewrite /resizeN /replicateN resize_spec !N2Nat.inj_sub Nat2N.id.
  Qed.

  (* Part of the theory of [resize], it's rather large. *)
  Lemma resizeN_all l x : resizeN (lengthN l) x l = l.
  Proof. by rewrite /resizeN /lengthN Nat2N.id resize_all. Qed.

  Lemma resizeN_0 l x : resizeN 0 x l = [].
  Proof. by rewrite /resizeN resize_0. Qed.

  Lemma resizeN_lengthN l n x :
    lengthN (resizeN n x l) = n.
  Proof. by rewrite /lengthN /resizeN /= resize_length N2Nat.id. Qed.

  Lemma resizeN_nil n x : resizeN n x [] = replicateN n x.
  Proof. apply resize_nil. Qed.

  Lemma resizeN_replicateN x n m:
    resizeN n x (replicateN m x) = replicateN n x.
  Proof. by rewrite /resizeN /replicateN resize_replicate. Qed.

  Lemma resizeN_idemp l n x :
    resizeN n x (resizeN n x l) = resizeN n x l.
  Proof. apply resize_idemp. Qed.

  (* Lift all theory about [drop] and [resize] interaction. *)
  Lemma dropN_resizeN_plus l m n x :
    dropN n (resizeN (n + m) x l) = resizeN m x (dropN n l).
  Proof. by rewrite /dropN /resizeN N2Nat.inj_add drop_resize_plus. Qed.

  Lemma dropN_resizeN_le l n m x :
    n <= m →
    dropN n (resizeN m x l) = resizeN (m - n) x (dropN n l).
  Proof.
    move=> /N2Nat_inj_le Hle.
    by rewrite /dropN /resizeN drop_resize_le // N2Nat.inj_sub.
  Qed.

  Lemma resizeN_plusN l n m x :
    resizeN (n + m) x l = resizeN n x l ++ resizeN m x (dropN n l).
  Proof. by rewrite /resizeN /dropN N2Nat.inj_add resize_plus. Qed.

  (* Lift all theory about [take] and [resize] interaction. *)
  Lemma takeN_resizeN_eq l n x :
    takeN n (resizeN n x l) = resizeN n x l.
  Proof. apply take_resize_eq. Qed.

  Lemma resizeN_takeN_eq l n x :
    resizeN n x (takeN n l) = resizeN n x l.
  Proof. apply resize_take_eq. Qed.

  Lemma takeN_resizeN l n m x :
    takeN n (resizeN m x l) = resizeN (n `min` m) x l.
  Proof. by rewrite /takeN /resizeN take_resize N2Nat.inj_min. Qed.

  Lemma takeN_resizeN_plus l n m x :
    takeN n (resizeN (n + m) x l) = resizeN n x l.
  Proof. by rewrite /takeN /resizeN N2Nat.inj_add take_resize_plus. Qed.

  Lemma to_nat_lengthN (l : list A) :
    N.to_nat (lengthN l) = length l.
  Proof. by rewrite /lengthN Nat2N.id. Qed.

  Lemma resizeN_le l n x :
    n <= lengthN l ->
    resizeN n x l = takeN n l.
  Proof. move=> /N2Nat_inj_le. rewrite to_nat_lengthN. apply resize_le. Qed.

  Lemma takeN_resizeN_le l n m x  :
    n ≤ m →
    takeN n (resizeN m x l) = resizeN n x l.
  Proof. move=> /N2Nat_inj_le. apply take_resize_le. Qed.

  Lemma resizeN_takeN_le l n m x :
    (n <= m) → resizeN n x (takeN m l) = resizeN n x l.
  Proof. move=> /N2Nat_inj_le. apply resize_take_le. Qed.

  (* resizeN_spec is above *)
End listN.

(** [pow2N n]'s output term has size exponential in [n], and simplifying
callers is even worse; so we seal it. *)
Definition pow2N_def (n : N) : N := 2^n.
Definition pow2N_aux : seal pow2N_def. Proof. by eexists. Qed.
Definition pow2N := pow2N_aux.(unseal).
Definition pow2N_eq : pow2N = _ := pow2N_aux.(seal_eq).
#[global] Hint Opaque pow2N : typeclass_instances.

#[deprecated(note="Use [pow2N]")]
Notation pow2 := pow2N (only parsing).

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

Instance Z_land_comm : Comm eq Z.land := Z.land_comm.
Instance Z_land_assoc : Assoc eq Z.land := Z.land_assoc.

Instance Z_lor_comm : Comm eq Z.lor := Z.lor_comm.
Instance Z_lor_assoc : Assoc eq Z.lor := Z.lor_assoc.

Instance Z_succ_inj : Inj (=) (=) Z.succ.
Proof. intros n1 n2. lia. Qed.

Instance Z_pred_inj : Inj (=) (=) Z.pred.
Proof. intros n1 n2. lia. Qed.

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
