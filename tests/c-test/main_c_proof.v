(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From Cpp Require Import
     Auto.

Require C.main_c.
Require Import C.main_c_spec.


Lemma can_get_element {T} :
  forall (x3 : list T) (x4 : Z),
    0 <= x4 <= Z.of_nat (Datatypes.length x3) ->
    x4 < Z.of_nat (Datatypes.length x3) ->
    exists (v : T) (i : nat), Z.of_nat i = x4 /\ nth_error x3 i = Some v.
Proof.
  induction x3.
  { simpl. intros. exfalso. lia. }
  { Opaque Z.of_nat. simpl in *. intros.
    destruct H.
    destruct x4.
    { exists a. exists 0%nat. simpl. tauto. }
    { specialize (IHx3 (Z.pos p - 1)). destruct IHx3; try lia.
      destruct H2. destruct H2.
      exists x. exists (S x0). simpl. split; eauto.
      lia. }
    { exfalso. lia. } }
Qed.
Transparent Z.of_nat.

Lemma skipn_allZ : forall {T} (ls : list T) x,
    x >= Z.of_nat (Datatypes.length ls) ->
    skipn (Z.to_nat x) ls = nil.
Proof.
  induction ls; simpl; intros.
  { destruct (Z.to_nat x); auto. }
  { destruct (Z.to_nat x) eqn:?.
    { simpl. exfalso. destruct x; simpl in *; try lia. }
    erewrite <- IHls.
    simpl. instantiate (1 := x-1).
    f_equal.
    rewrite (Znat.Z2Nat.inj_sub x 1); simpl.
    rewrite Heqn. lia. lia. lia. }
Qed.

Lemma skipn_to_nat_of_nat:
  forall (x3 : list string) (x4 : Z),
    x4 < Z.of_nat (Datatypes.length x3) ->
    forall x6 : nat,
      Z.of_nat x6 = x4 ->
      match x3 with
      | nil => nil
      | _ :: l0 => skipn (Z.to_nat x4) l0
      end = skipn (Z.to_nat (Z.of_nat x6 + 1)) x3.
Proof.
  intros x3 x4 l x6 H2.
  generalize (Znat.Nat2Z.inj_add x6 1); simpl; intros.
  rewrite <- H; clear H.
  subst.
  cutrewrite (Z.to_nat (Z.of_nat (x6 + 1)) = S (Z.to_nat (Z.of_nat x6))).
  reflexivity.
  rewrite <- Znat.Z2Nat.inj_succ; lia.
Qed.

Lemma nth_error_skipn:
  forall (x3 : list string) (x6 : nat) (x5 : string),
    nth_error x3 x6 = Some x5 ->
    skipn x6 x3 = x5 :: match x3 with
                       | nil => nil
                       | _ :: l => skipn x6 l
                       end.
Proof.
  induction x3.
  { destruct x6; simpl in *; congruence. }
  { intros.
    destruct x6; simpl in *.
    inversion H; clear H; subst; auto.
    eauto. }
Qed.

(* soundness of the specification *)
Theorem main_cpp_sound : forall (resolve : genv),
    denoteModule main_c.module |-- spec resolve.
Proof.
  intros.
  simpl.
  unfold spec.
  start_module.

  verifyF_forget "main".
  { (* ::main(int argc, char* argv[]) *)
    simpl.
    start_proof.
    rewrite denoteModule_weaken.
    work.
    simplifying.
    work.
    (* this is the loop invariant
     *)
    assert_sep (fun a1 x =>
        Exists i : Z,
           tlocal_at ρ "i" a1 (tprim T_int i) **
           trace (printEach (skipn (Z.to_nat i) x)) **
           [| 0 <= i <= Z.of_nat (Datatypes.length x) |]).
    eapply wp_for.
    simplifying.
    work.
    simplifying.
    work.
    simpl.
    subst.
    rewrite is_true_int.
    destruct (ZArith_dec.Z_lt_ge_dec i (Z.of_nat (Datatypes.length x))).
    { simpl.
      simplifying.
      Hint Resolve wp_prval_cast_noop : wpe.
      simplifying. simpl.
      simplifying.
      assert (exists v, exists i', Z.of_nat i' = i /\ nth_error x i' = Some v).
      { eapply can_get_element; eauto. }
      destruct H0 as [ ? [ ? [ ? ? ] ] ].
      unfold main.args_array.
      rewrite tarray_cell; eauto with size_of.
      work.
      simplifying.
      work.
      { subst. work. }
      simpl.
      work.
      cutrewrite (skipn (Z.to_nat i) x = x1 :: skipn (S (Z.to_nat i)) x).
      2:{ simpl. subst.
          rewrite Znat.Nat2Z.id.
          eauto using nth_error_skipn. }
      simpl. work.
      simplifying. simpl.
      work.
      rewrite tarray_cell with (ms :=x); eauto with size_of.
      erewrite skipn_to_nat_of_nat; eauto.
      work. work. }
    { simpl.
      repeat (simplifying; simpl; work).
      rewrite skipn_allZ; eauto.
      work.
      done_proof. } }

  finish_module.
Qed.
