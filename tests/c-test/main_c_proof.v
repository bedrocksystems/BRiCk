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
Proof. Admitted.

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

(* soundness of the specification *)
Theorem main_cpp_sound : forall (resolve : genv),
    denoteModule main_c.module |-- spec resolve.
Proof.
  intros.
  simpl.
  unfold spec.
  start_module.

  verifyF_forget "_Z4main".
  { (* ::main(int argc, char* argv[]) *)
    start_proof.
    rewrite denoteModule_weaken.
    simplifying.
    work.
    (* this is the loop invariant
     * todo(gmm): i need to clean this up a lot!
     *)
    transitivity (
        (ti_cglob' (resolve:=resolve) "_Z6putstr" putstr_spec **
         tlocal x1 (Tint None true) "argc" x **
         tlocal x1 (Tpointer (Qmut (Tpointer (Qmut T_char)))) "argv" x0) **
         (Forall res : val, [| res = 0 |] ** args_array x0 x3 ** @trace PutStr (Ret tt) -* x2 res) **
         args_array x0 x3 **
         Exists i,
           [| 0 <= i <= Z.of_nat (Datatypes.length x3) |] **
           tlocal x1 T_int "i" i **
           trace (printEach (skipn (Z.to_nat i) x3))).
    { work. }
    eapply wp_for.
    simplifying.
    work.
    simplifying.
    work.
    rewrite is_true_int.
    destruct (ZArith_dec.Z_lt_ge_dec x4 (Z.of_nat (Datatypes.length x3))).
    { simpl.
      simplifying.
      unfold args_array.
      assert (exists v, exists i, Z.of_nat i = x4 /\ nth_error x3 i = Some v).
      { eapply can_get_element; eauto. }
      destruct H2 as [ ? [ ? [ ? ? ] ] ].
      rewrite tarray_cell; eauto with size_of.
      rewrite <- wp_lhs_subscript.
      simplifying.
      simpl.
      work.
      simplifying.
      work.
      { subst. work. }
      simplifying.
      instantiate (1 := (x5, printEach (skipn (S (Z.to_nat x4)) x3))).
      simpl.
      unfold tlocal.
      lift_ex_l.
      perm_left ltac:(idtac; eapply (Lemmas.learn_bounds x4); simpl; intros).
      work.
      cutrewrite (skipn (Z.to_nat x4) x3 = x5 :: skipn (S (Z.to_nat x4)) x3).
      { simpl. work.
        simplifying.
        work.
        rewrite tarray_cell with (ms :=x3); eauto with size_of.
        work.
        erewrite skipn_to_nat_of_nat; eauto. reflexivity. }
      { simpl. subst.
        rewrite Znat.Nat2Z.id.
        clear - H3.
        generalize dependent x6.
        induction x3.
        { destruct x6; simpl in *; congruence. }
        { intros.
          destruct x6; simpl in *.
          inversion H3; clear H3; subst; auto.
          eauto. } } }
    { simpl.
      unfold Sskip.
      simplifying.
      work.
      rewrite skipn_allZ; eauto.
      done_proof. } }

  finish_module.
  Unshelve.
  all: eassumption.
Qed.