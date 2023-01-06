(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import ssreflect.
From stdpp Require Import base decidable finite countable.

From bedrock.prelude Require Import prelude finite.

From bedrock.prelude.elpi.derive Require Export
  eq_dec
  inhabited
  finite
  countable.

From elpi.apps Require Export derive.

Module BasicTests.
  Variant T1 := A1 | B1 | C1.
  #[only(eq_dec)] derive T1.
  #[only(inhabited)] derive T1.
  #[only(countable)] derive T1.
  #[only(finite)] derive T1.

  (*TODO: Potential derive bug; the following produces:
    Anomaly: Uncaught exception Failure("split dirpath")*)
  (*#[only(finite)] derive
   Variant T2 := A2 | B2 | C2.*)

  #[only(eq_dec,inhabited)] derive
  Variant T2 := A2 | B2 | C2.
  #[only(countable)] derive T2.
  #[only(finite)] derive T2.
End BasicTests.

(*** Test derivation using Countable. *)
#[local] Ltac assert_True :=
  match goal with
  | |- True => idtac
  | |- _ => fail
  end.

Module DerivingTest.
  Variant t := A | B | C.
  #[only(eq_dec,countable)] derive t.
  Goal forall x y : t, if bool_decide (x = y) then True else True.
  Proof. by move => x y; case (bool_decide_reflect (x = y)). Qed.
  Goal forall x y : t, encode x = encode y -> x = y.
  Proof. by move => x y X; apply encode_inj in X. Qed.
  Goal match Pos.compare (encode A) (encode B) with
       | Eq => True
       | Lt => True
       | Gt => True
       end.
  Proof.
    Succeed by vm_compute.
    (* Even [simpl] normalizes this goal - that's nice! *)
    by simpl; assert_True.
  Qed.
End DerivingTest.

(*** Test derivation using Finite. *)
Module Deriving2Test.
  Variant t := A | B | C (_ : bool) | D (_ : option bool) (_ : bool).
  (* #[global] Instance: EqDecision t.
  Proof. solve_decision. Defined. *)
  #[only(inhabited,eq_dec,finite)] derive t.

  (*
  Print Assumptions t_inhabited.
  Print t_inhabited.
  Print Assumptions t_finite.
  Print t_finite.
  Print t_finite_subproof_nodup.
  Print t_finite_subproof_elem_of.
  *)

  (* Test the tactic in isolation. *)
  Definition t_finite2 : Finite t.
  Proof. solve_finite ([A; B] ++ (C <$> enum _) ++ (D <$> enum _ <*> enum _)). Defined.
  (*
  Print Assumptions t_finite2.
  Print t_finite2_subproof.
  *)
  Variant t2 := E | F | G.
  #[only(inhabited,eq_dec)] derive t2.
  #[only(finite)] derive t2.
  (* #[global] Instance: EqDecision t.
  Proof. solve_decision. Defined. *)
  Section test.
    Context (x : nat).
    Variant t3 := H.
    #[only(inhabited,eq_dec,finite)] derive t3.
  End test.

  Goal forall x y : t, if bool_decide (x = y) then True else True.
  Proof. by move => x y; case (bool_decide_reflect (x = y)). Qed.
  Goal forall x y : t, encode x = encode y -> x = y.
  Proof. by move => x y X; apply encode_inj in X. Qed.

  (* Eval vm_compute in enum t. *)

  Goal match Pos.compare (encode A) (encode B) with
       | Eq => True
       | Lt => True
       | Gt => True
       end.
  Proof.
    Succeed by vm_compute.
    (* [simpl] normalizes this goal too! *)
    by simpl; assert_True.
  Qed.
End Deriving2Test.
