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
From Cpp.Auto Require Import vc.

Require RetRef.test_cpp.
Require Import RetRef.test_cpp_spec.

(* soundness of the specification *)
Theorem main_cpp_sound : forall (resolve : genv),
    denoteModule test_cpp.module |-- test_cpp_spec resolve.
Proof.
  intros.
  simpl.
  unfold test_cpp_spec.

  verifyF_forget "_Z7get_refPi".
  { (* ::get_ref(int* ) *)
    start_proof.
    simplifying.
    change (wpe resolve ti x0 Lvalue) with (wp_lhs (resolve:=resolve) ti x0).
    simplifying.
    work.
    done_proof. }

  finish_module.
Qed.
