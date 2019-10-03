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

Require RetRef.test_cpp.
Require Import RetRef.test_cpp_spec.

Section with_Σ.
Context {Σ:gFunctors}.

(* soundness of the specification *)
Theorem main_cpp_sound : forall (resolve : genv),
    denoteModule (Σ:=Σ) test_cpp.module |-- test_cpp_spec.
Proof.
  intros.
  simpl.
  unfold test_cpp_spec.

  verify_forget_spec @get_ref_spec.
  { (* ::get_ref(int* ) *)
    start_proof.
    simplifying.
    work.
    done_proof. }

  finish_module.
Qed.

End with_Σ.
