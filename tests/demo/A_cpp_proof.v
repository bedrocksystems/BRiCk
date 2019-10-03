(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From Cpp Require Import Auto.

Require Demo.A_cpp.
Require Import Demo.A_cpp_spec.

Opaque denoteModule.

Section with_Σ.
Context {Σ:gFunctors}.

(* soundness of the specification *)
Theorem A_cpp_sound : forall (resolve : genv),
    denoteModule (Σ:=Σ) A_cpp.module |-- A_cpp_spec.
Proof.
  intros.
  unfold A_cpp_spec, module.
  work.

  verify_forget_spec @A_hpp_spec.A__foo_spec.
  { (* A::foo(int) *)
    start_proof.
    repeat (simplifying; simpl; work).
    done_proof. }

  finish_module.
Qed.

End with_Σ.
