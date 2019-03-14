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

(* soundness of the specification *)
Theorem A_cpp_sound : forall (resolve : genv),
    denoteModule A_cpp.module |-- A_cpp_spec resolve.
Proof.
  intros.
  unfold A_cpp_spec.
  work.

  verifyF_forget A_hpp_spec.A__foo.
  { (* A::foo(int) *)
    start_proof.
    simplifying.
    work.
    simplifying.
    work.
    done_proof. }

  finish_module.
Qed.
