(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Cpp Require Import
     Auto.
Require Import Cpp.Sem.Linking.

From Demo Require
     A_hpp A_hpp_spec A_hpp_proof
     A_cpp A_cpp_spec A_cpp_proof.
Import A_hpp_spec.

Section with_Σ.
Context {Σ:gFunctors}.

Theorem A_o_sound (resolve : genv)
: denoteModule (Σ:=Σ) A_cpp.module
  |-- A__foo_spec ** A__bar_spec.
Proof.
  use_module (A_hpp_proof.A_hpp_sound (Σ:=Σ) resolve).
  use_module (A_cpp_proof.A_cpp_sound (Σ:=Σ) resolve).
  rewrite denoteModule_weaken.
  unfold A_cpp_spec.A_cpp_spec.
  unfold A_hpp_spec.A_hpp_spec.
  assert (Persistent (A__foo_spec (Σ:=Σ))) by eapply Duplicable_global_ticptr.
  module_cancel.
  work.
Qed.

End with_Σ.
