(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
This file axiomatizes and instantiates [mpred] with the ghost types of the logic
that we use for C++.
The core C++ logic is defined in [pred.v]. *)
From iris.base_logic.lib Require Import own cancelable_invariants.
Require Import iris.bi.monpred.

From bedrock.prelude Require Import base.
From bedrock.lang Require Import bi.prelude.
Require Export bedrock.lang.base_logic.mpred.
Import ChargeNotation.

Module Type CPP_LOGIC_CLASS_BASE.
  Parameter cppPreG : gFunctors -> Type.
  Axiom has_inv : forall Σ, cppPreG Σ -> invGS Σ.
  Axiom has_cinv : forall Σ, cppPreG Σ -> cinvG Σ.

  Parameter _cpp_ghost : Type.
End CPP_LOGIC_CLASS_BASE.

Module Type CPP_LOGIC_CLASS_MIXIN (Import CC : CPP_LOGIC_CLASS_BASE).

  (* In Iris idiom, this corresponds to a cppG *)
  Class cpp_logic {thread_info : biIndex} {Σ : gFunctors} : Type :=
  { cpp_ghost    : _cpp_ghost
  ; cpp_has_cppG : cppPreG Σ
  }.
  #[global] Arguments cpp_logic : clear implicits.
  #[global] Hint Mode cpp_logic - - : cpp_logic.

  #[global] Instance cpp_has_inv `{!cpp_logic thread_info Σ} : invGS Σ
    := has_inv Σ cpp_has_cppG.
  #[global] Instance cpp_has_cinv `{!cpp_logic thread_info Σ} : cinvG Σ
    := has_cinv Σ cpp_has_cppG.
  #[global] Hint Opaque cpp_has_inv cpp_has_cinv : typeclass_instances br_opacity.

End CPP_LOGIC_CLASS_MIXIN.

Module Type CPP_LOGIC_CLASS := CPP_LOGIC_CLASS_BASE <+ CPP_LOGIC_CLASS_MIXIN.

Declare Module LC : CPP_LOGIC_CLASS.
Export LC.
