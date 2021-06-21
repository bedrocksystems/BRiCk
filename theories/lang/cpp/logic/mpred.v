(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
This file defines the core [bi] (called [mpred]) that we use for C++.
The core logic is defined in [pred.v]. *)
From iris.base_logic.lib Require Import own cancelable_invariants.
Require Import iris.bi.monpred.

From bedrock.lang Require Import prelude.base bi.prelude.
Import ChargeNotation.

Module Type CPP_LOGIC_CLASS_BASE.
  Parameter cppG : gFunctors -> Type.
  Axiom has_inv : forall Σ, cppG Σ -> invG Σ.
  Axiom has_cinv : forall Σ, cppG Σ -> cinvG Σ.

  Global Existing Instances has_inv has_cinv.

  Existing Class cppG.

  Parameter _cpp_ghost : Type.
End CPP_LOGIC_CLASS_BASE.

Module Type CPP_LOGIC_CLASS_MIXIN (Import CC : CPP_LOGIC_CLASS_BASE).

  Class cpp_logic {thread_info : biIndex} : Type :=
  { _Σ       : gFunctors
  ; _ghost   : _cpp_ghost
  ; has_cppG : cppG _Σ
  }.
  Arguments cpp_logic : clear implicits.
  Coercion _Σ : cpp_logic >-> gFunctors.

  Global Existing Instance has_cppG.

  Section with_cpp.
    Context `{cpp_logic ti}.

    Definition mpredI : bi := monPredI ti (iPropI _Σ).
    Definition mpred := bi_car mpredI.

    (* TODO: seal *)
    Canonical Structure mpredO : ofeT
      := OfeT mpred (ofe_mixin (monPredO ti (iPropI _Σ))).
  End with_cpp.

  Bind Scope bi_scope with bi_car.
  Bind Scope bi_scope with mpred.
  Bind Scope bi_scope with mpredI.
End CPP_LOGIC_CLASS_MIXIN.

Module Type CPP_LOGIC_CLASS := CPP_LOGIC_CLASS_BASE <+ CPP_LOGIC_CLASS_MIXIN.

Declare Module LC : CPP_LOGIC_CLASS.
Export LC.
