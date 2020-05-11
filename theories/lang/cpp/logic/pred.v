(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(** this file defines the core logic (called [mpred]) that we use
    for C++.

    known issues:
    - currently the logic is sequentially consistent
    - the memory model is simplified from the standard C++ memory
      model.
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Coq.Classes Require Import
     RelationClasses Morphisms.

From iris.base_logic.lib Require Export iprop.
Require Import iris.bi.monpred.
From iris.bi.lib Require Import fractional.
Require Import iris.base_logic.lib.fancy_updates.
Require Import iris.base_logic.lib.own.
Require Import iris.base_logic.lib.cancelable_invariants.

From bedrock Require Export IrisBridge.
Export ChargeNotation.

From bedrock.lang.cpp Require Import ast semantics.

Module Type CPP_LOGIC.

  Parameter cppG : gFunctors -> Type.
  Parameter has_inv : forall Σ, cppG Σ -> invG Σ.
  Parameter has_cinv : forall Σ, cppG Σ -> cinvG Σ.
  Existing Class cppG.

  Parameter _cpp_ghost : Type.

  Class cpp_logic {thread_info : biIndex} : Type :=
  { _Σ       : gFunctors
  ; _ghost   : _cpp_ghost
  ; has_cppG :> cppG _Σ }.
  Arguments cpp_logic : clear implicits.
  Coercion _Σ : cpp_logic >-> gFunctors.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    Definition mpred := iProp Σ.
    Canonical Structure mpredI : bi :=
      {| bi_car := mpred
       ; bi_ofe_mixin := (iPropI Σ).(bi_ofe_mixin)
       ; bi_bi_mixin := (iPropI Σ).(bi_bi_mixin) |}.
    (* todo: Fix the warning generated from this definition *)
    Canonical Structure mpredSI : sbi :=
      {| sbi_car := mpred
       ; sbi_ofe_mixin := (iPropI Σ).(bi_ofe_mixin)
       ; sbi_bi_mixin := (iPropI Σ).(bi_bi_mixin)
       ; sbi_sbi_mixin := (iPropSI Σ).(sbi_sbi_mixin) |}.

    (* valid pointers allow for accessing one past the end of a structure/array *)
    Parameter valid_ptr : ptr -> mpred.

    Axiom valid_ptr_persistent : forall p, Persistent (valid_ptr p).
    Axiom valid_ptr_affine : forall p, Affine (valid_ptr p).
    Axiom valid_ptr_timeless : forall p, Timeless (valid_ptr p).
    Existing Instance valid_ptr_persistent.
    Existing Instance valid_ptr_affine.
    Existing Instance valid_ptr_timeless.

    Axiom valid_ptr_nullptr : |-- valid_ptr nullptr.

    (* heap points to *)
    Parameter tptsto : forall {σ:genv} (t : type) (q : Qp) (a : ptr) (v : val), mpred.

    Axiom tptsto_proper_entails :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> lentails) (@tptsto).
    Axiom tptsto_proper_equiv :
      Proper (genv_eq ==> eq ==> eq ==> eq ==> eq ==> lequiv) (@tptsto).

    Axiom tptsto_fractional :
      forall {σ} ty a v, Fractional (λ q, @tptsto σ ty q a v).
    Axiom tptsto_as_fractional :
      forall {σ} ty q a v, AsFractional (@tptsto σ ty q a v) (λ q, @tptsto σ ty q a v)%I q.

    Axiom tptsto_timeless :
      forall {σ} ty q a v, Timeless (@tptsto σ ty q a v).

    Axiom tptsto_has_type : forall σ t q a v,
        @tptsto σ t q a v |-- @tptsto σ t q a v ** [| has_type v t |] ** valid_ptr a.

    (** the pointer points to the code

      note that in the presence of code-loading, function calls will
      require an extra side-condition that the code is loaded.
     *)
    Parameter code_at : Func -> ptr -> mpred.
    Parameter method_at : Method -> ptr -> mpred.
    Parameter ctor_at : Ctor -> ptr -> mpred.
    Parameter dtor_at : Dtor -> ptr -> mpred.

    Axiom code_at_persistent : forall f p, Persistent (@code_at f p).
    Axiom code_at_affine : forall f p, Affine (@code_at f p).
    Axiom code_at_timeless : forall f p, Timeless (@code_at f p).

    Axiom method_at_persistent : forall f p, Persistent (@method_at f p).
    Axiom method_at_affine : forall f p, Affine (@method_at f p).
    Axiom method_at_timeless : forall f p, Timeless (@method_at f p).

    Axiom ctor_at_persistent : forall f p, Persistent (@ctor_at f p).
    Axiom ctor_at_affine : forall f p, Affine (@ctor_at f p).
    Axiom ctor_at_timeless : forall f p, Timeless (@ctor_at f p).

    Axiom dtor_at_persistent : forall f p, Persistent (@dtor_at f p).
    Axiom dtor_at_affine : forall f p, Affine (@dtor_at f p).
    Axiom dtor_at_timeless : forall f p, Timeless (@dtor_at f p).

  End with_cpp.

End CPP_LOGIC.

Declare Module L : CPP_LOGIC.
Export L.

Existing Instances
         L.code_at_persistent L.code_at_affine
         L.method_at_persistent L.method_at_affine
         L.ctor_at_persistent L.ctor_at_affine
         L.dtor_at_persistent L.dtor_at_affine
         L.tptsto_proper_entails
         L.tptsto_proper_equiv
         L.tptsto_fractional
         L.tptsto_as_fractional
         L.tptsto_timeless
         L.has_inv
         L.has_cinv
         L.has_cppG
         L.valid_ptr_affine
         L.valid_ptr_persistent.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** function specifications written in weakest pre-condition style.
   *)
  Record function_spec : Type :=
    { fs_return : type
    ; fs_arguments : list type
    ; fs_spec : thread_info -> list val -> (val -> mpred) -> mpred
    }.
  Arguments function_spec : clear implicits.
  Arguments Build_function_spec : clear implicits.

  Definition type_of_spec `(fs : function_spec) : type :=
    normalize_type (Tfunction fs.(fs_return) fs.(fs_arguments)).

End with_cpp.
