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
Require Import iris.algebra.lib.frac_auth.
Require Import iris.algebra.excl.
Require Import iris.algebra.gmap.
From bedrock Require Export IrisBridge.
Export ChargeNotation.

From bedrock.lang.cpp Require Import ast semantics.

(** this is the ghost state necessary for C++
 *)
Class cppG (Σ : gFunctors) : Type :=
{ has_inv :> invG Σ
; has_cinv :> cinvG Σ
}.

(** this class wraps up everything necessary to write specifications
    about C++ program.

    [thread_info] is the additional information that is associated with
    each thread.
 *)
Class cpp_logic {thread_info : biIndex} : Type :=
{ _Σ :> gFunctors
; has_cppG :> cppG _Σ }.
Arguments cpp_logic : clear implicits.
Coercion _Σ : cpp_logic >-> gFunctors.

Section with_PROP.
  Context `{Σ : cpp_logic}.
  (* ^ note that implicit argument insertion allows us to write [cpp_logic]
     and Coq will automatically introduce [thread_info : biIndex]
   *)

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

  (** typed points to
      stack and heap pointers are treated uniformly
   *)
  Definition tptsto {σ:genv} (t : type) (q : Qp) (a : ptr) (v : val) : mpred.
  Proof using Σ. Admitted.

  Global Instance tptsto_proper_entails :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> lentails) (@tptsto).
  Proof. Admitted.
  Global Instance tptsto_proper_equiv :
    Proper (genv_eq ==> eq ==> eq ==> eq ==> eq ==> lequiv) (@tptsto).
  Proof. Admitted.

  Global Instance tptsto_fractional σ ty a v
    : Fractional (λ q, @tptsto σ ty q a v).
  Proof. Admitted.
  Global Instance tptsto_as_fractional σ ty q a v :
    AsFractional (@tptsto σ ty q a v) (λ q, @tptsto σ ty q a v)%I q.
  Proof. Admitted.

  Global Instance tptsto_timeless σ ty q a v
    : Timeless (@tptsto σ ty q a v).
  Proof. Admitted.

  Theorem tptsto_has_type : forall σ t q a v,
      @tptsto σ t q a v |-- @tptsto σ t q a v ** [| has_type v t |].
  Proof. Admitted.

  (** this is like a "points to" where the location is (region * ident).
   *)
  Definition local_addr (ρ : region) (i : ident) (p : ptr) : mpred.
  Proof using Σ.
    (* refine (own _ {[ ρ := {[ i := Excl p ]} ]}). eapply localG. 2,3: refine _. *)
  Admitted.

  (** the pointer points to the code

      note that in the presence of code-loading, function calls will
      require an extra side-condition that the code is loaded.
   *)
  Definition code_at : forall {σ:genv}, Func -> ptr -> mpred.
  Proof using Σ. Admitted.
  Definition method_at : forall {σ:genv}, Method -> ptr -> mpred.
  Proof using Σ. Admitted.
  Definition ctor_at : forall {σ: genv}, Ctor -> ptr -> mpred.
  Proof using Σ. Admitted.
  Definition dtor_at : forall {σ:genv}, Dtor -> ptr -> mpred.
  Proof using Σ. Admitted.

  Global Instance code_at_persistent σ f p : Persistent (@code_at σ f p).
  Proof. Admitted.
  Global Instance code_at_affine σ f p : Affine (@code_at σ f p).
  Proof. Admitted.

  Global Instance method_at_persistent σ f p : Persistent (@method_at σ f p).
  Proof. Admitted.
  Global Instance method_at_affine σ f p : Affine (@method_at σ f p).
  Proof. Admitted.

  Global Instance ctor_at_persistent σ f p : Persistent (@ctor_at σ f p).
  Proof. Admitted.
  Global Instance ctor_at_affine σ f p : Affine (@ctor_at σ f p).
  Proof. Admitted.

  Global Instance dtor_at_persistent σ f p : Persistent (@dtor_at σ f p).
  Proof. Admitted.
  Global Instance dtor_at_affine σ f p : Affine (@dtor_at σ f p).
  Proof. Admitted.


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

End with_PROP.
