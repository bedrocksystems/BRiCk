(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
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

(* (* this is the ghost state necessary for C++ *) *)
(* Instance: EqDecision ptr := ptr_eq_dec. *)
(* Instance: Countable ptr. *)
(* Admitted. *)

(* Print region. *)
(* Instance: EqDecision region. Admitted. *)
(* Instance: Countable region. Admitted. *)

(* Check (leibnizO N). *)
(* SearchAbout ofeT. *)

(* Definition addr : Set := N. *)
(* Definition byte : Set := N. *)
(* Variant runtime_val : Set := *)
(* | Rundef *)
(* | Rval (_ : byte). *)

(* Definition fractionalR (o : ofeT) : cmraT := *)
(*   prodR fracR (optionUR (agreeR (leibnizO N))). *)

Class cppG (Σ : gFunctors) : Type :=
{ (* heapG : inG Σ (gmapR addr (prodR fracR (optionUR (agreeR (leibnizO N))))) *)
(* ; localG : inG Σ (gmapUR region (gmapUR ident (exclR (leibnizO ptr)))) *)
(* ; mem_injG : inG Σ (gmapUR ptr (agreeR (leibnizO addr))) *)
  has_inv :> invG Σ
; has_cinv :> cinvG Σ
}.

Class cpp_logic {ti : biIndex} : Type :=
{ _Σ :> gFunctors
; has_cppG :> cppG _Σ }.
Arguments cpp_logic : clear implicits.
Coercion _Σ : cpp_logic >-> gFunctors.

Section with_PROP.
  Context `{Σ : cpp_logic ti}.

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

  (* heap points to *)
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

  (* Axiom tptsto_same_val : forall σ t q1 q2 a v1 v2, *)
  (*     let p := @tptsto σ t q1 a v1 ** @tptsto σ t q2 a v2 in *)
  (*     p |-- p ** [| v1=v2 |] ** ([| ((q1+q2)%Qp ≤ 1)%Qc |]). *)


  (* this is like a "points to" where the location is (region * ident).
   *)
  Definition local_addr (ρ : region) (i : ident) (p : ptr) : mpred.
  Proof using Σ.
    (* refine (own _ {[ ρ := {[ i := Excl p ]} ]}). eapply localG. 2,3: refine _. *)
  Admitted.

  (* the pointer points to the code
   * todo(gmm): i need to bottom this out in something "real" in order
   * to do code-loading.
   *)
  Definition code_at : forall {σ:genv}, Func -> ptr -> mpred.
  Proof using Σ. Admitted.
  Definition ctor_at : forall {σ: genv}, Ctor -> ptr -> mpred.
  Proof using Σ. Admitted.
  Definition dtor_at : forall {σ:genv}, Dtor -> ptr -> mpred.
  Proof using Σ. Admitted.

  (* code_at is freely duplicable *)
  Global Instance code_at_persistent σ f p
    : Persistent (@code_at σ f p).
  Proof. Admitted.
  Global Instance code_at_affine σ f p
    : Affine (@code_at σ f p).
  Proof. Admitted.

End with_PROP.
