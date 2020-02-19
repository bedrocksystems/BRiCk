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
From iris.bi.lib Require Import fractional.
From bedrock Require Export IrisBridge.
Export ChargeNotation.

From bedrock.lang.cpp Require Import ast semantics.

Module Type logic.

  Section with_Σ.
    Context {Σ : gFunctors}.

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

    Global Instance later_entails : Proper ((lentails) ==> (lentails)) (@sbi_later mpredSI).
    Proof.
      intros H H1 Hent.
      f_equiv. eauto.
    Qed.

    (* heap points to *)
    Parameter tptsto : forall {resolve:genv}, type -> Qp -> forall addr value : val, mpred.
    Axiom Proper_tptsto :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> lentails) (@tptsto).

    Global Declare Instance tptsto_timeless resolve ty q a v
      : Timeless (@tptsto resolve ty q a v).
    Global Declare Instance tptsto_fractional resolve ty a v
      : Fractional (λ q, @tptsto resolve ty q a v).
    Global Declare Instance tptsto_as_fractional resolve ty q a v :
      AsFractional (@tptsto resolve ty q a v) (λ q, @tptsto resolve ty q a v)%I q.

    Axiom tptsto_has_type : forall resolve t q a v,
        @tptsto resolve t q a v |-- @tptsto resolve t q a v ** [| has_type v t |].

    Lemma tptsto_split resolve t q1 q2 a v :
        @tptsto resolve t (q1+q2) a v -|- @tptsto resolve t q1 a v ** @tptsto resolve t q2 a v.
    Proof. apply tptsto_fractional. Qed.

    Axiom tptsto_same_val : forall resolve t q1 q2 a v1 v2,
        let p :=
            @tptsto resolve t q1 a v1 ** @tptsto resolve t q2 a v2 in
        p |-- p ** [| v1=v2 |] ** ([| ((q1+q2)%Qp ≤ 1)%Qc |]).

    (* this is like a "points to" where the location is (region * ident).
     *)
    Parameter local_addr : region -> ident -> ptr -> mpred.

    (* the pointer points to the code
     * todo(gmm): i need to bottom this out in something "real" in order
     * to do code-loading.
     *)
    Parameter code_at : forall {resolve:genv}, Func -> ptr -> mpred.
    (* code_at is freely duplicable *)
    Global Declare Instance code_at_persistent resolve f p
      : Persistent (@code_at resolve f p).
    Global Declare Instance code_at_affine resolve f p
      : Affine (@code_at resolve f p).

    Parameter ctor_at : forall {resolve: genv}, ptr -> Ctor -> mpred.
    Parameter dtor_at : forall {resolve:genv}, ptr -> Dtor -> mpred.

  End with_Σ.
  Arguments mpred _ : clear implicits.
  Arguments mpredI _ : clear implicits.
  Arguments mpredSI _ : clear implicits.

  Existing Instance tptsto_timeless.

End logic.


Declare Module L : logic.

Export L.
