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
From Cpp Require Export IrisBridge.
Export ChargeNotation.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Semantics.

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

    Parameter with_genv : (genv -> mpred) -> mpred.
    Axiom with_genv_single : forall f g,
        with_genv f //\\ with_genv g -|- with_genv (fun r => f r //\\ g r).
    Axiom with_genv_single_sep : forall f g,
        with_genv f ** with_genv g -|- with_genv (fun r => f r ** g r).
    Axiom with_genv_ignore : forall P,
        with_genv (fun _ => P) -|- P.
    Declare Instance Proper_with_genv_lentails :
      Proper (pointwise_relation _ lentails ==> lentails) with_genv.
    Declare Instance Proper_with_genv_lequiv :
      Proper (pointwise_relation _ lequiv ==> lequiv) with_genv.

    (* heap points to *)
    (* note(gmm): this needs to support fractional permissions and other features *)
    Parameter tptsto : type -> Qp -> forall addr value : val, mpred.

    Parameter Timeless_tptsto : forall {ty q a v}, Timeless (tptsto ty q a v).

    Axiom tptsto_has_type : forall t q a v,
        tptsto t q a v |-- tptsto t q a v ** [| has_type v t |].

    Axiom tptsto_split : forall t q1 q2 a v,
        tptsto t (q1+q2) a v -|- tptsto t q1 a v ** tptsto t q2 a v.

    Axiom tptsto_same_val : forall t q1 q2 a v1 v2,
        let p :=
            tptsto t q1 a v1 ** tptsto t q2 a v2 in
        p |-- p ** [| v1=v2 |] ** ([| ((q1+q2)%Qp ≤ 1)%Qc |]).
    
    Parameter local_addr : region -> ident -> ptr -> mpred.

    (* the pointer contains the code *)
    Parameter code_at : Func -> ptr -> mpred.
    (* code_at is freely duplicable *)
    Axiom code_at_dup : forall p f, code_at p f -|- code_at p f ** code_at p f.
    Axiom code_at_drop : forall p f, code_at p f |-- empSP.

    Parameter ctor_at : ptr -> Ctor -> mpred.
    Parameter dtor_at : ptr -> Dtor -> mpred.
  End with_Σ.
  Arguments mpred _ : clear implicits.
  Arguments mpredI _ : clear implicits.
  Arguments mpredSI _ : clear implicits.

  Existing Instance Timeless_tptsto.

End logic.


Declare Module L : logic.

Export L.
