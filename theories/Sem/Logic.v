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

    Axiom with_genv_ignore_pred : forall P,
        Forall x, P x |-- with_genv P.
    Lemma with_genv_ignore_only_provable : forall (P : _ -> Prop),
        [| forall x, P x |] |-- with_genv (λ x, [| P x |]).
    Proof. intros. rewrite <- with_genv_ignore_pred. eauto. Qed.

    Axiom with_genv_ignore1 : forall P,
        with_genv (fun _ => P) |-- P.
    Lemma with_genv_ignore2 P :
        P |-- with_genv (fun _ => P).
    Proof. rewrite <- with_genv_ignore_pred. eauto. Qed.
    Lemma with_genv_ignore P :
        with_genv (fun _ => P) -|- P.
    Proof. split'. apply with_genv_ignore1. apply with_genv_ignore2. Qed.

    Declare Instance Proper_with_genv_lentails :
      Proper (pointwise_relation _ lentails ==> lentails) with_genv.
    Declare Instance Proper_with_genv_lequiv :
      Proper (pointwise_relation _ lequiv ==> lequiv) with_genv.

    Global Declare Instance with_genv_persistent P :
      (forall resolve, Persistent (P resolve)) -> Persistent (with_genv P).

    (* heap points to *)
    (* note(gmm): this needs to support fractional permissions and other features *)
    Parameter tptsto : type -> Qp -> forall addr value : val, mpred.

    Global Declare Instance tptsto_timeless ty q a v : Timeless (tptsto ty q a v).
    Global Declare Instance tptsto_fractional ty a v : Fractional (λ q, tptsto ty q a v).
    Global Declare Instance tptsto_as_fractional ty q a v :
      AsFractional (tptsto ty q a v) (λ q, tptsto ty q a v)%I q.

    Axiom tptsto_has_type : forall t q a v,
        tptsto t q a v |-- tptsto t q a v ** [| has_type v t |].

    Lemma tptsto_split t q1 q2 a v :
        tptsto t (q1+q2) a v -|- tptsto t q1 a v ** tptsto t q2 a v.
    Proof. apply tptsto_fractional. Qed.

    Axiom tptsto_same_val : forall t q1 q2 a v1 v2,
        let p :=
            tptsto t q1 a v1 ** tptsto t q2 a v2 in
        p |-- p ** [| v1=v2 |] ** ([| ((q1+q2)%Qp ≤ 1)%Qc |]).
    
    Parameter local_addr : region -> ident -> ptr -> mpred.

    Global Declare Instance local_addr_persistent resolve x p :
      Persistent (local_addr resolve x p).

    (* the pointer contains the code *)
    Parameter code_at : Func -> ptr -> mpred.
    (* code_at is freely duplicable *)
    Global Declare Instance code_at_persistent f p : Persistent (code_at f p). 
    Lemma code_at_dup f p : code_at f p -|- code_at f p ** code_at f p.
    Proof. apply bi.persistent_sep_dup; apply _. Qed.

    Lemma code_at_drop f p : code_at f p |-- empSP.
    Proof. auto. Qed.

    Parameter ctor_at : ptr -> Ctor -> mpred.
    Parameter dtor_at : ptr -> Dtor -> mpred.
  End with_Σ.
  Arguments mpred _ : clear implicits.
  Arguments mpredI _ : clear implicits.
  Arguments mpredSI _ : clear implicits.

  Existing Instance tptsto_timeless.

End logic.


Declare Module L : logic.

Export L.
