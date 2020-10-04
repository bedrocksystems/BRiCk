(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
From iris Require Import bi.bi.
From iris.proofmode Require Import tactics.
Require Import bedrock.lang.bi.prelude.
Import ChargeNotation.

Section with_PROP.
  Context {PROP : bi}.

  (* Original charge lemmas. *)
  Lemma ltrueR: forall (C : PROP), C |-- True.
  Proof. intros. iIntros "C". eauto. Qed.
  Lemma lfalseL: forall (C : PROP), False |-- C.
  Proof. intros. iIntros "[]". Qed.
  Lemma lexistsL: forall {T : Type} (P: T -> PROP) C, (forall x, P x |-- C) -> Exists y, P y |-- C.
  Proof. intros. iIntros "HP". iDestruct "HP" as (x) "HP". iApply H. eauto. Qed.
  Lemma lexistsR: forall {T : Type} (x : T) (P: T -> PROP) C, C |-- P x -> C |-- Exists y, P y.
  Proof. intros. iIntros "HC". iDestruct (H with "HC") as "HP". eauto. Qed.
  Lemma lforallL: forall {T : Type} x (P: T -> PROP) C, P x |-- C -> Forall y, P y |-- C.
  Proof. intros. iIntros "HP". iApply H. iApply ("HP" $!x). Qed.
  Lemma lforallR: forall {T : Type} (P: T -> PROP) C, (forall x, C |-- P x) -> C |-- Forall y, P y.
  Proof. intros. iIntros "HC". iIntros (y). iApply H. eauto. Qed.
  Lemma landL1: forall (P Q C : PROP), P |-- C  ->  P //\\ Q |-- C.
  Proof. intros. iIntros "[HP _]". iApply H; eauto. Qed.
  Lemma landL2: forall (P Q C : PROP), Q |-- C  ->  P //\\ Q |-- C.
  Proof. intros. iIntros "[_ HQ]". iApply H; eauto. Qed.
  Lemma lorR1:  forall (P Q C : PROP), C |-- P  ->  C |-- P \\// Q.
  Proof. intros. iIntros "HC". iLeft. iApply H; eauto. Qed.
  Lemma lorR2:  forall (P Q C : PROP), C |-- Q  ->  C |-- P \\// Q.
  Proof. intros. iIntros "HC". iRight. iApply H; eauto. Qed.
  Lemma landR:  forall (P Q C : PROP), C |-- P  ->  C |-- Q  ->  C |-- P //\\ Q.
  Proof. intros. iIntros "HC". iSplit; [iApply H | iApply H0]; eauto. Qed.
  Lemma lorL:   forall (P Q C : PROP), P |-- C  ->  Q |-- C  ->  P \\// Q |-- C.
  Proof. intros. iIntros "[HP |HQ]"; [iApply H | iApply H0]; eauto. Qed.
  Lemma landAdj: forall (P Q C : PROP), C |-- (P -->> Q) -> C //\\ P |-- Q.
  Proof.
    iIntros (P Q C HCP).
    iApply bi.impl_elim_l'. iIntros "HC". iApply HCP. iApply "HC".
  Qed.
  Lemma limplAdj: forall (P Q C : PROP), C //\\ P |-- Q -> C |-- (P -->> Q).
  Proof.
    iIntros (P Q C H) "HC".
    iApply bi.impl_intro_r. eauto. iApply "HC".
  Qed.

  (* Charge derivations *)
  Lemma embedPropR (p : Prop) (P : PROP) (H : p) : P |-- bi_pure p.
  Proof. eauto. Qed.

  Lemma wandSPI (P Q R : PROP) (HQ : P ** Q |-- R) : (P |-- Q -* R).
  Proof. intros. iIntros "HP HQ". iApply HQ; iFrame. Qed.

  Lemma sepSPC (P Q : PROP) : P ** Q |-- Q ** P.
  Proof. iIntros "[HP HQ]". iFrame. Qed.

  Lemma scME (P Q R S : PROP) (HPR: P |-- R) (HQS: Q |-- S) :
    P ** Q |-- R ** S.
  Proof. iIntros "[HP HQ]". rewrite HPR. rewrite HQS. iFrame. Qed.

  Lemma sepSPAdj (P Q C : PROP) (HWand: C |-- P -* Q) : C ** P |-- Q.
  Proof. iIntros "[HC HP]". rewrite HWand. iApply "HC". eauto. Qed.

  Lemma embedPropExists (p : Prop) : (embed p : PROP) |-- Exists x : p, ltrue.
  Proof. eauto. Qed.
  Lemma embedPropExistsL (p : Prop) (P : PROP) : Exists x : p, P |-- embed p.
  Proof. iIntros "H". iDestruct "H" as (Hp) "H". iPureIntro. eauto. Qed.

  (* TODO rename embedPropExists to embedPropExistsR *)
  Lemma embedPropExists' (p : Prop) : Exists x : p, (ltrue : PROP) -|- embed p.
  Proof. simpl. split'; [ apply embedPropExistsL | iApply embedPropExists ]. Qed.

  Lemma landexistsDL1 {T} (f : T -> PROP) (P : PROP) :
    Exists y, f y //\\ P |-- Exists a, (f a //\\ P).
  Proof.
    iIntros "H".
    iDestruct "H" as (y) "H".
    iExists y.
    iSplit.
    iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ $]".
  Qed.

  Lemma landtrueL : forall (a : PROP), ltrue //\\ a -|- a.
  Proof. intros. split'. eapply landL2. reflexivity. apply landR; eauto. Qed.

  Lemma bilexistssc {T} (P : PROP) (Q : T -> PROP) :
    Exists x : T, P ** Q x -|- P ** Exists y, Q y.
  Proof.
    iSplit.
    - iIntros "H".
      iDestruct "H" as (x) "[$ HQ]".
      iExists x. iFrame.
    - iIntros "[HP HQ]".
      iDestruct "HQ" as (y) "HQ".
      iExists y. iFrame.
  Qed.
  Lemma wandSPAdj' (P Q C : PROP) (HSep: P ** C |-- Q) : C |-- P -* Q.
  Proof. iIntros "HC HP". iApply HSep. iFrame. Qed.

  Lemma sepSP_falseL (P : PROP) : lfalse ** P -|- lfalse.
  Proof.
    iSplit.
    { iIntros "[$ HP]". }
    { iIntros "F". iStopProof. eapply lfalseL. }
  Qed.

  Lemma wandSP_cancel : forall P Q R F : PROP,
      R |-- P ** F ->
      (P -* Q) ** R |-- Q ** F.
  Proof.
    intros.
    rewrite -> H; clear H.
    iIntros "(HPQ & HP & HF)". iFrame. by iApply "HPQ".
  Qed.

  Lemma bilforallscR {T} (P : PROP) (Q : T -> PROP) :
    P ** (Forall y, Q y) |-- Forall x : T, P ** Q x.
  Proof.
    apply lforallR; intro x.
    iIntros "[$ HQ]".
    iSpecialize ("HQ" $!x). eauto.
  Qed.

  Lemma wandSepSPAdj : forall (P Q R : PROP), sepSP P Q |-- R <-> P |-- wandSP Q R.
  Proof.
    split.
    intros. rewrite <- H. iIntros "HP HQ". iFrame.
    intros. rewrite -> H. iIntros "[HQR HQ]". iDestruct ("HQR" with "HQ") as "HR". iFrame.
  Qed.

  Lemma wandSPAdj (P Q C : PROP) (HSep: C ** P |-- Q) : C |-- P -* Q.
  Proof. apply wandSepSPAdj; assumption. Qed.

  Lemma bilexistsscR2 {T} (P : PROP) (f : T -> PROP):
    Exists x : T, f x ** P |-- (Exists y, f y) ** P.
  Proof.
    iIntros "H".
    iDestruct "H" as (x) "[Hf HP]". iFrame.
    eauto.
  Qed.

  Lemma bilexistsscL1 {T} (P : PROP) (f : T -> PROP) :
    P ** lexists f |-- Exists x : T, P ** f x.
  Proof.
    rewrite -> sepSPC; rewrite -> wandSepSPAdj.
    apply lexistsL; intro x; erewrite <- wandSPAdj. reflexivity.
    eapply lexistsR; rewrite sepSPC; reflexivity.
  Qed.

  Lemma bilexistsscL2 {T} (P : PROP) (f : T -> PROP) :
    lexists f ** P |-- Exists x : T, f x ** P.
  Proof.
    rewrite -> sepSPC, bilexistsscL1.
    setoid_rewrite sepSPC at 1.
    reflexivity.
  Qed.

  Lemma wandSPL (P Q : PROP) CL CR (HP: CL |-- P) (HR: Q |-- CR) :
    (P -* Q) ** CL |-- CR.
  Proof. rewrite <-HR, <-HP. apply sepSPAdj. reflexivity. Qed.

  Lemma sepSPA1 : forall (P Q R : PROP), sepSP (sepSP P Q) R |-- sepSP P (sepSP Q R).
  Proof. intros. iIntros "[[$ $] $]". Qed.
  Lemma sepSPA2 (P Q R : PROP) : P ** (Q ** R) |-- (P ** Q) ** R.
  Proof. intros. iIntros "[$ [$ $]]". Qed.
  Lemma sepSPA (P Q R : PROP) : (P ** Q) ** R -|- P ** (Q ** R).
  Proof. iSplit; [ iApply sepSPA1 | iApply sepSPA2 ]. Qed.

  Lemma wandSPE (P Q R S : PROP) (HQR: Q |-- S -* R) (HP : P |-- Q ** S) : P |-- R.
  Proof.
    apply sepSPAdj in HQR.
    rewrite <- HQR, HP. reflexivity.
  Qed.

  Lemma empSPR : forall (P : PROP), sepSP P empSP -|- P.
  Proof. intros. iSplit. iIntros "[$ _]". iIntros "$". Qed.

  Lemma lexists_known : forall t a (P : t -> PROP),
    Exists x : t, [| x = a |] ** P x -|- P a.
  Proof.
    intros. iSplit.
    - iIntros "H". iDestruct "H" as (x) "[-> H]". subst; eauto.
    - iIntros "HP". iExists a. eauto.
  Qed.

  Lemma bilsep (P Q R : PROP) : P |-- Q -> sepSP P R |-- sepSP Q R.
  Proof. intros. rewrite -> H. reflexivity. Qed.

  Lemma bilorscDL (P Q R : PROP) : (P \\// Q) ** R -|- (P ** R) \\// (Q ** R).
  Proof.
    split'.
    + apply wandSepSPAdj; apply lorL; apply wandSepSPAdj;
  	[apply lorR1 | apply lorR2]; reflexivity.
    + apply lorL; apply bilsep; [apply lorR1 | apply lorR2]; reflexivity.
  Qed.

  Lemma lforall_specialize : forall {T} (x : T) (P : T -> PROP),
    lforall P |-- P x.
  Proof. intros. eapply lforallL. reflexivity. Qed.

  Lemma sepSPC1 (P Q : PROP) : sepSP P Q |-- sepSP Q P.
  Proof. iIntros "[HP HQ]". iFrame. Qed.

  Lemma sepSPAdj' (P Q C : PROP) (HWand: C |-- P -* Q) : P ** C |-- Q.
  Proof.
    etransitivity; [apply sepSPC1| ]. apply wandSepSPAdj. assumption.
  Qed.

End with_PROP.

Section with_SPROP.
  Context {SPROP: bi}.
  Lemma spec_later_weaken (P : SPROP) : P |-- illater P.
  Proof. eauto. Qed.

  Lemma later_sep : forall (P Q R : SPROP),
      (|> P) ** Q |-- R ->
      P ** Q |-- R.
  Proof.
    intros. rewrite <- H.
    rewrite <- spec_later_weaken.
    eauto.
  Qed.

End with_SPROP.
