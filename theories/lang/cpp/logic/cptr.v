(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From iris.bi Require Export monpred.
From iris.proofmode Require Import tactics monpred.
From iris_string_ident Require Import ltac2_string_ident.

Require Import bedrock.prelude.base.

From bedrock.lang.cpp Require Import
     semantics logic.pred logic.rep logic.wp.
Export bedrock.lang.cpp.logic.rep.

Section defs.
  Context `{Σ : cpp_logic}.

  (* this is the core definition that the program logic will be based on.
     it is really an assertion about assembly.
   *)
  Definition cptrR_def {resolve : genv} (fs : function_spec) : Rep :=
    as_Rep (fun p =>
         strict_valid_ptr p **
         □ (Forall vs Q,
         [| List.length vs = List.length fs.(fs_arguments) |] -*
         fs.(fs_spec) vs Q -*
         fspec resolve.(genv_tu).(globals) (type_of_spec fs) (Vptr p) vs Q)).
  Definition cptrR_aux : seal (@cptrR_def). Proof. by eexists. Qed.
  Definition cptrR := cptrR_aux.(unseal).
  Definition cptrR_eq : @cptrR = _ := cptrR_aux.(seal_eq).
End defs.

#[global] Instance: Params (@cptrR) 3 := {}.

#[global] Arguments cptrR {_ Σ resolve} _ : rename.

Section with_cpp.
  Context `{Σ : cpp_logic} {resolve : genv}.

  #[global] Instance cptrR_persistent {s} : Persistent (cptrR s).
  Proof. rewrite cptrR_eq. apply _. Qed.
  #[global] Instance cptrR_affine {s} : Affine (cptrR s).
  Proof. rewrite cptrR_eq. apply _. Qed.

  Lemma cptrR_strict_valid_observe (p : ptr) f : Observe (strict_valid_ptr p) (_at p (cptrR f)).
  Proof.
    apply observe_intro_persistent; refine _.
    rewrite cptrR_eq/cptrR_def _at_as_Rep.
    iIntros "[$ _]".
  Qed.

  (* NOTE this should become an instance. *)
  Lemma cptrR_valid_observe (p : ptr) f : Observe (valid_ptr p) (_at p (cptrR f)).
  Proof. apply observe_strict_valid_valid; apply cptrR_strict_valid_observe. Qed.

  Lemma cptrR_fs_impl f g :
    pureR (fs_impl f g) |-- cptrR f -* cptrR g.
  Proof.
    rewrite cptrR_eq/cptrR_def /pureR /as_Rep.
    constructor => p; rewrite Rep_wand_force; iIntros "#(%ty & fs_impl)" => /=.
    iIntros "(val & #rest)"; iFrame. iIntros (vs Q len).
    rewrite ty. iModIntro. iIntros "fs_g".
    iApply "rest"; first by apply length_type_of_spec in ty; rewrite -ty len.
    by iApply "fs_impl".
  Qed.

(* TODO: Proper wrt [genv_leq]. *)
  #[global] Instance cptrR_ne : NonExpansive cptrR.
  Proof.
    intros n P Q HPQ. rewrite cptrR_eq. rewrite/cptrR_def.
    rewrite (length_fs_arguments_ne _ _ _ HPQ) (type_of_spec_ne _ _ _ HPQ).
    apply as_Rep_ne=>p. (do 2!f_equiv). do 6 f_equiv. by apply fs_spec_ne.
  Qed.
  #[global] Instance cptrR_proper : Proper (equiv ==> equiv) cptrR.
  Proof. exact: ne_proper. Qed.

  #[global] Instance cptrR_mono : Proper (fs_entails ==> (⊢)) cptrR.
  Proof.
    intros ??; rewrite /fs_entails/flip => impl. iApply cptrR_fs_impl.
    by rewrite -impl pureR_emp.
  Qed.

  #[global] Instance cptrR_flip_mono : Proper (flip fs_entails ==> flip (⊢)) cptrR.
  Proof. by intros ?? <-. Qed.
End with_cpp.

#[global] Instance Persistent_spec `{Σ:cpp_logic ti} {resolve:genv} p s :
  Persistent (_at (Σ:=Σ) p (cptrR s)) := _.
