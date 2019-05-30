(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Cpp Require Import
     Auto.
Require Import Cpp.Sem.Linking.
From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Demo Require
     A_hpp A_hpp_spec A_hpp_proof
     A_cpp A_cpp_spec A_cpp_proof.
Import A_hpp_spec.

(* todo(gmm): I'm a bit confused about the appropriate specification of linking
 *)
Lemma wand_apply : forall A B F F' : mpred,
    F |-- A ** F' ->
    (A -* B) ** F |-- B ** F'.
Proof.
  intros.
  rewrite H.
  work.
  rewrite sepSPC.
  eapply sepSPAdj.
  reflexivity.
Qed.

Theorem A_o_sound (resolve : _)
: |-- denoteModule (module_link A_hpp.module A_cpp.module) -*
      (Forall ti, cglob' (resolve:=resolve) A__foo ti A__foo_spec) **
      (Forall ti, cglob' (resolve:=resolve) A__bar ti A__bar_spec).
Proof.
  eapply spec_lob.
  eapply wandSPAdj.
  rewrite denote_module_dup at 2.
  rewrite denoteModule_link.
  rewrite (A_cpp_proof.A_cpp_sound resolve) at 2.
  rewrite (A_hpp_proof.A_hpp_sound resolve) at 2.
  unfold A_hpp_spec, A_cpp_spec.A_cpp_spec.
  do 2 Discharge.perm_right ltac:(idtac; Discharge.perm_left ltac:(eapply wand_apply)).
  rewrite illater_wandSP.
  rewrite <- illater_sepSP.
  Discharge.perm_right ltac:(idtac; Discharge.perm_left ltac:(eapply wand_apply)).
  rewrite <- spec_later_weaken.
  Discharge.discharge fail idtac fail ltac:(Discharge.canceler fail eauto) eauto.
Qed.
