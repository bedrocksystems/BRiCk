(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export iris.proofmode.proofmode.

(* See https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/1041. *)
#[global] Remove Hints class_instances_frame.frame_bupd : typeclass_instances.
#[global] Remove Hints class_instances_frame.frame_fupd : typeclass_instances.
Section class_instances_frame.
  Context {PROP : bi}.
  Implicit Types P Q R : PROP.
  #[global] Instance frame_bupd `{!BiBUpd PROP} p R P Q :
    (FrameInstantiateExistDisabled → Frame p R P Q) →
    Frame p R (|==> P) (|==> Q) | 2.
  Proof. rewrite /Frame=>/(_ ltac:(constructor))<-. by rewrite bupd_frame_l. Qed.
  #[global] Instance frame_fupd `{!BiFUpd PROP} p E1 E2 R P Q :
    (FrameInstantiateExistDisabled → Frame p R P Q) →
    Frame p R (|={E1,E2}=> P) (|={E1,E2}=> Q) | 2.
  Proof. rewrite /Frame=>/(_ ltac:(constructor))<-. by rewrite fupd_frame_l. Qed.
End class_instances_frame.

(* https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/1042 *)
Import environments.
#[global]
Ltac iFrameAnyIntuitionistic ::=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => repeat iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     let Hs := eval lazy in (env_dom (env_intuitionistic Δ)) in go Hs
  end.

#[global]
Ltac iFrameAnySpatial ::=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => try iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     let Hs := eval lazy in (env_dom (env_spatial Δ)) in go Hs
  end.
