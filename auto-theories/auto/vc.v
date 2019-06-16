(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(* Automation for high-level verification conditions *)
From Cpp Require Export Parser Sem.
From Cpp.Auto Require Lemmas type.

From Cpp.Auto Require Export Discharge Definitions.

Ltac start_proof :=
  try unfold func_ok'; intros; simpl; work;
  repeat
    lazymatch goal with
    | H : prod _ _ |- _ => destruct H
    | |- ?L |-- _ =>
          match L with
          | context [ empSP ] => work
          end
    end.

Ltac done_proof :=
  repeat rewrite cglob'_weaken;
  repeat rewrite ti_cglob'_weaken;
  try rewrite denoteModule_weaken;
  repeat rewrite later_empSP ;
  solve [ work ].

(* used for doing case splits *)
Ltac vc_split :=
  match goal with
  | |- context [ if is_true (Vint (if ?X then _ else _)) then _ else _ ] =>
    rewrite is_true_int; destruct X; simpl
  end.
