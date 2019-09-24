(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(* Automation for high-level verification conditions *)
From Cpp Require Export Parser Sem.
From Cpp.Auto Require Lemmas type.

From Cpp.Auto Require Export Discharge Definitions.
Require Cpp.Auto.sep.

Require Import bedrock.auto.drop_to_emp.

Ltac start_proof :=
  try unfold func_ok, ctor_ok, method_ok; intros; simpl; sep.work;
  repeat
    lazymatch goal with
    | H : prod _ _ |- _ => destruct H
    | |- ?L |-- _ =>
          match L with
          | context [ empSP ] => sep.work
          end
    end.

Ltac done_proof :=
  (* repeat rewrite Cpp.Auto.Lemmas.cglob'_weaken; *)
  (* repeat rewrite ti_cglob'_weaken; *)
  try rewrite denoteModule_weaken;
  repeat rewrite later_empSP ;
  sep.work ;
  drop_to_emp ;
  solve [ sep.work ].

(* used for doing case splits *)
Ltac vc_split :=
  match goal with
  | |- context [ if is_true (Vint (if ?X then _ else _)) then _ else _ ] =>
    rewrite is_true_int; destruct X; simpl
  end.
