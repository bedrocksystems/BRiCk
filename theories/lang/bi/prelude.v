(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.bi Require Import bi.
From iris.proofmode Require Import tactics.
From bedrock.lang.bi Require Export only_provable derived_laws.

Set Default Proof Using "Type".

(** * Notation for functions in the Iris scope. To upstream,
per https://gitlab.mpi-sws.org/iris/iris/-/issues/320. *)
Notation "'λI' x .. y , t" := (fun x => .. (fun y => t%I) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : function_scope.

(* ASCII variant. *)
Notation "'funI' x .. y => t" := (fun x => .. (fun y => t%I) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : function_scope.

Global Notation lentails := (bi_entails) (only parsing).
Global Notation lequiv := (≡) (only parsing).
Global Notation ltrue := (True%I) (only parsing).
Global Notation lfalse := (False%I) (only parsing).
Global Notation land := (bi_and) (only parsing).
Global Notation lor := (bi_or) (only parsing).
Global Notation limpl := (bi_impl) (only parsing).
Global Notation lforall := (bi_forall) (only parsing).
Global Notation lexists := (bi_exist) (only parsing).

Global Notation empSP := (bi_emp) (only parsing).
Global Notation sepSP := (bi_sep) (only parsing).
Global Notation wandSP := (bi_wand) (only parsing).
Global Notation illater := (bi_later) (only parsing).

Global Notation "[! P !]" := (bi_pure P).

Ltac split' := intros; apply (anti_symm (⊢)).

(* Charge notation levels *)
Module ChargeNotation.

  Notation "P |-- Q"  := (P%I ⊢ Q%I) (at level 80, no associativity).
  Notation "P '|-@{' PROP } Q" := (P%I ⊢@{PROP} Q%I)
    (at level 80, no associativity, only parsing).

  Notation "P //\\ Q"   := (P ∧ Q)%I (at level 75, right associativity).
  Notation "P \\// Q"   := (P ∨ Q)%I (at level 76, right associativity).
  Notation "P -->> Q"   := (P → Q)%I (at level 77, right associativity).
  Notation "'Forall' x .. y , p" :=
    (lforall (fun x => .. (lforall (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).

  Notation "'Exists' x .. y , p" :=
    (lexists (fun x => .. (lexists (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).

  Notation "|--  P" := (⊢ P%I) (at level 85, no associativity).
  Notation "'|-@{' PROP } P" := (⊢@{PROP} P%I)
    (at level 85, no associativity, only parsing).

  Notation "P ** Q" := (P ∗ Q)%I (at level 58, right associativity).
  Notation "P -* Q" := (P -∗ Q)%I (at level 60, right associativity).
  Notation "'sepSPs' ps" := ([∗] ps)%I (at level 20).

  (* Notation "'|>' P" := (▷  P)%I (at level 71). *)
  Notation "|> P" := (▷  P)%I (at level 20, right associativity).

  Notation "P -|- Q"  := (P%I ≡ Q%I) (at level 85, no associativity).
  Notation "P '-|-@{' PROP } Q"  := (P%I ⊣⊢@{PROP} Q%I)
    (at level 85, no associativity, only parsing).

End ChargeNotation.
