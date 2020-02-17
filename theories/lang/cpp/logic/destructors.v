(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred heap_pred wp.

Section with_resolve.
  Context {Σ:gFunctors} {resolve: genv}.
  Variable ti : thread_info.
  Variable ρ : region.

  Local Notation wp := (wp (Σ:=Σ)  ti ρ).
  Local Notation wpe := (wpe (Σ:=Σ) ti ρ).
  Local Notation wp_lval := (wp_lval (Σ:=Σ) ti ρ).
  Local Notation wp_rval := (wp_rval (Σ:=Σ) ti ρ).
  Local Notation wp_xval := (wp_xval (Σ:=Σ) ti ρ).
  Local Notation wpAny := (wpAny (Σ:=Σ) ti ρ).
  Local Notation wpAnys := (wpAnys (Σ:=Σ) ti ρ).
  Local Notation fspec := (fspec (Σ:=Σ)).

  Local Notation mpred := (mpred Σ) (only parsing).
  Local Notation Rep := (Rep Σ) (only parsing).

  Axiom wpd_deinit : forall resolve cls this path dn Q,
      Exists dp, Exists fp,
    (@_global resolve dn &~ dp **
     _offsetL (offset_for resolve cls path) (_eq this) &~ fp ** ltrue) //\\
     |> fspec (Vptr dp) ti (this :: nil) (fun _ => Q)
    |-- @wpd Σ resolve ti ρ cls this (path, dn) Q.

End with_resolve.
