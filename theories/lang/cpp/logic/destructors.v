(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Lists.List.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp.

Section with_resolve.
  Context `{Σ : cpp_logic thread_info} {σ: genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Axiom wpd_deinit : forall (cls : globname) (this : val) path dn (Q : epred),
    Exists dp, Exists fp,
      (_global (resolve:=σ) dn &~ dp **
       _offsetL (offset_for σ cls path) (_eqv this) &~ fp ** ltrue) //\\
      (|> fspec ti (Vptr dp) (this :: nil) (fun _ => Q))
    |-- wpd (resolve:=σ) M ti ρ cls this (path, dn) Q.

End with_resolve.
