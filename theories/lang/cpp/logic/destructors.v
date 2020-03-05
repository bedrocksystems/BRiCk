(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp.

Section with_resolve.
  Context `{Σ : cpp_logic thread_info} {σ: genv}.
  Variable ti : thread_info.
  Variable ρ : region.

  Axiom wpd_deinit : forall (cls : globname) (this : val) path dn (Q : epred),
    Exists dp, Exists fp,
      (@_global σ dn &~ dp **
       _offsetL (offset_for σ cls path) (_eqv this) &~ fp ** ltrue) //\\
      (|> fspec ti (Vptr dp) (this :: nil) (fun _ => Q))
    |-- wpd (resolve:=σ) ti ρ cls this (path, dn) Q.

End with_resolve.
