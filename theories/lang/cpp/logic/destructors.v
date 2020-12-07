(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Lists.List.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp destroy.
Require Import bedrock.lang.cpp.heap_notations.

Section with_resolve.
  Context `{Σ : cpp_logic thread_info} {σ: genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Axiom wpd_deinit : forall (cls : globname) (this : ptr) path dn (Q : epred),
      match type_of_path (σ:=σ) cls path with
      | Some target_type =>
        destruct_val (σ:=σ) ti target_type (this ., offset_for σ cls path) (Some dn) Q
      | _ => False
      end
    |-- wpd (resolve:=σ) M ti ρ cls this (path, dn) Q.

End with_resolve.
