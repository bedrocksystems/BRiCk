(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Lists.List.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp destroy.

Section with_resolve.
  Context `{Σ : cpp_logic thread_info} {σ: genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Definition type_of_field (cls : globname) (f : ident) : option type :=
    match σ.(genv_tu) !! cls with
    | None => None
    | Some (Gstruct st) =>
      match List.find (fun '(x,_,_,_) => bool_decide (f = x)) st.(s_fields) with
      | Some (_, ty, _, _) => Some ty
      | _ => None
      end
    | _ => None
    end.

  Definition get_type_of_path (from : globname) (p : FieldOrBase) : option type :=
    match p with
    | This => Some (Tnamed from)
    | Field fn => type_of_field from fn
    | Base gn => Some (Tnamed gn)
    | Indirect ls i =>
      (* this is a little bit awkward because we assume the correctness of
         the type annotations in the path
       *)
      (fix go (from : globname) (ls : _) : option type :=
         match ls with
         | nil => type_of_field from i
         | (_, gn) :: ls => go gn ls
         end) from ls
    end.

  Axiom wpd_deinit : forall (cls : globname) (this : val) path dn (Q : epred),
    Exists fp,
      (_offsetL (offset_for σ cls path) (_eqv this) &~ fp ** ltrue) //\\
      (match get_type_of_path cls path with
       | Some target_type =>
         destruct_val (σ:=σ) ti target_type (Vptr fp) (Some dn) Q
       | _ => lfalse
       end)
    |-- wpd (resolve:=σ) M ti ρ cls this (path, dn) Q.

End with_resolve.
