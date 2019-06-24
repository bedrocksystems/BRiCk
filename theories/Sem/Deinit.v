(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Util Logic PLogic Semantics Wp.

Module Type Deinit.

  Section with_resolve.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp := (wp (resolve:=resolve)  ti ρ).
    Local Notation wpe := (wpe (resolve:=resolve) ti ρ).
    Local Notation wp_lhs := (wp_lhs (resolve:=resolve) ti ρ).
    Local Notation wp_rhs := (wp_rhs (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (resolve:=resolve) ti ρ).
    Local Notation fspec := (fspec (resolve:=resolve)).

  (** destructor lists
   *
   *  the opposite of initializer lists, this is just a call to the
   *  destructors *in the right order*
   *)
  Parameter wpd
    : forall {resolve : genv} (ti : thread_info) (ρ : region)
        (cls : globname) (this : val)
        (init : FieldOrBase * globname)
        (Q : mpred), mpred.

  Fixpoint wpds
           (cls : globname) (this : val)
           (dests : list (FieldOrBase * globname))
           (Q : mpred) : mpred :=
    match dests with
    | nil => Q
    | d :: ds => @wpd resolve ti ρ cls this d (wpds cls this ds Q)
    end.

  End with_resolve.

End Deinit.

Declare Module D : Deinit.

Export D.
