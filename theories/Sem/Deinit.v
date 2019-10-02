(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     ChargeUtil Logic PLogic Semantics Wp.

Module Type Deinit.

  Section with_resolve.
    Context {Σ:gFunctors}.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp := (wp (Σ:=Σ) (resolve:=resolve)  ti ρ).
    Local Notation wpe := (wpe (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_lval := (wp_lval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_rval := (wp_rval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_xval := (wp_xval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation fspec := (fspec (Σ:=Σ) (resolve:=resolve)).

    Local Notation mpred := (mpred Σ) (only parsing).
    Local Notation Rep := (Rep Σ) (only parsing).

    (** destructor lists
     *
     *  the opposite of initializer lists, this is just a call to the
     *  destructors *in the right order*
     *)
    Parameter wpd
      : forall {resolve : genv} (ti : thread_info) (ρ : region)
          (cls : globname) (this : val)
          (init : FieldOrBase * obj_name)
          (Q : mpred), mpred.

    Fixpoint wpds
             (cls : globname) (this : val)
             (dests : list (FieldOrBase * globname))
             (Q : mpred) : mpred :=
      match dests with
      | nil => Q
      | d :: ds => @wpd resolve ti ρ cls this d (wpds cls this ds Q)
      end.

    Axiom wpd_deinit : forall cls this path dn Q,
        Exists dp, Exists fp,
           (_global dn &~ dp **
            _offsetL (offset_for cls path) (_eq this) &~ fp ** ltrue) //\\
                   |> fspec dp (this :: nil) ti (fun _ => Q)
        |-- wpd (resolve:=resolve) ti ρ cls this (path, dn) Q.

  End with_resolve.

End Deinit.

Declare Module D : Deinit.

Export D.
