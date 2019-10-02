(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Local Open Scope string_scope.
Local Open Scope Z_scope.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     ChargeUtil Logic PLogic Semantics Wp Destroy Intensional.

Module Type Call.

  Section with_resolve.
    Context {Σ:gFunctors}.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp := (wp (Σ:=Σ) (resolve:=resolve)  ti ρ).
    Local Notation wpe := (wpe (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_lval := (wp_lval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_rval := (wp_rval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_prval := (wp_prval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_xval := (wp_xval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_init := (wp_init (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation fspec := (fspec (Σ:=Σ) (resolve:=resolve)).

    Local Notation mpred := (mpred Σ) (only parsing).
    Local Notation FreeTemps := (FreeTemps Σ) (only parsing).

    Fixpoint wp_args (es : list (ValCat * Expr)) (Q : list val -> FreeTemps -> mpred) : mpred :=
      match es with
      | nil => Q nil empSP
      | (vc,e) :: es =>
        let ty := type_of e in
        match vc with
        | Lvalue =>
          wp_lval e (fun v free =>
                       wp_args es (fun vs frees => Q (v :: vs) (free ** frees)))
        | Rvalue =>
          if is_aggregate ty then
            Forall a, _at (_eq a) (uninit (erase_qualifiers ty)) -*
                      let (e,dt) := destructor_for e in
                      wp_init ty a e (fun free => wp_args es (fun vs frees =>
                                                             Q (a :: vs) (mdestroy (resolve:=resolve) ti ty a dt free ** frees)))
          else
            wp_prval e (fun v free => wp_args es (fun vs frees =>
                                                Q (v :: vs) (free ** frees)))
        | Xvalue => wp_xval e (fun v free => wp_args es (fun vs frees =>
                                                       Q (v :: vs) (free ** frees)))
        end
      end.

  End with_resolve.

End Call.

Declare Module CALL : Call.

Export CALL.
