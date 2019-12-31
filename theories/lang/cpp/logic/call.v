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

Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred heap_pred wp destroy intensional.

Module Type Call.

  Section with_resolve.
    Context {Σ:gFunctors}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp := (wp (Σ:=Σ) ti ρ).
    Local Notation wpe := (wpe (Σ:=Σ) ti ρ).
    Local Notation wp_lval := (wp_lval (Σ:=Σ) ti ρ).
    Local Notation wp_rval := (wp_rval (Σ:=Σ) ti ρ).
    Local Notation wp_prval := (wp_prval (Σ:=Σ) ti ρ).
    Local Notation wp_xval := (wp_xval (Σ:=Σ) ti ρ).
    Local Notation wp_init := (wp_init (Σ:=Σ) ti ρ).
    Local Notation wpAny := (wpAny (Σ:=Σ) ti ρ).
    Local Notation wpAnys := (wpAnys (Σ:=Σ) ti ρ).
    Local Notation fspec := (fspec (Σ:=Σ)).

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
            Forall a, _at (_eq a) (uninit (erase_qualifiers ty) 1) -*
                      let (e,dt) := destructor_for e in
                      wp_init ty a e (fun free => wp_args es (fun vs frees =>
                                                             Q (a :: vs) (mdestroy ti ty a dt free ** frees)))
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
