(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp destroy.

Section with_resolve.
  Context `{Σ : cpp_logic} {σ : genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Local Notation wp_lval := (wp_lval (resolve:=σ) M ti ρ).
  Local Notation wp_prval := (wp_prval (resolve:=σ) M ti ρ).
  Local Notation wp_xval := (wp_xval (resolve:=σ) M ti ρ).
  Local Notation wp_init := (wp_init (resolve:=σ) M ti ρ).

  Fixpoint wp_args (es : list (ValCat * Expr)) (Q : list val -> FreeTemps -> mpred)
  : mpred :=
    match es with
    | nil => Q nil empSP
    | (vc,e) :: es =>
      let ty := type_of e in
      match vc with
      | Lvalue =>
        Exists Qarg,
        wp_lval e Qarg **
          wp_args es (fun vs frees => Forall v free,
                                   Qarg v free -* Q (v :: vs) (free ** frees))
      | Prvalue =>
        if is_aggregate ty then
          Forall a, _at (_eq a) (anyR (resolve:=σ) (erase_qualifiers ty) 1) -*
          let (e,dt) := destructor_for e in
          Exists Qarg,
          wp_init ty (Vptr a) e Qarg **
            wp_args es (fun vs frees =>
                          Forall free,
                          Qarg free -* Q (Vptr a :: vs) (destruct_val (σ:=σ) ti ty (Vptr a) dt (_at (_eq a) (anyR (resolve:=σ) (erase_qualifiers ty) 1) ** free) ** frees))
        else
          Exists Qarg,
          wp_prval e Qarg **
            wp_args es (fun vs frees => Forall v free,
                                     Qarg v free -* Q (v :: vs) (free ** frees))
      | Xvalue =>
        Exists Qarg,
        wp_xval e Qarg **
            wp_args es (fun vs frees => Forall v free,
                                     Qarg v free -* Q (v :: vs) (free ** frees))
      end
    end.

End with_resolve.
