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
     ChargeUtil Logic PLogic Semantics Wp.

Module Type Call.

  Section with_resolve.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp := (wp (resolve:=resolve)  ti ρ).
    Local Notation wpe := (wpe (resolve:=resolve) ti ρ).
    Local Notation wp_lval := (wp_lval (resolve:=resolve) ti ρ).
    Local Notation wp_rval := (wp_rval (resolve:=resolve) ti ρ).
    Local Notation wp_prval := (wp_prval (resolve:=resolve) ti ρ).
    Local Notation wp_xval := (wp_xval (resolve:=resolve) ti ρ).
    Local Notation wp_init := (wp_init (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (resolve:=resolve) ti ρ).
    Local Notation fspec := (fspec (resolve:=resolve)).

    Fixpoint is_aggregate (t : type) : bool :=
      match t with
      | Tref _
      | Tarray _ _ => true
      | Tqualified _ t => is_aggregate t
      | _ => false
      end.

    Fixpoint wp_args (es : list (ValCat * Expr)) (Q : list val -> FreeTemps -> mpred) : mpred :=
      match es with
      | nil => Q nil empSP
      | (vc,e) :: es =>
        let ty := type_of e in
        match vc with
        | Lvalue => wp_lval e (fun v free => wp_args es (fun vs frees =>
                                                       Q (v :: vs) (free ** frees)))
        | Rvalue =>
          if is_aggregate ty then
            Forall a, _at (_eq a) (uninit (erase_qualifiers ty)) -*
                      wp_init ty a e (fun free => wp_args es (fun vs frees =>
                                                             Q (a :: vs) (_at (_eq a) (tany (erase_qualifiers ty)) ** free ** frees)))
          else
            wp_prval e (fun v free => wp_args es (fun vs frees =>
                                                Q (v :: vs) (free ** frees)))
        | Xvalue => wp_xval e (fun v free => wp_args es (fun vs frees =>
                                                       Q (v :: vs) (free ** frees)))
        end
      end.
    (* todo(gmm): check sequence points *)

  End with_resolve.

End Call.

Declare Module CALL : Call.

Export CALL.
