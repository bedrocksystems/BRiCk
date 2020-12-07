(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

(** this module provides a denotational/axiomatic semantics to c++ compilation
    units.
 *)
Require Import bedrock.lang.prelude.base.
Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp Require Import
     semantics logic.pred logic.path_pred logic.heap_pred.
From bedrock.lang.cpp Require Import logic.wp.
Require Import iris.proofmode.tactics.

Import ChargeNotation.

Section with_cpp.
  Context `{Σ : cpp_logic} {resolve:genv}.

  Set Default Proof Using "Σ resolve".

  Local Notation _global := (_global (Σ:=Σ) (resolve:=resolve)) (only parsing).
  Local Notation code_at := (@code_at _ Σ) (only parsing).
  Local Notation method_at := (@method_at _ Σ) (only parsing).
  Local Notation ctor_at := (@ctor_at _ Σ) (only parsing).
  Local Notation dtor_at := (@dtor_at _ Σ) (only parsing).
  Local Notation _field := (@_field resolve) (only parsing).
  Local Notation _base := (@_base resolve) (only parsing).
  Local Notation _sub := (@_sub resolve) (only parsing).

  Definition denoteSymbol (n : obj_name) (o : ObjValue) : mpred :=
    Exists a, _global n &~ a **
    match o with
    | Ovar _ e => empSP
    | Ofunction f =>
      match f.(f_body) return mpred with
      | None => empSP
      | Some body => code_at resolve f a
      end
    | Omethod m =>
      match m.(m_body) return mpred with
      | None => emp
      | Some body =>
        method_at resolve m a
      end
    | Oconstructor c =>
      match c.(c_body) return mpred with
      | None => empSP
      | Some body => ctor_at resolve c a
      end
    | Odestructor d =>
      match d.(d_body) return mpred with
      | None => empSP
      | Some body => dtor_at resolve d a
      end
    end.

  Global Instance: Persistent (denoteSymbol n o).
  Proof using .
    rewrite /denoteSymbol; destruct o; simpl; red.
    - iIntros "#H"; iModIntro; iFrame "#".
    - iIntros "#H"; iModIntro; iFrame "#".
    - iIntros "#H"; iModIntro; iFrame "#".
    - iIntros "#H"; iModIntro; iFrame "#".
    - iIntros "#H"; iModIntro; iFrame "#".
  Qed.

  Global Instance: Affine (denoteSymbol n o).
  Proof using . refine _. Qed.

  Definition initSymbol (n : obj_name) (o : ObjValue) : mpred :=
    Exists a, _global n &~ a **
    match o with
    | Ovar t (Some e) =>
      ltrue (*
      Exists Q : FreeTemps -> mpred,
      □ (_at (_eq a) (uninitR (resolve:=resolve) t 1) -*
         Forall ρ ti, wp_init (resolve:=resolve) ti ρ t (Vptr a) e Q) ** Q empSP
*)
      (* ^^ todo(gmm): static initialization is not yet supported *)
    | Ovar t None =>
      _at (_eq a) (uninitR (resolve:=resolve) t 1)
    | _ => empSP
    end.

  Definition denoteModule_def (d : translation_unit) : mpred :=
    ([∗list] sv ∈ map_to_list d.(symbols), denoteSymbol sv.1 sv.2) **
    [| module_le d resolve.(genv_tu) |].
  Definition denoteModule_aux : seal (@denoteModule_def). Proof. by eexists. Qed.
  Definition denoteModule := denoteModule_aux.(unseal).
  Definition denoteModule_eq : @denoteModule = _ := denoteModule_aux.(seal_eq).

  Global Instance: Persistent (denoteModule module).
  Proof.
    red. rewrite denoteModule_eq /denoteModule_def; intros.
    destruct module; simpl.
    iIntros "[#M #H]"; iFrame "#".
  Qed.

  Global Instance: Affine (denoteModule module).
  Proof using . refine _. Qed.

End with_cpp.

Arguments denoteModule _ : simpl never.
