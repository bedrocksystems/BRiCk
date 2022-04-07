(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** this module provides a denotational/axiomatic semantics to c++ compilation
    units.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp Require Import
     semantics logic.pred logic.path_pred logic.heap_pred.
From bedrock.lang.cpp Require Import logic.wp.
Require Import iris.proofmode.proofmode.

Import ChargeNotation.

Section with_cpp.
  Context `{Σ : cpp_logic} {resolve:genv}.

  Set Default Proof Using "Σ resolve".

  Local Notation code_at := (@code_at _ Σ) (only parsing).
  Local Notation method_at := (@method_at _ Σ) (only parsing).
  Local Notation ctor_at := (@ctor_at _ Σ) (only parsing).
  Local Notation dtor_at := (@dtor_at _ Σ) (only parsing).
  Local Open Scope bi_scope. (*Does this scope need to be exported?*)

  Definition denoteSymbol (n : obj_name) (o : ObjValue) : mpred :=
    _at (_global n)
        match o with
        | Ovar t e =>
          (* no need for [erase_qualifiers], we only check the head *)
          match drop_qualifiers t with
          | Tarray _ 0 =>
            (* TODO: maybe arrays of unknown size should also use [validR]? *)
            validR
          | _ =>
            svalidR
          end
        | Ofunction f =>
          match f.(f_body) with
          | None => svalidR
          | Some body => as_Rep (code_at resolve f)
          end
        | Omethod m =>
          match m.(m_body) with
          | None => svalidR
          | Some body => as_Rep (method_at resolve m)
          end
        | Oconstructor c =>
          match c.(c_body) with
          | None => svalidR
          | Some body => as_Rep (ctor_at resolve c)
          end
        | Odestructor d =>
          match d.(d_body) with
          | None => svalidR
          | Some body => as_Rep (dtor_at resolve d)
          end
        end.

  #[global] Instance denoteSymbol_persistent {n o} : Persistent (denoteSymbol n o).
  Proof. rewrite /denoteSymbol; repeat case_match; apply _. Qed.

  #[global] Instance denoteSymbol_affine {n o} : Affine (denoteSymbol n o) := _.

  Lemma denoteSymbol_fun_strict_valid n o :
    match o with | Ovar _ _ => False | _ => True end ->
    denoteSymbol n o |-- strict_valid_ptr (_global n).
  Proof.
    rewrite /denoteSymbol; destruct o => // _; case_match.
    all: by rewrite !(_at_as_Rep, _at_svalidR,
      code_at_strict_valid, method_at_strict_valid, ctor_at_strict_valid, dtor_at_strict_valid).
  Qed.

  Lemma denoteSymbol_valid n o :
    denoteSymbol n o |-- valid_ptr (_global n).
  Proof.
    case: o. {
      rewrite /denoteSymbol => t o; repeat case_match => //=; intros;
        rewrite (_at_validR, _at_svalidR); trivial using strict_valid_valid.
    }
    all: intros; rewrite denoteSymbol_fun_strict_valid //; apply strict_valid_valid.
  Qed.

  Definition initSymbol (n : obj_name) (o : ObjValue) : mpred :=
    _at (_global n)
        match o with
        | Ovar t (Some e) =>
          emp (*
      Exists Q : FreeTemps -> mpred,
      □ (_at (_eq a) (uninitR (resolve:=resolve) t 1) -*
         Forall ρ ti, wp_init (resolve:=resolve) ti ρ t (Vptr a) e Q) ** Q emp
*)
      (* ^^ todo(gmm): static initialization is not yet supported *)
        | Ovar t None =>
          uninitR (resolve:=resolve) t 1
        | _ => emp
        end.

  Definition denoteModule_def (d : translation_unit) : mpred :=
    ([∗list] sv ∈ map_to_list d.(symbols), denoteSymbol sv.1 sv.2) **
    [| module_le d resolve.(genv_tu) |].
  Definition denoteModule_aux : seal (@denoteModule_def). Proof. by eexists. Qed.
  Definition denoteModule := denoteModule_aux.(unseal).
  Definition denoteModule_eq : @denoteModule = _ := denoteModule_aux.(seal_eq).

  #[global] Instance denoteModule_persistent {module} : Persistent (denoteModule module).
  Proof.
    red. rewrite denoteModule_eq /denoteModule_def; intros.
    destruct module; simpl.
    iIntros "[#M #H]"; iFrame "#".
  Qed.

  #[global] Instance denoteModule_affine {module} : Affine (denoteModule module).
  Proof using . refine _. Qed.

End with_cpp.

Arguments denoteModule _ : simpl never.
