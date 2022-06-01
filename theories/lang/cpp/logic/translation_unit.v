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

  Definition denoteSymbol (n : obj_name) (o : ObjValue) : mpred :=
    _global n |->
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

  (** [is_strict_valid o] states that if the declaration [o] occurs in a
      translation unit, the pointer to it is guaranteed to be strictly valid.
   *)
  Definition is_strict_valid o : Prop :=
    match o with
    | None => False
    | Some (Ovar t _) =>
        match drop_qualifiers t with
        | Tarray _ 0 => False
        | _ => True
        end
    | Some _ => True
    end.

  Lemma denoteSymbol_strict_valid n o :
    is_strict_valid (Some o) ->
    denoteSymbol n o |-- strict_valid_ptr (_global n).
  Proof.
    rewrite /is_strict_valid/denoteSymbol; destruct o.
    { case_match; intros; try by rewrite _at_svalidR.
      destruct n0; try tauto. by rewrite _at_svalidR. }
    all: case_match; by
        intros;rewrite !(_at_as_Rep, _at_svalidR,
      code_at_strict_valid, method_at_strict_valid, ctor_at_strict_valid, dtor_at_strict_valid).
  Qed.

  Lemma denoteSymbol_valid n o :
    denoteSymbol n o |-- valid_ptr (_global n).
  Proof.
    case: o. {
      rewrite /denoteSymbol => t o; repeat case_match => //=; intros;
        rewrite (_at_validR, _at_svalidR); trivial using strict_valid_valid.
    }
    all: intros; rewrite denoteSymbol_strict_valid //; apply strict_valid_valid.
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

  Lemma denoteModule_denoteSymbol n m o :
    m.(symbols) !! n = Some o ->
    denoteModule m |-- denoteSymbol n o.
  Proof.
    rewrite denoteModule_eq/denoteModule_def.
    intros; iIntros "[M _]".
    rewrite /lookup /symbol_lookup /= /lookup in H.
    rewrite /map_to_list /avl.IM_maptolist.
    assert (exists xs ys, avl.IM.elements (symbols m) = xs ++ (n, o) :: ys) as [ ? [ ? -> ] ].
    { apply avl.IM.find_2 in H.
      apply avl.IM.elements_1 in H.
      eapply SetoidList.InA_alt in H.
      destruct H as [ ? [ ? H ]].
      do 2 red in H0; simpl in H0. destruct H0; subst.
      eapply in_split in H.
      destruct x; apply H. }
    rewrite big_opL_app.
    rewrite big_opL_cons.
    by iDestruct "M" as "[_ [M _]]".
  Qed.

  Lemma denoteModule_strict_valid n m :
    is_strict_valid (m.(symbols) !! n) ->
    denoteModule m |-- strict_valid_ptr (_global n).
  Proof.
    rewrite /is_strict_valid.
    case_match; try tauto.
    intros; iIntros "M".
    iDestruct (denoteModule_denoteSymbol with "M") as "M"; eauto.
    iApply denoteSymbol_strict_valid; eauto.
  Qed.

  Lemma denoteModule_valid n m :
    m.(symbols) !! n <> None ->
    denoteModule m |-- valid_ptr (_global n).
  Proof.
    intros; iIntros "M".
    destruct (symbols m !! n) eqn:?; try congruence.
    iDestruct (denoteModule_denoteSymbol with "M") as "M"; eauto.
    by iApply denoteSymbol_valid.
  Qed.

  #[global] Instance denoteModule_models_observe tu : Observe [| tu ⊧ resolve |] (denoteModule tu).
  Proof.
    apply observe_intro_only_provable.
    rewrite denoteModule_eq/denoteModule_def.
    iIntros "[_ %]". iPureIntro. constructor.
    destruct (module_le_spec tu (genv_tu resolve)); eauto.
    destruct H.
  Qed.

End with_cpp.

Arguments denoteModule _ : simpl never.
