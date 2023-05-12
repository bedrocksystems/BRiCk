(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
This file defines the core [bi] (called [mpred]) that we use for C++.
The core logic is defined in [pred.v]. *)
From iris.base_logic.lib Require Import own cancelable_invariants.
Require Import iris.bi.monpred.

From bedrock.prelude Require Import base.
From bedrock.lang Require Import bi.prelude.
Import ChargeNotation.

Module Type CPP_LOGIC_CLASS_BASE.
  Parameter cppG : gFunctors -> Type.
  Axiom has_inv : forall Σ, cppG Σ -> invGS Σ.
  Axiom has_cinv : forall Σ, cppG Σ -> cinvG Σ.

  #[global] Existing Instances has_inv has_cinv.

  Existing Class cppG.

  Parameter _cpp_ghost : Type.
End CPP_LOGIC_CLASS_BASE.

Module Type CPP_LOGIC_CLASS_MIXIN (Import CC : CPP_LOGIC_CLASS_BASE).

  Class cpp_logic {thread_info : biIndex} : Type :=
  { _Σ       : gFunctors
  ; _ghost   : _cpp_ghost
  ; has_cppG : cppG _Σ
  }.
  Arguments cpp_logic : clear implicits.
  Coercion _Σ : cpp_logic >-> gFunctors.

  #[global] Existing Instance has_cppG.

  Section with_cpp.
    Context `{cpp_logic ti}.

    Definition mpredI : bi := monPredI ti (iPropI _Σ).
    Definition mpred := bi_car mpredI.

    (* TODO: seal *)
    Canonical Structure mpredO : ofe
      := Ofe mpred (ofe_mixin (monPredO ti (iPropI _Σ))).

    (* We name this, for manual use later when importing [linearity]. *)
    Lemma mpred_BiAffine : BiAffine mpred.
    Proof. apply _. Qed.
  End with_cpp.

  Bind Scope bi_scope with mpred.
End CPP_LOGIC_CLASS_MIXIN.

Module Type CPP_LOGIC_CLASS := CPP_LOGIC_CLASS_BASE <+ CPP_LOGIC_CLASS_MIXIN.

Declare Module LC : CPP_LOGIC_CLASS.
Export LC.

(**
To implement higher-order ghost state mentioning [mpred], we
presuppose [mpred ≈ I -mon> iProp] and use the discrete OFE [I -d>
iProp Σ] rather than [monPredO]. We cannot use [monPredO] because Iris
lacks a functor [monPredOF].
*)
Definition later_mpredO (Σ : gFunctors) (ti : biIndex) : ofe :=
  laterO (ti -d> iPropI Σ).
Definition later_mpredOF (ti : biIndex) : oFunctor :=
  laterOF (ti -d> idOF).
Definition later_mpred `{Σ : cpp_logic ti} (P : mpred) :
    later (ti -d> iPropI Σ) :=
  Next (monPred_at P).

Section later_mpred.
  Context `{Σ : cpp_logic ti}.

  #[global] Instance later_mpred_contractive : Contractive later_mpred.
  Proof.
    move => n ?? HP. apply: Next_contractive.
    dist_later_intro. destruct n as [|n]; [lia | by destruct HP].
  Qed.
  #[global] Instance later_mpred_ne : NonExpansive later_mpred.
  Proof. exact: contractive_ne. Qed.
  #[global] Instance later_mpred_proper : Proper (equiv ==> equiv) later_mpred.
  Proof. exact: ne_proper. Qed.

  Lemma equivI_later_mpred P Q :
    later_mpred P ≡ later_mpred Q -|-@{mpredI} |> (P ≡ Q).
  Proof.
    rewrite /later_mpred later_equivI.
    by rewrite discrete_fun_equivI monPred_equivI.
  Qed.
End later_mpred.
#[global] Hint Opaque later_mpred : typeclass_instances.
