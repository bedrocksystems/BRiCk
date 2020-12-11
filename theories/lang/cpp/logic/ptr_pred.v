(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.proofmode Require Import tactics.
From bedrock.lang.prelude Require Import base addr.
From bedrock.lang.bi Require Import prelude observe.
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp Require Import pred.

(* Experimental APIs for observation from pointer predicates, to allow you to
write a bunch of observations at once.
*)

(* Only import when defining representation predicates and associated instances. *)
Module ptr_pred_helpers.
  (* Fail #[export] Existing Instances observe_strict_valid_valid. *)
  #[export] Hint Resolve
    observe_strict_valid_valid
    observe_type_ptr_strict_valid
    observe_type_ptr_valid_plus_one : typeclass_instances.
End ptr_pred_helpers.

(* Alternative setup. *)
Module ptr_pred_observe.
  (* XXX instances of these classes are easier to declare with less overhead, but the classes
  themselves cause some backtracking. *)
  Class ObserveStrictValid `{Σ : cpp_logic} P p := {
    obs_strict_valid :> Observe (strict_valid_ptr p) P;
    obs_rel_valid :> Observe (valid_ptr p) P
  }.
  Hint Mode ObserveStrictValid ! ! ! - : typeclass_instances.

  Class ObserveTypePtr `{Σ : cpp_logic} P p (σ : genv) ty := {
    obs_type_ptr :> Observe (type_ptr ty p) P;
    obs_type_ptr_valid_plus_one :> Observe (valid_ptr (p .., o_sub σ ty 1)) P;
    obs_type_ptr_strict_valid :> ObserveStrictValid P p;
  }.
  Hint Mode ObserveTypePtr ! ! ! - - - : typeclass_instances.

  Section with_cpp.
    Context `{Σ : cpp_logic} (σ : genv).

    Lemma observe_strict_valid_intro
      `(Hobs : !Observe (strict_valid_ptr p) P) :
      ObserveStrictValid P p.
    Proof. split => //. exact /observe_strict_valid_valid. Qed.

    Lemma observe_type_ptr_intro
      `(Hobs : !Observe (type_ptr ty p) P) :
      ObserveTypePtr P p σ ty.
    Proof.
      split => //.
      exact /observe_type_ptr_valid_plus_one.
      apply /observe_strict_valid_intro /observe_type_ptr_strict_valid.
    Qed.

    Local Instance tptsto_observe_type_ptr ty q p v :
      ObserveTypePtr (tptsto ty q p v) p σ ty.
    Proof. apply /observe_type_ptr_intro /tptsto_type_ptr. Qed.

    Local Instance tptsto_strict_valid_ptr ty q p v :
      Observe (strict_valid_ptr p) (tptsto ty q p v) := _.
    Local Instance tptsto_valid_ptr : forall ty q p v,
      Observe (valid_ptr p) (tptsto ty q p v) := _.
    Local Instance tptsto_valid_ptr_plus_one : forall ty q p v,
      Observe (valid_ptr (p .., o_sub σ ty 1)) (tptsto ty q p v) := _.
  End with_cpp.

  #[export] Hint Resolve tptsto_observe_type_ptr : typeclass_instances.
End ptr_pred_observe.
