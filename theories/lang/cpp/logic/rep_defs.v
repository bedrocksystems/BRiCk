(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.bi Require Export monpred.

Require Import bedrock.prelude.base.

From bedrock.lang.cpp Require Import semantics.values logic.mpred.
From bedrock.lang.bi Require Import prelude.

Import ChargeNotation.
Implicit Types (σ resolve : genv) (p : ptr) (o : offset).

(** representations are predicates over a location, they should be used to
  * assert properties of the heap
  *)
Canonical Structure ptr_bi_index : biIndex :=
  BiIndex ptr _ eq _.

#[global] Instance ptr_bi_index_discrete : BiIndexDiscrete ptr_bi_index.
Proof. by move=>i i'. Qed.

(** The tactic [intros ->%ptr_rel_elim] is much faster than [intros
    ->] when introducing [p1 ⊑ p2] (when the latter works at all). *)
Lemma ptr_rel_elim (p1 p2 : ptr) : p1 ⊑ p2 → p1 = p2.
Proof. done. Qed.

Canonical Structure RepI `{Σ : cpp_logic} := monPredI ptr_bi_index mpredI.
Definition Rep `{Σ : cpp_logic} : Type := RepI.
Definition RepO `{Σ : cpp_logic} : ofe := RepI.

#[global] Bind Scope bi_scope with Rep.

Section defs.
  Context `{Σ : cpp_logic}.

  Definition as_Rep (P : ptr -> mpred) : Rep := MonPred P _.

  (** [_at base R] states that [R base] holds.

      NOTE This is "weakly at"
   *)
  Definition _at_def (base : ptr) (R : Rep) : mpred :=
    R.(monPred_at) base.
  Definition _at_aux : seal (@_at_def). Proof. by eexists. Qed.
  Definition _at := _at_aux.(unseal).
  Definition _at_eq : @_at = _ := _at_aux.(seal_eq).

  Definition _offsetR_def (o : offset) (r : Rep) : Rep :=
    as_Rep (fun base => r.(monPred_at) (base ,, o)).
  Definition _offsetR_aux : seal (@_offsetR_def). Proof. by eexists. Qed.
  Definition _offsetR := _offsetR_aux.(unseal).
  Definition _offsetR_eq : @_offsetR = _ := _offsetR_aux.(seal_eq).

  (** Values
   * These `Rep` predicates wrap `ptsto` facts
   *)
  (* todo(gmm): make opaque *)
  Definition pureR (P : mpred) : Rep :=
    as_Rep (fun _ => P).
End defs.

#[global] Instance: Params (@_at) 3 := {}.
#[global] Instance: Params (@as_Rep) 2 := {}.
#[global] Instance: Params (@_offsetR) 3 := {}.
#[global] Instance: Params (@pureR) 2 := {}.
