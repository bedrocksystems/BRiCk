(*
 * Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE file in the repository root for details.
 *)

(** * iProp satisfies Ghostly and HasUsualOwn

iProp instances of the PROP constraint bundles defined in
lang/bi/prop_constraints.v

This is only needed as we instantiate general [bedrock.lang.bi.own] with [iProp].
*)

Require Import bedrock.lang.bi.prop_constraints.
Require Export bedrock.lang.base_logic.iprop_own.

#[global] Instance iprop_ghostly {Σ : gFunctors} : Ghostly (iPropI Σ) :=
  {| ghostly_bibupd := _
   ; ghostly_embed := _ |}.

#[global] Instance iprop_has_usual_own `{Σ : gFunctors, T : cmra, !inG Σ T }
  : HasUsualOwn (iPropI Σ) T :=
  {| has_usual_own_own := _
   ; has_usual_own_upd := _
   ; has_usual_own_valid := _ |}.
