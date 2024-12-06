(*
 * Copyright (C) BlueRock Security Inc. 2021
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE file in the repository root for details.
 *)

(** * Mpred satisfies Ghostly and HasUsualOwn

Mpred instances of the PROP constraint bundles defined in
lang/bi/prop_constraints.v

*)

Require Import bedrock.lang.base_logic.own_instances.
Require Import bedrock.lang.bi.prop_constraints.
Require Import bedrock.lang.cpp.logic.pred.

#[global] Instance mpred_ghostly `{ cpp_logic } : Ghostly mpredI :=
  {| ghostly_bibupd := _
   ; ghostly_embed := _ |}.

#[global] Instance mpred_has_usual_own `{ !cpp_logic ti Σ, T : cmra, hasG : !inG Σ T }
  : HasUsualOwn mpredI T :=
  {| has_usual_own_own := _
   ; has_usual_own_upd := _
   ; has_usual_own_valid := _ |}.
