(*
 * Copyright (C) BedRock Systems Inc. 2020-2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bedrock.lang.bi.prelude.

From bedrock.lang.bi Require Import observe spec.knowledge.
Import ChargeNotation.

#[local] Set Primitive Projections.

(** * Spec building block: logical constants *)
(**
The judgment [Constant I P] means "under invariant [I], [P] is a
logical constant"; specifically, there exists a unique [x : A] such
that [P x], where [P x] itself is timeless, affine, and persistent.

Warning: [Constant] should be avoided when simpler things work. It
exists to track values that arise _dynamically_.
*)

Class Constant {A} {PROP : bi} (I : PROP) (P : A → PROP) : Prop := {
  constant_inv_knowledge :> Knowledge I;
  constant_exist :> Observe (Exists x, P x) I;

  constant_unique    x y :> Observe2 [| x = y |] (P x) (P y);
  constant_knowledge x :> Knowledge (P x);
  constant_timeless  x :> Timeless (P x);
}.
Arguments constant_exist {_ _} (_ _)%I {_} : assert.
Arguments constant_unique {_ _} (_ _)%I {_} _ _ : assert.
