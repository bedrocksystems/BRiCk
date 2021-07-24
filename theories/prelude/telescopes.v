(*
 * Copyright (C) BedRock Systems Inc. 2020-21
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Export stdpp.telescopes.
Require Export bedrock.prelude.base.

#[local] Set Universe Polymorphism.

Fixpoint tele_append (t : tele) {struct t}: (t -t> tele) -> tele :=
  match t as t return (t -t> tele) -> tele with
  | TeleO => fun x : tele => x
  | @TeleS T f => fun x => @TeleS T (fun t => tele_append (f t) (x t))
  end.

Definition tele_fun_pointwise@{X Z Y} {t : tele@{X}} {A : Type@{Z}}
    (R : A -> A -> Prop) (f g : tele_fun@{X Z Y} t A) : Prop :=
  forall x, R (tele_app f x) (tele_app g x).
