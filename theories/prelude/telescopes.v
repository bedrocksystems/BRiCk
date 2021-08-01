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

(** [tforallT F] is just like [tforall F] except that [F] returns
    a [Type] rather than a [Prop].

    To apply this, use [tapplyT].
 *)
Fixpoint tforallT {TT : tele} : (TT -> Type) -> Type :=
  match TT as TT return (TT -> Type) -> Type with
  | TeleO => fun F => F TargO
  | TeleS f => fun F => forall x, tforallT (fun arg => F (TargS x arg))
  end.

Definition targ_0 {T F} (t : tele_arg (@TeleS T F)) : T :=
  match t in tele_arg X return match X with
                               | TeleO => unit
                               | @TeleS x f => x
                               end
  with
  | TargO => tt
  | TargS x _ => x
  end.

(** [tapplyT F args] applys [F] to [args] *)
Fixpoint tapplyT {TT : tele} f (ff : @tforallT TT f) (x: TT) {struct x} : f x :=
  match x as x in tele_arg X
        return forall f : X -> Type, tforallT f -> f x
  with
  | TargO => fun _ F => F
  | TargS y t => fun _ F => tapplyT (fun x => _ (TargS y x)) (F y) t
  end f ff.
