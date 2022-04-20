(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
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
Definition tforallT {TT : tele} (Ψ : TT → Type) : Type :=
  tele_fold (λ (T : Type) (b : T → Type), ∀ x : T, b x) (λ x, x) (tele_bind Ψ).

(** [tapplyT F args] applys [F] to [args] *)
Fixpoint tapplyT {TT : tele} (f : TT -> Type) (ff : @tforallT TT f) (x: TT) {struct TT} : f x.
Proof.
  destruct TT.
  - destruct x. apply ff.
  - destruct x as [y t].
    refine (tapplyT _ (fun x => _ (TargS y x)) (ff y) t).
Defined.
