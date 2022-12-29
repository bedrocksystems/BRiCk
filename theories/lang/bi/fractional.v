(*
 * Copyright (c) 2021-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export iris.bi.lib.fractional.

From bedrock.lang.bi Require Import prelude observe.

(** * Simple extensions to iris.bi.lib.fractional *)
(**
Overview:

- Tactic [solve_as_frac] for solving [AsFractional]

- [FractionalN], [AsFractionalN], [AgreeF1] notation to save typing

- Some properties of fractional predicates
*)

Ltac solve_as_frac := solve [intros; exact: Build_AsFractional].

(**
Do not extend this module. It exists for backwards compatibility.
*)
Module Export nary.
  (**
  [FractionalN] states that predicate [P] taking a fraction and then [N]
  arguments is [Fractional]
  *)
  Notation Fractional1 P := (∀ a, Fractional (fun q => P q a)).
  Notation Fractional2 P := (∀ a b, Fractional (fun q => P q a b)).
  Notation Fractional3 P := (∀ a b c, Fractional (fun q => P q a b c)).
  Notation Fractional4 P := (∀ a b c d, Fractional (fun q => P q a b c d)).
  Notation Fractional5 P := (∀ a b c d e, Fractional (fun q => P q a b c d e)).

  (** [AsFractionalN] informs the IPM about predicate [P] satisfying [FracitonalN P] *)
  Notation AsFractional0 P := (∀ q, AsFractional (P q) P q).
  Notation AsFractional1 P := (∀ q a, AsFractional (P q a) (fun q => P%I q a) q).
  Notation AsFractional2 P := (∀ q a b, AsFractional (P q a b) (fun q => P%I q a b) q).
  Notation AsFractional3 P := (∀ q a b c, AsFractional (P q a b c) (fun q => P%I q a b c) q).
  Notation AsFractional4 P := (∀ q a b c d, AsFractional (P q a b c d) (fun q => P%I q a b c d) q).
  Notation AsFractional5 P := (∀ q a b c d e, AsFractional (P q a b c d e) (fun q => P%I q a b c d e) q).

  (** [AgreeF1 P] states that [P q a] can only holds for one possible [a],
  regardless of the fraction [q]. *)
  Notation AgreeF1 P := (∀ (q1 q2 : Qp) a1 a2, Observe2 [| a1 = a2 |] (P q1 a1) (P q2 a2)).
End nary.

#[global] Instance fractional_exist {PROP : bi} {A} (P : A → Qp → PROP)
  (Hfrac : ∀ oa, Fractional (P oa))
  (Hobs : ∀ a1 a2 q1 q2, Observe2 [| a1 = a2 |] (P a1 q1) (P a2 q2)) :
  Fractional (λ q, ∃ a : A, P a q)%I.
Proof.
  intros q1 q2.
  rewrite -bi.exist_sep; last by intros; exact: observe_2_elim_pure.
  f_equiv=>oa. apply: fractional.
Qed.
