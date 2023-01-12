(*
 * Copyright (C) BedRock Systems Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bedrock.lang.cpp.bi.cfractional.

From bedrock.lang.bi Require Import prelude observe spec.exclusive.
Require Import iris.proofmode.proofmode.

#[local] Set Primitive Projections.
#[local] Set Printing Coercions.
#[local] Set Default Proof Using "Type*".

(** * Spec building block: const/mutable fractional ownership *)
(**
Overview:

- [CFracSplittable_N R]

- Tactic [solve_cfrac] for solving [CFracSplittable_N]

[CFracSplittable_N R], where [N] counts the number of arguments taken
by [R] after its const/mutable fraction, is short-hand for:

- [R] is _timeless_, meaning it represents ownership;

- [R] is _const/mutable fractional_, meaning it can be split and
combined using [andb] on booleans and addition on fractions; and

- the fraction in [R] is _valid_, meaning [≤ 1].
*)

Ltac solve_cfrac := solve [intros; split; apply _].

Class CFracSplittable_0 {PROP : bi} (R : cQp.t → PROP) : Prop := {
  cfrac_splittable_0_fractional :> CFractional R;
  cfrac_splittable_0_timeless :> Timeless1 R;
  cfrac_splittable_0_frac_valid :> CFracValid0 R;
}.
Section cfrac_0.
  Context {PROP : bi} (R : cQp.t → PROP) `{!CFracSplittable_0 R}.

  #[global] Instance cfrac_splittable_0_as_fractional : AsCFractional0 R.
  Proof. solve_as_cfrac. Qed.
  #[global] Instance cfrac_splittable_0_frac_valid_2 : CFrac2Valid0 R.
  Proof.
    intros. iIntros "R1 R2". iCombine "R1 R2" as "R".
    (**
    TODO (Revisit if clients see similar problems): The shorter proof
    [iApply observe with "R"] does not work because the goal [[|
    cQp.frac q1 + cQp.frac q2 ≤ 1 |]%Qp] does not match the observation
    [[| cQp.frac (q1 ⋅ q2) ≤ 1 |]%Qp] on the nose. Reconsider having
    [iCombine] introduce [op].
    *)
    iDestruct (observe [| _ ≤ 1 |]%Qp with "R") as %?. auto.
  Qed.
End cfrac_0.

Section cfrac_1_gen.
  Context {A} {PROP : bi} (R : cQp.t → A → PROP).
  Context {cfrac_splittable_1_frac_valid : CFracValid1 R}.
  Context {cfrac_splittable_1_as_fractional : AsCFractional1 R}.

  #[global] Instance cfrac_splittable_1_frac_valid_2 : AgreeCF1 R -> CFrac2Valid1 R.
  Proof.
    intros Ha *. iIntros "R1 R2".
    iDestruct (Ha with "R1 R2") as %->. iCombine "R1 R2" as "R".
    (** TODO: As above *)
    iDestruct (observe [| _ ≤ 1 |]%Qp with "R") as %?. auto.
  Qed.

  #[global] Instance cfrac_splittable_1_agreef_excl_gen c q v1 v2 `{!AgreeCF1 R} :
    Observe2 False (R (cQp.mk c 1) v1) (R q v2).
  Proof.
    iIntros "R1 R2".
    iDestruct (observe_2 [| _ ≤ 1 |]%Qp with "R1 R2") as %Hv.
    by apply Qp.not_add_le_l in Hv.
  Qed.

  #[global] Instance cfrac_splittable_1_agreef_excl c :
    AgreeCF1 R → Exclusive1 (R (cQp.mk c 1)) := _.
End cfrac_1_gen.

Class CFracSplittable_1 {A} {PROP : bi} (R : cQp.t → A → PROP) : Prop := {
  cfrac_splittable_1_fractional :> CFractional1 R;
  cfrac_splittable_1_timeless :> Timeless2 R;
  cfrac_splittable_1_frac_valid :> CFracValid1 R;
}.
Section cfrac_1.
  Context {A} {PROP : bi} (R : cQp.t → A → PROP) `{!CFracSplittable_1 R}.

  #[global] Instance cfrac_splittable_1_as_fractional : AsCFractional1 R.
  Proof. solve_as_cfrac. Qed.

  Goal AgreeCF1 R -> CFrac2Valid1 R.
  Proof. apply _. Abort.

  Goal ∀ c, AgreeCF1 R → Exclusive1 (R (cQp.mk c 1)).
  Proof. apply _. Abort.
End cfrac_1.

Class CFracSplittable_2 {A B} {PROP : bi} (R : cQp.t → A → B → PROP) : Prop := {
  cfrac_splittable_2_fractional :> CFractional2 R;
  cfrac_splittable_2_timeless :> Timeless3 R;
  cfrac_splittable_2_frac_valid :> CFracValid2 R;
}.
Section cfrac_2.
  Context {A B} {PROP : bi} (R : cQp.t → A → B → PROP) `{!CFracSplittable_2 R}.

  #[global] Instance cfrac_splittable_2_as_fractional : AsCFractional2 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_2.

Class CFracSplittable_3 {A B C} {PROP : bi}
    (R : cQp.t → A → B → C → PROP) : Prop := {
  cfrac_splittable_3_fractional :> CFractional3 R;
  cfrac_splittable_3_timeless :> Timeless4 R;
  cfrac_splittable_3_frac_valid :> CFracValid3 R;
}.
Section cfrac_3.
  Context {A B C} {PROP : bi} (R : cQp.t → A → B → C → PROP) `{!CFracSplittable_3 R}.

  #[global] Instance cfrac_splittable_3_as_fractional : AsCFractional3 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_3.

Class CFracSplittable_4 {A B C D} {PROP : bi}
    (R : cQp.t → A → B → C → D → PROP) : Prop := {
  cfrac_splittable_4_fractional :> CFractional4 R;
  cfrac_splittable_4_timeless :> Timeless5 R;
  cfrac_splittable_4_frac_valid :> CFracValid4 R;
}.
Section cfrac_4.
  Context {A B C D} {PROP : bi} (R : cQp.t → A → B → C → D → PROP).
  Context `{!CFracSplittable_4 R}.

  #[global] Instance cfrac_splittable_4_as_fractional : AsCFractional4 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_4.

Class CFracSplittable_5 {A B C D E} {PROP : bi}
    (R : cQp.t → A → B → C → D → E → PROP) : Prop := {
  cfrac_splittable_5_fractional :> CFractional5 R;
  cfrac_splittable_5_timeless :> Timeless6 R;
  cfrac_splittable_5_cfrac_valid :> CFracValid5 R;
}.
Section cfrac_5.
  Context {A B C D E} {PROP : bi} (R : cQp.t → A → B → C → D → E → PROP).
  Context `{!CFracSplittable_5 R}.

  #[global] Instance cfrac_splittable_5_as_fractional : AsCFractional5 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_5.
