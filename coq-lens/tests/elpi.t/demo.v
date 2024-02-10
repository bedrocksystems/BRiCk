(* TODO: copyright header. *)
(* From https://github.com/bedrocksystems/coq-lens/blob/master/test-suite/demo.v *)
Require Import Coq.Strings.String.
Require Import elpi.elpi.
Require Import elpi.apps.derive.
Require Import Lens.Lens.
Require Import Lens.Elpi.Elpi.

Import LensNotations.
#[local] Open Scope lens_scope.

#[projections(primitive=no)]
Record Oops : Set :=
{ oops1 : nat }.

#[only(lens)] derive Oops.

#[projections(primitive=yes)]
Record Foo : Set :=
{ foo : nat
; bar : bool }.


#[only(lens)] derive Foo.

About _foo.
About _bar.

Goal {| foo := 3 ; bar := true |} .^ _foo = 3.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} .^ _bar = true.
Proof. reflexivity. Qed.


Goal {| foo := 3 ; bar := true |} & _bar .= false = {| foo := 3 ; bar := false |}.
Proof. reflexivity. Qed.

Set Printing All.

(* Test for https://github.com/LPCIC/coq-elpi/pull/521 *)
Lemma prim_proj_fold_test r :
  foo r = 0 ->
  view _foo r = foo r.
Proof.
  simpl.
  intros Hpr.
  Show.
  rewrite Hpr.
  Show.
  reflexivity.
Qed.
