(* TODO: copyright header. *)
(* From https://github.com/bedrocksystems/coq-lens/blob/master/test-suite/demo.v *)
Require Import Coq.Strings.String.
From elpi Require Import elpi.
From elpi.apps Require Import derive.
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
