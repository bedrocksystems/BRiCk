Require Import Coq.Strings.String.
Require Import Lens.Lens.
Require Import Lens.TC.TC.

Import LensNotations.
#[local] Open Scope lens_scope.

#[projections(primitive=no)]
Record Oops : Set :=
{ oops1 : nat }.

Fail MetaCoq Run (genLens Oops).

#[projections(primitive=yes)]
Record Foo : Set :=
{ foo : nat
; bar : bool }.


MetaCoq Run (genLens Foo).

About _foo.
About _bar.

Goal {| foo := 3 ; bar := true |} .^ _foo = 3.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} .^ _bar = true.
Proof. reflexivity. Qed.


Goal {| foo := 3 ; bar := true |} & _bar .= false = {| foo := 3 ; bar := false |}.
Proof. reflexivity. Qed.
