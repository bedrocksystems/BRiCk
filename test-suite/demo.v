Require Import Coq.Strings.String.
Require Import Lens.Lens.
Require Import Lens.TC.TC.

Record Oops : Set :=
{ oops1 : nat }.

Run TemplateProgram (genLens Oops).

Set Primitive Projections.

Record Foo : Set :=
{ foo : nat
; bar : bool }.


Run TemplateProgram (genLens Foo).

About _foo.
About _bar.

Goal view _foo {| foo := 3 ; bar := true |} = 3.
Proof. reflexivity. Qed.

Goal view _bar {| foo := 3 ; bar := true |} = true.
Proof. reflexivity. Qed.


Goal set _bar  false {| foo := 3 ; bar := true |} = {| foo := 3 ; bar := false |}.
Proof. reflexivity. Qed.
