# coq-lens
An implementation of lenses in Coq. This package uses [template-coq](https://github.com/template-coq/template-coq) to generate lenses for records.

## Use
See `demo.v` in the `test-suite` directory. A simple example is included below.

```coq
Set Primitive Projections.

Record Foo : Set :=
{ foo : nat
; bar : bool
}.
Run TemplateProgram (genLens Foo). (* generates _foo and _bar *)

About _foo. (* : Lens Foo Foo nat nat *)
About _bar. (* : Lens Foo Foo bool bool *)

Goal view _foo {| foo := 3 ; bar := true |} = 3.
Proof. reflexivity. Qed.

Goal view _bar {| foo := 3 ; bar := true |} = true.
Proof. reflexivity. Qed.

Goal set _bar false {| foo := 3 ; bar := true |} = {| foo := 3 ; bar := false |}.
Proof. reflexivity. Qed.
```

## Limitations
Generation of lenses via template-coq is currently only supports `Record`s defined with `Primitive Projections` enabled. Further, it does not support:

- Polymorphic lenses
- Universe polymorphic definitions
- Universe polymorphic lenses
