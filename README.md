# coq-lens
An implementation of lenses in Coq. This package uses [meta-coq](https://github.com/MetaCoq/metacoq) to generate lenses for records.

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

### Implementation Note
Unlike the Haskell implementation, this implementation is significantly more first-order, prefering separate `get` and `set` functions packaged as a record. This has several benefits in Coq.

1. We don't need to depend on a `Functor` class.
2. We don't require extra universes for the types of the universally quantified functor.
3. Error messages are simpler and type checking does not rely on typeclass inference which is not as robust as it is in Haskell due to the dependent nature of Gallina.
