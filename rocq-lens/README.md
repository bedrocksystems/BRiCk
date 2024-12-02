Lenses in Rocq (with Elpi Generation)
=====================================

Lenses provide a general and composable means of manipulating data, e.g., via
getters and setters. They are very popular in Haskell, see for example the
[lens](https://hackage.haskell.org/package/lens) package.

The rocq-lens-elpi package uses [coq-elpi](https://github.com/LPCIC/coq-elpi)
to generate lenses for records.

## Usage

```coq
Require Import elpi.apps.derive.derive.
Require Import Lens.Lens.
Require Import Lens.Elpi.Elpi. (* for Elpi lens generation *)

Import LensNotations.
#[local] Open Scope lens_scope.

Record Foo : Set := {
  foo : nat;
  bar : bool;
}.
#[only(lens)] derive Foo. (* requires rocq-lens-elpi *)

About _foo.
About _bar.

Goal {| foo := 3 ; bar := true |} .^ _foo = 3.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} .^ _bar = true.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} &: _bar .= false =
     {| foo := 3 ; bar := false |}.
Proof. reflexivity. Qed.
```

## Limitations

Currently, lenses do not support strong updates, and they are not universe
polymorphic. Enhancements on both of these fronts are welcome.

## Implementation Notes

This implementation is significantly more first-order than that of Haskell. We
prefer separate `get` and `set` functions, packaged as a record. This has the
following benefits in Coq:

1. We don't need to depend on a `Functor` class.
2. We don't require extra universes for the types of the universally
   quantified functor.
3. Error messages are simpler and type checking does not rely on typeclass
   inference which is not as robust as it is in Haskell due dependent types.
