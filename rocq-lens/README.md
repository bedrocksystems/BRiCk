Implementation of Lenses in Rocq/Coq Using Elpi
===============================================

This package uses [coq-elpi](https://github.com/LPCIC/coq-elpi) to generate
lenses for records.

## Usage

```coq
Require Import elpi.apps.derive.derive.
Require Import Lens.Lens.
Require Import Lens.Elpi.Elpi.

Import LensNotations.
#[local] Open Scope lens_scope.

#[projections(primitive=yes)]
Record Foo : Set := {
  foo : nat;
  bar : bool;
}.

#[only(lens)] derive Foo.

About _foo.
About _bar.

Goal {| foo := 3 ; bar := true |} .^ _foo = 3.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} .^ _bar = true.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} &: _bar .= false = {| foo := 3 ; bar := false |}.
Proof. reflexivity. Qed.
```

## Limitations

Generation of lenses currently only supports `Record`s defined with primitive
projections enabled. Further, it does not support:
- polymorphic lenses,
- universe polymorphic definitions,
- iniverse polymorphic lenses.

## Implementation Notes

This implementation is significantly more first-order than that of Haskell. We
prefer separate `get` and `set` functions, packaged as a record. This has the
following benefits in Coq:
1. We don't need to depend on a `Functor` class.
2. We don't require extra universes for the types of the universally
   quantified functor.
3. Error messages are simpler and type checking does not rely on typeclass
   inference which is not as robust as it is in Haskell due dependent types.
