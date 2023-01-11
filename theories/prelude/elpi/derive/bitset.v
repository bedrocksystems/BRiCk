(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import elpi.
From elpi.apps Require Import derive.

From bedrock.prelude Require Import prelude.
From bedrock.prelude.elpi Require Import basis derive.finite_type.

(***************************************************
 Bitsets
 - [[ #[only(bitset)] derive VariantType ]]
   Assembles pieces from finite.v to expose `to_bits`, together with laws, on [gset VariantType].
   The encoding into bit indices is derived automatically from the order of constructors of `VariantType`
   (0 for the first constructor, 1 for the second, etc.).
   Add an instance of `ToBit` to override the default behavior.
 ***************************************************)
Class ToBit (T : Type) (to_bit : T -> N) : Type := {}.
#[global] Hint Mode ToBit + - : typeclass_instances.

Elpi Db derive.bitset.db lp:{{
  pred finite-type-done o:gref.
  pred bitset-done o:gref.

  namespace derive.bitset {
    pred mk-simple-bitset i:string, i:gref.
    mk-simple-bitset TypeName TyGR :- std.do! [
      derive.if-verbose (coq.say "[derive.bitset][mk-simple-bitset]" TypeName),
      derive.finite_type.mk-finite-prelim TypeName TyGR,
      coq.env.include-module-type {coq.locate-module-type "simple_finite_bitmask_type_mixin"} coq.inline.default,
      coq.env.end-module MP,

      %TODO: at this point, remove the `TypeName_finite` instance, etc.
      %But coq-elpi doesn't seem to have an API for Remove Hints
      %(cf. https://bedrocksystems.atlassian.net/browse/FM-3019).

      %Module TypeName_set := simple_finite_bits TypeName.
      ModName is TypeName ^ "_set",
      coq.env.apply-module-functor ModName none {coq.locate-module "simple_finite_bits"} [MP] coq.inline.default _,
    ].

    pred mk-bitset i:string, i:gref, i:term.
    mk-bitset TypeName TyGR ToBit :- std.do! [
      derive.if-verbose (coq.say "[derive.bitset][mk-bitset]" TypeName),
      derive.finite_type.mk-finite-prelim TypeName TyGR,

      coq.locate "t" GRTy,
      Ty is global GRTy,
      coq.env.add-const "to_bit" ToBit {{ lp:Ty -> N }} @transparent! CToBit_,

      coq.env.include-module-type {coq.locate-module-type "finite_bitmask_type_mixin"} coq.inline.default,
      coq.env.end-module MP,

      ModName is TypeName ^ "_set",
      coq.env.apply-module-functor ModName none {coq.locate-module "finite_bits"} [MP] coq.inline.default _,
    ].
  }
}}.

Elpi Accumulate derive Db derive.finite_type.db.
Elpi Accumulate derive lp:{{
  namespace derive.bitset {
    pred to-bits i:term, o:term.
    :name "to-bits.typeclass"
    to-bits T F :- typeclass "derive.bitset.db"  (before "to-bits.typeclass") (to-bits T F) {{ @ToBit lp:T lp:F }} Bo_.
  }
}}.

Elpi Accumulate derive Db derive.bitset.db.
Elpi Accumulate derive lp:{{
  namespace derive.finset {
    pred main i:gref, i:string, o:list prop.
    main TyGR Prefix Clauses :- std.do! [
      remove-final-underscore Prefix Variant,
      if (derive.bitset.to-bits (global TyGR) ToBit)
        (derive.bitset.mk-bitset Variant TyGR ToBit)
        (derive.bitset.mk-simple-bitset Variant TyGR),
      Clauses = [bitset-done TyGR],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.bitset.db" (clause _ _ x)
      ),
    ].
    main _ _ _ :- usage.

    pred usage.
    usage :- coq.error "Usage: derive.bitset TyGR Prefix Clauses".
  }

  dep1 "bitset" "finite". %finite implies eq_dec
  derivation
    (indt T) Prefix
    (derive "bitset"
      (derive.finset.main (indt T) Prefix)
      (bitset-done (indt T))
    ).
}}.
Elpi Typecheck derive.
