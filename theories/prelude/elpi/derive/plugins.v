(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import elpi.
From elpi.apps Require Import derive.

From stdpp Require Export finite.

From bedrock.prelude Require Export prelude.

Require Import bedrock.prelude.elpi.prelude.

Elpi Accumulate derive Db bedrock.prelude.db.

(****************************************
 stdpp plugins
 ****************************************)
(*For each supported deriviation, two predicates:
   - [myderiv TyGR DerivGR] Maps [TyGR] to its generated derivation
   - [myderiv-done TyGR] We're done deriving [myderiv] for [TyGR].*)
Elpi Db derive.stdpp.db lp:{{
  pred eqdec o:gref, o:gref.
  pred eqdec-done o:gref.

  pred inhabited o:gref, o:gref.
  pred inhabited-done o:gref.

  pred countable o:gref, o:gref.
  pred countable-done o:gref.

  pred finite o:gref, o:gref.
  pred finite-done o:gref.
}}.
Elpi Accumulate derive Db derive.stdpp.db.

(****************************************
 bedrock finset/bitset (finite.v) plugins
 ****************************************)
Elpi Db derive.finbitset.db lp:{{
  pred finset-done o:gref.
  pred bitset-done o:gref.
}}.
Elpi Accumulate derive Db derive.finbitset.db.
