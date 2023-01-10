(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import elpi.
From elpi.apps Require Import derive.

From stdpp Require Export finite.

From bedrock.prelude Require Export prelude.

Require Import bedrock.prelude.elpi.basis.

Elpi Accumulate derive Db bedrock.basis.db.

(*We must export this tactic to [[ #[only(finite_type)] derive ]] use sites.*)
Ltac try_typeclasses_eauto := try typeclasses eauto.

(****************************************
 stdpp plugins
 ****************************************)
(*For each supported derivation, two predicates:
   - [myderiv TyGR DerivGR] Maps [TyGR] to its generated derivation
   - [myderiv-done TyGR] We're done deriving [myderiv] for [TyGR].*)
Elpi Db derive.stdpp.db lp:{{
  pred typeclass i:grafting, i:prop, i:term, o:term.
  typeclass Grafting Done T Bo :- std.do! [
    std.assert-ok! (coq.typecheck {{ lp:Bo : lp:T }} _) "[typeclass] typechecking an instance failed",
    coq.ltac.collect-goals Bo [SealedGoal] [],
    coq.ltac.open (coq.ltac.call "try_typeclasses_eauto" []) SealedGoal [],
    derive.if-verbose (coq.say "[typeclass] Instance:" Grafting T Bo),
    coq.elpi.accumulate library "derive.stdpp.db" (clause _ Grafting Done),
  ].

  pred eqdec o:gref, o:gref.
  pred eqdec-done o:gref.
  :name "eqdec-done.typeclass"
  eqdec-done GR :- typeclass (before "eqdec-done.typeclass") (eqdec-done GR) {{ @EqDecision lp:{{global GR}} }} Bo_.

  pred inhabited o:gref, o:gref.
  pred inhabited-done o:gref.
  :name "inhabited-done.typeclass"
  inhabited-done GR :- typeclass (before "inhabited-done.typeclass") (inhabited-done GR) {{ @Inhabited lp:{{global GR}} }} Bo_.

  pred countable o:gref, o:gref.
  pred countable-done o:gref.
  :name "coutable-done.typeclass"
  countable-done GR :- typeclass (before "countable-done.typeclass") (countable-done GR) {{ @Countable lp:{{global GR}} _ }} Bo_.

  pred finite o:gref, o:gref.
  pred finite-done o:gref.
  :name "finite-done.typeclass"
  finite-done GR :- typeclass (before "finite-done.typeclass") (finite-done GR) {{ @Finite lp:{{global GR}} _ }} Bo_.
}}.
Elpi Typecheck derive.

Elpi Accumulate derive Db derive.stdpp.db.
Elpi Typecheck derive.

(****************************************
 bedrock finite type/bitset (finite.v) plugins
 ****************************************)
 (** Configuration classes: *)
 (** finite type *)
Class ToN (T : Type) (to_N : T -> N) : Type := {}.
#[global] Hint Mode ToN + - : typeclass_instances.
(** bitset *)
Class ToBit (T : Type) (to_bit : T -> N) : Type := {}.
#[global] Hint Mode ToBit + - : typeclass_instances.

Elpi Db derive.finbitset.db lp:{{
  pred finite-type-done o:gref.
  pred bitset-done o:gref.
}}.
Elpi Accumulate derive Db derive.finbitset.db.
