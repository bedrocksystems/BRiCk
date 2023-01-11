(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From stdpp Require Import decidable.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

From bedrock.prelude.elpi Require Import basis.

(***************************************************
 EqDecision
 ***************************************************)
(*For each supported derivation, two predicates:
   - [myderiv TyGR DerivGR] Maps [TyGR] to its generated derivation
   - [myderiv-done TyGR] We're done deriving [myderiv] for [TyGR].*)
Elpi Db derive.stdpp.eq_dec.db lp:{{
  pred eqdec o:gref, o:gref.
  pred eqdec-done o:gref.
  :name "eqdec-done.typeclass"
  eqdec-done GR :-
    typeclass "derive.stdpp.eq_dec.db" (before "eqdec-done.typeclass") (eqdec-done GR) {{ @EqDecision lp:{{global GR}} }} Bo_.
}}.
Elpi Accumulate derive Db derive.stdpp.eq_dec.db.
Elpi Typecheck derive.

Elpi Accumulate derive lp:{{
  /* [derive.eqdec.main TyGR Prefix Clauses] creates a global instance
   * of type [EqDecision lp:{{global TyGR}}].
   * It works with any type supported by [solve_decision].
   *
   * Example of the generated Coq code:
   * | (* Inductive C : Set := FOO | BAR | BAZ. *)
   * | #[global] Instance C_eq_dec : EqDecision C. Proof. ... Defined.
   */
  namespace derive.eqdec {
    pred main i:gref, i:string, o:list prop.
    main TyGR Prefix Clauses :- std.do! [
      remove-final-underscore Prefix Prefix',
      InstanceName is Prefix' ^ "_eq_dec",
      TyEqDecision = {{ EqDecision lp:{{global TyGR}} }},
      std.assert-ok! (coq.elaborate-skeleton TyEqDecision _ ETyEqDecision) "[derive.eqdec] [TyEqDecision]",
      std.assert-ok! (coq.typecheck {{ lp:BoEqDecision : lp:ETyEqDecision }} _) "typechecking the [EqDecision t] instance failed",
      coq.ltac.collect-goals BoEqDecision [SealedGoal] [],
      coq.ltac.open (coq.ltac.call "solve_decision" []) SealedGoal [],
      coq.env.add-const InstanceName BoEqDecision ETyEqDecision @transparent! C,
      @global! => coq.TC.declare-instance (const C) 0,
      Clauses = [eqdec-done TyGR, eqdec TyGR (const C)],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.stdpp.eq_dec.db" (clause _ _ x)
      ),
    ].
    main _ _ _ :- usage.

    pred usage.
    usage :- coq.error "Usage: derive.eqdec TyGR Prefix Clauses".
  }

  derivation
    (indt T) Prefix                         % inputs
    (derive "eq_dec"                        % name (for dep1)
       (derive.eqdec.main (indt T) Prefix)  % code to run
       (eqdec-done (indt T))                % idempotency test
    ).
}}.
Elpi Typecheck derive.
