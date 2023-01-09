(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import elpi.
From elpi.apps Require Import derive.

From bedrock.prelude.elpi Require Import basis derive.plugins.

(***************************************************
 Inhabited
 ***************************************************)
Elpi Accumulate derive lp:{{
  namespace derive.inhabited {
    pred main i:gref, i:string, o:list prop.
    main TyGR Prefix Clauses :- std.do! [
      remove-final-underscore Prefix Prefix',
      InstanceName is Prefix' ^ "_inhabited",
      TyInhabited = {{ Inhabited lp:{{global TyGR}} }},
      std.assert-ok! (coq.elaborate-skeleton TyInhabited _ ETyInhabited) "[derive.inh.main] [TyInhabited]",
      std.assert-ok! (coq.typecheck {{ lp:BoInhabited : lp:ETyInhabited }} _) "typechecking the [Inhabited t] instance failed",
      coq.ltac.collect-goals BoInhabited [SealedGoal] [],
      coq.ltac.open (coq.ltac.call "solve_inhabited" []) SealedGoal [],
      @using! "Type" => coq.env.add-const InstanceName BoInhabited ETyInhabited @opaque! C,
      @global! => coq.TC.declare-instance (const C) 0,
      Clauses = [inhabited-done TyGR, inhabited TyGR (const C)],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.stdpp.db" (clause _ _ x)
      ),
    ].
    main _ _ _ :- usage.

    pred usage.
    usage :- coq.error "Usage: derive.inhabited TyGR Prefix Clauses".
  }

  derivation
    (indt T) Prefix
    (derive "inhabited"
       (derive.inhabited.main (indt T) Prefix)
       (inhabited-done (indt T))
    ).
}}.
Elpi Typecheck derive.
