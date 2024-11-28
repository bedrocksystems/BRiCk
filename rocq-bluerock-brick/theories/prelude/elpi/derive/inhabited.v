(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.base.

Require Import elpi.elpi.
Require Export bedrock.prelude.elpi.derive.common.

Require Export bedrock.prelude.elpi.basis.
Elpi Accumulate derive Db bedrock.basis.db.

Elpi Db derive.stdpp.inhabited.db lp:{{
  pred inhabited o:gref, o:gref.
  pred inhabited-done o:gref.
  :name "inhabited-done.typeclass"
  inhabited-done GR :-
    typeclass "derive.stdpp.inhabited.db"
      (before "inhabited-done.typeclass") (inhabited-done GR) {{ @Inhabited lp:{{global GR}} }} Bo_.
}}.
Elpi Accumulate derive Db derive.stdpp.inhabited.db.
Elpi Typecheck derive.

(***************************************************
 Inhabited
 ***************************************************)

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "inhabited" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  namespace derive.inhabited {
    pred main i:gref, i:string, o:list prop.
    main TyGR Prefix Clauses :- std.do! [
      InstanceName is Prefix ^ "inhabited",
      derive-original-gref TyGR OrigGR,
      TyInhabited = {{ Inhabited lp:{{global OrigGR}} }},
      std.assert-ok! (coq.elaborate-skeleton TyInhabited _ ETyInhabited) "[derive.inh.main] [TyInhabited]",
      std.assert-ok! (coq.typecheck {{ lp:BoInhabited : lp:ETyInhabited }} _) "typechecking the [Inhabited t] instance failed",
      coq.ltac.collect-goals BoInhabited [SealedGoal] [],
      coq.ltac.open (coq.ltac.call "solve_inhabited" []) SealedGoal [],
      @using! "Type" => coq.env.add-const InstanceName BoInhabited ETyInhabited @opaque! C,
      @global! => coq.TC.declare-instance (const C) 0,
      Clauses = [inhabited-done OrigGR, inhabited OrigGR (const C)],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.stdpp.inhabited.db" (clause _ _ x)
      ),
    ].
    main _ _ _ :- usage.

    pred usage.
    usage :- coq.error
"Usage: #[only(inhabited)] derive T
where T is an inductive or a definition that unfolds to an inductive.

Example #1:
 Variant T := A | B | C.
 #[only(inhabited)] derive T

Example #2:
  #[only(inhabited)] derive
  Variant T := A | B | C.

Example #3:
  Variant _T := A | B | C.
  Definition T := _T.
  #[only(inhabited)] derive T.".

  }

  derivation
    (indt T) Prefix ff
    (derive "inhabited"
       (derive.inhabited.main (indt T) Prefix)
       (inhabited-done (indt T))
    ).
}}.
Elpi Typecheck derive.
