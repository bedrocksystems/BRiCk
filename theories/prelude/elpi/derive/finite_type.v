(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import elpi.
From elpi.apps Require Import derive.

From bedrock.prelude.elpi Require Import prelude derive.plugins.

(***************************************************
 Finite Types
 - [[ #[only(finite_type)] derive VariantType ]]
   Assembles pieces from finite.v to expose `to_N` and `of_N` functions on `VariantType`, together with laws.
   The encoding into `N` is derived automatically from the order of constructors of `VariantType`.
 ***************************************************)
Elpi Db derive.finite_type.db lp:{{
  namespace derive.finite_type {
    pred mk-finite-prelim i:string, i:gref.
    mk-finite-prelim TypeName TyGR :- std.do! [
      #line 21 "derive.v"
      %TODO: I'd like to be able to do a transparent ascription here, but
      %it doesn't seem like coq-elpi supports this (the following gives opaque ascription):
      %coq.locate-module-type "simple_finite_bitmask_type_intf" MTP,
      coq.env.begin-module TypeName none,

      coq.env.add-const "t" (global TyGR) _ @transparent! C,
      Ty = global (const C),

      %TODO: these names are couplings, so centralize the calculation of instance names
      %across Deriving and here.
      EqdecName is TypeName ^ "_eq_dec",
      coq.locate EqdecName GrEqdec,
      std.assert-ok! (coq.elaborate-skeleton {{ EqDecision lp:{{ Ty }} }} _ ETyEqdec) "mk-finite-prelim: failed to check eq_dec",
      coq.env.add-const "t_eq_dec" (global GrEqdec) ETyEqdec @transparent! Ceq_dec,
      @global! => coq.TC.declare-instance (const Ceq_dec) 0,

      FinName is TypeName ^ "_finite",
      coq.locate FinName GrFin,
      std.assert-ok! (coq.elaborate-skeleton {{ Finite lp:{{ Ty }} }} _ ETyFin) "mk-finite-prelim: failed to check finite",
      coq.env.add-const "t_finite" (global GrFin) ETyFin @transparent! Cfin,
      @global! => coq.TC.declare-instance (const Cfin) 0,
    ].

    pred mk-simple-finite i:string, i:gref.
    mk-simple-finite TypeName TyGR :- std.do! [
      derive.if-verbose (coq.say "[derive.finite_type][mk-simple-finite]" TypeName),
      mk-finite-prelim TypeName TyGR,
      coq.env.include-module-type {coq.locate-module-type "finite_type_mixin"} coq.inline.default,
      coq.env.end-module MP_,
    ].

    pred mk-finite i:string, i:gref, i:term.
    mk-finite TypeName TyGR ToN :- std.do! [
      derive.if-verbose (coq.say "[derive.finite_type][mk-finite]" TypeName),
      mk-finite-prelim TypeName TyGR,

      coq.locate "t" GRTy,
      Ty is global GRTy,
      coq.env.add-const "to_N" ToN {{ lp:Ty -> N }} @transparent! CtoN_,

      coq.env.include-module-type {coq.locate-module-type "finite_encoded_type_mixin"} coq.inline.default,
      coq.env.end-module MP_,
    ].
  }
}}.

Elpi Accumulate derive lp:{{
  namespace derive.finite_type {
    pred to-N i:term, o:term.
    :name "to-N.fail"
    to-N T F :- std.do! [
      Lem = {{ @ToN lp:T lp:F }},
      derive.if-verbose (coq.say "[derive.finite_type][to-N]" Lem),
      std.assert-ok! (coq.typecheck {{ lp:Bo : lp:Lem }} _) "typechecking a [ToN] instance failed",
      coq.ltac.collect-goals Bo [SealedGoal] [],
      coq.ltac.open (coq.ltac.call "typeclasses_eauto" []) SealedGoal [],
      derive.if-verbose (coq.say "[derive.finite_type][to-N]" T Lem),
      %Memoize the result:
      coq.elpi.accumulate library "derive.finite_type.db" (clause _ (before "to-N.fail") (to-N T F)),
    ].
  }
}}.

(*We must export this tactic to [[ #[only(finite_type)] derive ]] use sites.*)
Ltac typeclasses_eauto := typeclasses eauto.

Elpi Accumulate derive Db derive.finite_type.db.
Elpi Accumulate derive lp:{{
  namespace derive.finite_type {
    pred main i:gref, i:string, o:list prop.
    main TyGR Prefix Clauses :- std.do! [
      remove-final-underscore Prefix Variant,
      if (derive.finite_type.to-N (global TyGR) ToN)
        (derive.finite_type.mk-finite Variant TyGR ToN)
        (derive.finite_type.mk-simple-finite Variant TyGR),
      Clauses = [finite-type-done TyGR],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.finbitset.db" (clause _ _ x)
      ),
    ].
    main _ _ _ :- usage.

    pred usage.
    usage :- coq.error "Usage: derive.finite_type TyGR Prefix Clauses".
  }

  dep1 "finite_type" "finite". %finite implies eq_dec
  derivation
    (indt T) Prefix
    (derive "finite_type"
      (derive.finite_type.main (indt T) Prefix)
      (finite_type-done (indt T))
    ).
}}.
Elpi Typecheck derive.
