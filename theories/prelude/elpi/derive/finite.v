(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import elpi.
From elpi.apps Require Import derive.

From bedrock.prelude.elpi Require Import prelude derive.stdpp.

(***************************************************
 Finite
 ***************************************************)
Elpi Db derive.finite.db lp:{{
  namespace derive.finite {
     /* We want to process
      * [Variant ResType : Set := A | B | C (_ : option bool) | D (_ : bool) (_ : bool).]
      * into [A :: B :: (C <$> enum (option bool)) ++ (D <$> enum bool <*> enum bool).]
      */
      /*
      * [mk-finite-constructor.aux Constructor ConstrType InputList ResType OutputTerm]
      * will return  in [OutputTerm] the list
      * [(Constructor <$> enum _ <*> enum _) ++ InputList], passing as many
      * arguments to [Constructor] as needed.
      *
      * - [Constructor] must have type [ConstrType] = [A1 -> A2 -> ... -> An
      *   -> ResType] (where [n] can be 0).
      * [A1 ... An] are [Finite].
      * - [InputList] must have type [list ResType].
      */
      pred mk-finite-constructor.aux i:term, i:term, i:term, i:term, o:term.
      mk-finite-constructor.aux C {{ lp:{{ArgTy}} -> lp:{{ResType}} }} IL Ty OTm :- std.do! [
        std.assert-ok! (coq.elaborate-skeleton {{ lp:{{C}} <$> enum lp:{{ArgTy}} }} _ EC) "",
        mk-finite-constructor.aux EC {{ list lp:{{ResType}} }} IL Ty OTm
      ].

      mk-finite-constructor.aux C {{ list (lp:{{ArgTy}} -> lp:{{ResType}}) }} IL Ty OTm :- std.do! [
        std.assert-ok! (coq.elaborate-skeleton {{ lp:{{C}} <*> (enum lp:{{ArgTy}}) }} _ EC) "",
        mk-finite-constructor.aux EC {{list lp:{{ResType}} }} IL Ty OTm
      ].
      % Use "foo" instead of "foo ++ nil"
      mk-finite-constructor.aux C {{ list lp:{{ResTy}} }} {{ [] }} ResTy' C :-
        std.assert-ok! (coq.unify-leq ResTy ResTy') "".
      mk-finite-constructor.aux C {{ list lp:{{ResTy}} }} IL ResTy' {{ lp:{{C}} ++ lp:{{IL}} }} :-
        std.assert-ok! (coq.unify-leq ResTy ResTy') "".
      mk-finite-constructor.aux C ResTy IL ResTy' {{ lp:{{C}} :: lp:{{IL}} }} :-
        std.assert-ok! (coq.unify-leq ResTy ResTy') "".
      mk-finite-constructor.aux C ResTy IL ResTy' _foo :-
        coq.error "mk-finite-constructor.aux failed on C = " C ", ResTy =" ResTy ", IL =" IL ", ResTy' = " ResTy'.

      pred mk-finite-constructor i:term, i:term, i:term, o:term.
      mk-finite-constructor Ctor InputList ResType OutTm :- std.do! [
        std.assert-ok! (coq.elaborate-skeleton Ctor OTy ECtor) "[mk-finite-constructor] failed to elaborate ctor",
        mk-finite-constructor.aux ECtor OTy InputList ResType OutTm
      ].

      pred mk-finite-constructors i:list term, i: term, o:term.
      mk-finite-constructors L T EL :- std.do! [
        mk-finite-constructors.aux L T L',
        std.assert-ok! (coq.elaborate-skeleton L' {{list lp:{{T}}}} EL) "[mk-finite-constructors] failed to typecheck",
      ].

      pred mk-finite-constructors.aux i:list term, i:term, o:term.
      mk-finite-constructors.aux [] _ {{ nil }}.
      mk-finite-constructors.aux (Ctor :: RestCtors) T CtorsValues :- std.do! [
        mk-finite-constructors.aux RestCtors T RestValues,
        mk-finite-constructor Ctor RestValues T CtorsValues
      ].

      pred mk-finite i:string, i:list term, i:gref, o:constant.
      mk-finite InstanceName Ctors VariantGR C :- std.do![
        VariantTy = global VariantGR,
        derive.finite.mk-finite-constructors Ctors VariantTy CtorList,
        std.assert-ok! (coq.elaborate-skeleton CtorList _ ECtorList) "[mk-finite] failed to elaborate ctors",

        % The Finite instance must be transparent, but proof obligations must be Qed-opaque.
        % Since `abstract` is not supported (https://github.com/LPCIC/coq-elpi/issues/376),
        % we create separate goals by hand.

        std.assert-ok! (coq.elaborate-skeleton {{ NoDup lp:{{ECtorList}} }} _ ETyNoDup) "[mk-finite] [TyNoDup]",
        std.assert-ok! (coq.typecheck {{ lp:{{BoNoDup}} : lp:{{ETyNoDup}} }} _) "typechecking [NoDup] failed",
        coq.ltac.collect-goals BoNoDup [SealedGoalNoDup] [],
        % TODO AUTO (FM-2732) : Elpi disables vm_compute here
        coq.ltac.open (coq.ltac.call "solve_finite_nodup" []) SealedGoalNoDup [],
        @using! "Type" =>
        coq.env.add-const {calc (InstanceName ^ "_subproof_nodup")} BoNoDup ETyNoDup @opaque! CNoDup,

        std.assert-ok! (coq.elaborate-skeleton {{ ∀ x : lp:{{VariantTy}}, x ∈ lp:{{ECtorList}} }} _ ETyElemOf) "[mk-finite] [TyElemOf]",
        std.assert-ok! (coq.typecheck {{ lp:{{BoElemOf}} : lp:{{ETyElemOf}} }} _) "typechecking [ElemOf] failed",
        coq.ltac.collect-goals BoElemOf [SealedGoalElemOf] [],
        % TODO AUTO (FM-2732) : Elpi disables vm_compute here
        coq.ltac.open (coq.ltac.call "solve_finite_total" []) SealedGoalElemOf [],
        @using! "Type" =>
        coq.env.add-const {calc (InstanceName ^ "_subproof_elem_of")} BoElemOf ETyElemOf @opaque! CElemOf,

        std.assert-ok! (coq.elaborate-skeleton {{ Finite lp:{{VariantTy}} }} _ ETyFinite) "[mk-finite] [TyFinite]",
        std.assert-ok! (coq.elaborate-skeleton
        {{ @Build_Finite _ _ lp:{{ECtorList}}
            lp:{{ global (const CNoDup) }} lp:{{ global (const CElemOf) }}}}
        _ EFiniteBody) "[mk-finite] [TyFinite]",

        coq.env.add-const InstanceName EFiniteBody
        ETyFinite @transparent! C,
        @global! => coq.TC.declare-instance (const C) 0
      ].
  }
}}.

Elpi Accumulate derive Db derive.finite.db.
Elpi Accumulate derive lp:{{
  namespace derive.finite {
    pred main i:gref, i:string, o:list prop.
    main TyGR Prefix Clauses :- std.do! [
      remove-underscore Prefix Variant,
      bedrock.get-ctors Variant Ctors,
      std.map Ctors (c\ c'\ c' = global (indc c)) CTerms,
      FiniteName is Variant ^ "_finite",
      derive.finite.mk-finite FiniteName CTerms TyGR C,
      Clauses = [finite-done TyGR, finite TyGR (const C)],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.stdpp.db" (clause _ _ x)
      ),
    ].
    main _ _ _ :- usage.

    pred usage.
    usage :- coq.error "Usage: derive.finite VariantGR Prefix Clauses".
  }

  dep1 "finite" "eq_dec".
  derivation
    (indt T) Prefix
    (derive "finite"
      (derive.finite.main (indt T) Prefix)
      (finite-done (indt T))
    ).
}}.
Elpi Typecheck derive.
