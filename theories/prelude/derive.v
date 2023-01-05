(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import ssreflect. (*for [case]*)

From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

Require Import bedrock.prelude.elpi.prelude.

Require Import bedrock.prelude.finite.

Definition ap {M A B} `{!MRet M, !MBind M} (mf : M (A → B)) : M A → M B :=
  λ ma, f ← mf; a ← ma; mret (f a).
(* We use level 61 for <*> following <$>; ext-lib also has matching levels, but
different ones. *)
Infix "<*>" := ap (at level 61, left associativity).

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
Elpi Accumulate derive Db bedrock.prelude.db.

Elpi Accumulate derive lp:{{
  pred remove-underscore i:string, o:string.
  remove-underscore S S' :- std.do! [
    rex.replace "_" "" S S',
  ].
}}.

(***************************************************
 EqDecision
 ***************************************************)
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
      remove-underscore Prefix Prefix',
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
        coq.elpi.accumulate _ "derive.stdpp.db" (clause _ _ x)
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

(***************************************************
 Inhabited
 ***************************************************)
Elpi Accumulate derive lp:{{
  namespace derive.inhabited {
    pred main i:gref, i:string, o:list prop.
    main TyGR Prefix Clauses :- std.do! [
      remove-underscore Prefix Prefix',
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

(***************************************************
 Countable
 ***************************************************)
(** This Gallina function is used at code generation time (not at runtime) to produce the
    positive associated to a particular value [a : T], given the list of all constructors [l : list T]. *)
Fixpoint lookup_from_ctorlist `{EqDecision T} (p : positive) (l : list T) (a : T) : positive :=
  match l with
  | [] => p
  | a' :: l' => if bool_decide (a = a') then p else lookup_from_ctorlist (p + 1)%positive l' a
  end.

(** TODO: This generic decoding function is used in generated [Countable] instances but isn't efficient.
    It would be better to replace it by a table that's built at code generation time. *)
Fixpoint decode_from_encode `{EqDecision T} (encode : T -> positive) (l : list T) (x : positive) : option T :=
  match l with
  | [] => None
  | a :: l' => if bool_decide (encode a = x) then Some a else decode_from_encode encode l' x
  end.

(** This needs to be exported for use by callers of Deriving but shouldn't be otherwise used outside this module.*)
Ltac DERIVING_solve_countable := by case. (** TODO: [abstract] *)

Elpi Db derive.countable.db lp:{{
  namespace derive.countable {
    /*
    [mk-countable CtorList Name T] assumes that type [T] has
    constructors [CtorList] and generates a global instance [Name : Countable T].
    */
    pred ctor-to-positive i:term, i:term, o:term.
    ctor-to-positive CtorList K Pos :- std.do! [
      T = {{ @lookup_from_ctorlist _ _ 1%positive lp:CtorList lp:K }},
      std.assert-ok! (coq.elaborate-skeleton T _ EPos) "asdfasdf",
      coq.reduction.vm.norm EPos _ Pos,
    ].

    pred rty i:term, i:term, i:list term, i:list term, o:term.
    rty RTy _ _ _ RTy.

    pred to-positive-branch i:term, i:term, i:term, i:list term, i:list term, o:term.
    to-positive-branch CtorList K _Kty _Vars _VarsTys PosEncoding :- std.do![
      ctor-to-positive CtorList K PosEncoding
    ].

    pred to-positive i:term, i:term, i:term, i:term, o:term.
    to-positive CtorList S Ty RTy Match :-
      coq.build-match S Ty (rty RTy) (to-positive-branch CtorList) Match.

    pred mk-countable i:list term, i:string, i:gref, o:constant.
    mk-countable Ctors Name VariantGR C :- std.do![
      bedrock.elpi-list->list Ctors CtorList,
      std.assert-ok! (coq.elaborate-skeleton CtorList _ ECtorList) "[mk-countable] failed to elaborate ctors",
      VariantTy = global VariantGR,
      Encode = {{ fun (x : lp:VariantTy) => lp:{{ { to-positive ECtorList {{ x }} VariantTy {{ positive }} } }} }},
      Decode = {{ @decode_from_encode lp:VariantTy _ lp:Encode lp:CtorList }},
      Lem = {{ forall x : lp:VariantTy, lp:Decode (lp:Encode x) = Some x }},
      std.assert-ok! (coq.elaborate-skeleton Lem _ ELem) "[mk-countable] failed to elaborate lem",
      std.assert-ok! (coq.typecheck {{ lp:Bo : lp:ELem }} _) "[mk-countable] failed to typecheck lem",
      coq.ltac.collect-goals Bo [SealedGoal] [],
      coq.ltac.open (coq.ltac.call "DERIVING_solve_countable" []) SealedGoal [],
      Inst = {{ @Build_Countable lp:VariantTy _ lp:Encode lp:Decode lp:Bo }},
      std.assert-ok! (coq.elaborate-skeleton Inst _ EInst) "[mk-countable] failed to elaborate instance",
      coq.env.add-const Name EInst _ ff C,
      @global! => coq.TC.declare-instance (const C) 0, %%TODO: previously level 5; was there a reason?
    ].
  }
}}.

Elpi Accumulate derive Db derive.countable.db.
Elpi Accumulate derive lp:{{
  namespace derive.countable {
    pred main i:gref, i:string, o:list prop.
    main TyGR Prefix Clauses :- std.do! [
      remove-underscore Prefix Variant,
      bedrock.get-ctors Variant Ctors,
      std.map Ctors (c\ c'\ c' = global (indc c)) CTerms,
      CountableName is Variant ^ "_countable",
      derive.countable.mk-countable CTerms CountableName TyGR C,
      Clauses = [countable-done TyGR, countable TyGR (const C)],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.stdpp.db" (clause _ _ x)
      ),
    ].
    main _ _ _ :- usage.

    pred usage.
    usage :- coq.error "Usage: derive.finite VariantGR Prefix Clauses".
  }

  dep1 "countable" "eq_dec".
  derivation
    (indt T) Prefix
    (derive "countable"
      (derive.countable.main (indt T) Prefix)
      (countable-done (indt T))
    ).
}}.
Elpi Typecheck derive.

Module Tests.
  Variant T1 := A1 | B1 | C1.
  #[only(eq_dec)] derive T1.
  #[only(inhabited)] derive T1.
  #[only(countable)] derive T1.
  #[only(finite)] derive T1.

  (*TODO: Potential derive bug; the following produces:
    Anomaly: Uncaught exception Failure("split dirpath")*)
  (*#[only(finite)] derive
   Variant T2 := A2 | B2 | C2.*)

  #[only(eq_dec,inhabited)] derive
  Variant T2 := A2 | B2 | C2.
  #[only(countable)] derive T2.
  #[only(finite)] derive T2.
End Tests.
