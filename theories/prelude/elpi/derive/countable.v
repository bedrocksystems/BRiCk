(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import elpi.
From elpi.apps Require Import derive.

From bedrock.prelude.elpi Require Import prelude derive.stdpp.

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
      remove-final-underscore Prefix Variant,
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
