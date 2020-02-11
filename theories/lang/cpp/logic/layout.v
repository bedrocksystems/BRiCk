(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.logic Require Import
     pred heap_pred compilation_unit.
Require Import bedrock.lang.cpp.semantics.

Section with_Σ.
  Context {Σ : gFunctors} {resolve:genv}.

  Local Notation mpred := (mpred Σ) (only parsing).
  Local Notation _super := (_super (resolve:=resolve)) (only parsing).
  Local Notation _field := (_field (resolve:=resolve)) (only parsing).
  Local Notation _sub := (_sub (resolve:=resolve)) (only parsing).
  Local Notation uninit := (uninit (Σ:=Σ) (resolve:=resolve)) (only parsing).
  Local Notation tany := (tany (Σ:=Σ) (resolve:=resolve)) (only parsing).

Axiom uninit_class_fwd
  : forall cls base st q,
    glob_def resolve cls = Some (Gstruct st) ->
    _at (Σ:=Σ) (_eq base) (uninit (Tref cls) q)
    |-- _at (_eq base)
            (sepSPs (List.map (fun '(gn,_) =>
                                 _offsetR (_super cls gn)
                                          (uninit (Tref gn) q)) st.(s_bases) ++
                     List.map (fun '(n,t,_) =>
                            (* todo(gmm): there is a problem with references in this code.
                             *)
                                 _offsetR
                                   (_field {| f_name := n ; f_type := cls |})
                                   (uninit (erase_qualifiers t) q)) st.(s_fields))).

Axiom tany_class_bwd
: forall cls base st q,
    glob_def resolve cls = Some (Gstruct st) ->
    _at (_eq base)
        (sepSPs (List.map (fun '(gn,_) =>
                             _offsetR (_super cls gn) (tany (Tref gn) q)) st.(s_bases) ++
                 List.map (fun '(n,t,_) =>
                             _offsetR (_field {| f_name := n ; f_type := cls |})
                                      (tany (erase_qualifiers t) q)) st.(s_fields)))
    |-- _at (Σ:=Σ) (_eq base) (tany (Tref cls) q).

Axiom uninit_array : forall t n q,
    uninit (Tarray t n) q
    -|- sepSPs (map (fun i => _offsetR (_sub t (Z.of_nat i)) (uninit t q)) (seq 0 (BinNatDef.N.to_nat n))).

Axiom tany_array : forall t n q,
    tany (Tarray t n) q
    -|- sepSPs (map (fun i => _offsetR (_sub t (Z.of_nat i)) (tany t q)) (seq 0 (BinNatDef.N.to_nat n))).
End with_Σ.
