(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred compilation_unit.
Require Import bedrock.lang.cpp.semantics.

Section with_Σ.
  Context `{Σ : cpp_logic ti} {resolve:genv}.

  Local Notation _super := (_super (resolve:=resolve)) (only parsing).
  Local Notation _field := (_field (resolve:=resolve)) (only parsing).
  Local Notation _sub := (_sub (resolve:=resolve)) (only parsing).
  Local Notation uninitR := (uninitR (resolve:=resolve)) (only parsing).
  Local Notation anyR := (anyR (resolve:=resolve)) (only parsing).

  Axiom uninit_class_fwd
  : forall cls base st q,
    glob_def resolve cls = Some (Gstruct st) ->
    _at (Σ:=Σ) (_eqv base) (uninitR (Tnamed cls) q)
    |-- _at (_eqv base)
            (sepSPs (List.map (fun '(gn,_) =>
                                 _offsetR (_super cls gn)
                                          (uninitR (Tnamed gn) q)) st.(s_bases) ++
                     List.map (fun '(n,t,_) =>
                            (* todo(gmm): there is a problem with references in this code.
                             *)
                                 _offsetR
                                   (_field {| f_name := n ; f_type := cls |})
                                   (uninitR (erase_qualifiers t) q)) st.(s_fields))).

  Axiom anyR_class_bwd
  : forall cls base st q,
    glob_def resolve cls = Some (Gstruct st) ->
    _at (_eqv base)
        (sepSPs (List.map (fun '(gn,_) =>
                             _offsetR (_super cls gn) (anyR (Tnamed gn) q)) st.(s_bases) ++
                 List.map (fun '(n,t,_) =>
                             _offsetR (_field {| f_name := n ; f_type := cls |})
                                      (anyR (erase_qualifiers t) q)) st.(s_fields)))
    |-- _at (Σ:=Σ) (_eqv base) (anyR (Tnamed cls) q).

  Axiom uninit_array : forall t n q,
    uninitR (Tarray t n) q
    -|- sepSPs (map (fun i => _offsetR (_sub t (Z.of_nat i)) (uninitR t q)) (seq 0 (BinNatDef.N.to_nat n))).

  Axiom anyR_array : forall t n q,
    anyR (Tarray t n) q
    -|- sepSPs (map (fun i => _offsetR (_sub t (Z.of_nat i)) (anyR t q)) (seq 0 (BinNatDef.N.to_nat n))).
End with_Σ.
