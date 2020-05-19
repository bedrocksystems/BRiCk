(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred translation_unit.
Require Import bedrock.lang.cpp.semantics.

Section with_Σ.
  Context `{Σ : cpp_logic} {resolve:genv}.

  Local Notation _super := (_super (resolve:=resolve)) (only parsing).
  Local Notation _field := (_field (resolve:=resolve)) (only parsing).
  Local Notation _sub := (_sub (resolve:=resolve)) (only parsing).
  Local Notation anyR := (anyR (resolve:=resolve)) (only parsing).

  Definition borrow_from {PROP : bi} (part all : PROP) : PROP :=
    part ** (part -* all).

  Axiom decompose_struct
  : forall cls st q,
    glob_def resolve cls = Some (Gstruct st) ->
    anyR (Tnamed cls) q
    |-- borrow_from
          (([∗list] base ∈ st.(s_bases),
              let '(gn,_) := base in
              _offsetR (_super cls gn) (anyR (Tnamed gn) q)) **
           ([∗list] fld ∈ st.(s_fields),
              let '(n,ty,_) := fld in
              _offsetR (_field {| f_name := n ; f_type := cls |})
                       (anyR (erase_qualifiers ty) q)))
          (anyR (Tnamed cls) q).

  Axiom decompose_union
  : forall (cls : globname) st q,
    glob_def resolve cls = Some (Gunion st) ->
    anyR (Tnamed cls) q
    |-- [∧list] it ∈ st.(u_fields),
           let '(i, t, _) := it in
           let f := _field {| f_name := i ; f_type := cls |} in
           borrow_from (_offsetR f (anyR (erase_qualifiers t) q))
                       (anyR (Tnamed cls) q).

  Axiom decompose_array : forall t n q,
    anyR (Tarray t n) q
    |-- borrow_from ([∗list] i ∈ seq 0 (BinNatDef.N.to_nat n),
                       _offsetR (_sub t (Z.of_nat i)) (anyR t q))
                    (anyR (Tarray t n) q).

End with_Σ.
