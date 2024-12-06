(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.prelude.bytestring.

Set Primitive Projections.

Export core(Stmt'(..)).
Export core(VarDecl'(..)).

Notation Stmt := (Stmt' lang.cpp).
Notation MStmt := (Stmt' lang.temp).

Notation VarDecl := (VarDecl' lang.cpp).
Notation MVarDecl := (VarDecl' lang.temp).

Definition Sskip {lang} : Stmt' lang := Sseq nil.

