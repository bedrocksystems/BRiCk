(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.parser.reduction.
Require Export bedrock.lang.cpp.syntax.stmt. (* for [Sskip] *)
Require Import bedrock.lang.cpp.parser.name.
Require Import bedrock.lang.cpp.parser.type.
Require Import bedrock.lang.cpp.parser.expr.
Require Import bedrock.lang.cpp.parser.decl.
Require Export bedrock.lang.cpp.mparser.prelude.
Require Export bedrock.lang.cpp.mparser.type.
Require Export bedrock.lang.cpp.mparser.expr.
Require Export bedrock.lang.cpp.mparser.stmt.
Require Export bedrock.lang.cpp.mparser.tu.

#[local] Definition parser_lang : lang.t := lang.temp.
Include ParserName.
Include ParserType.
Include ParserExpr.
Include ParserDecl.

Definition Qconst_volatile : Mtype -> Mtype := Tqualified QCV.
Definition Qconst : Mtype -> Mtype := Tqualified QC.
Definition Qvolatile : Mtype -> Mtype := Tqualified QV.
