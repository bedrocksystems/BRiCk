(*
 * Copyright (c) 2023-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.mparser.prelude.
Require Export bedrock.lang.cpp.parser.stmt.
Require Import bedrock.lang.cpp.syntax.typing.

(** ** Template-only derived variable declarations emitted by cpp2v *)

#[local] Definition set_declared_type (t : Mdecltype) (e : MExpr) : MExpr :=
  match e with
  | Eunresolved_parenlist None es => Eunresolved_parenlist (Some t) es
  (**
  TODO: The same treatment for other direct initiailization
  expressions.
  *)
  | _ => e
  end.

Definition Dvar (name : localname) (t : Mdecltype) (init : option MExpr) : MVarDecl :=
  Dvar name t (set_declared_type t <$> init).

