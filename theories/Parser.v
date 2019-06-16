(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Coq Require Export
     Strings.Ascii
     Strings.String
     Lists.List.

Require Export Coq.ZArith.BinInt.

From Cpp Require Export Ast.

Definition Nanon (ty : globname) : globname :=
  String "#"%char ty.

Definition Talias (underlying : type) (name : globname) : type :=
  underlying.

Definition NStop : list ident := nil.

Bind Scope string_scope with globname.
Bind Scope string_scope with obj_name.
Bind Scope string_scope with ident.
Bind Scope string_scope with localname.
