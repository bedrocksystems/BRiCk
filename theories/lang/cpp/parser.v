(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Export
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Lists.List
        Coq.ZArith.BinInt.

Require Export bedrock.lang.cpp.ast.

Definition Nanon (ty : globname) : globname :=
  String "#"%char ty.

Definition Talias (underlying : type) (name : globname) : type :=
  underlying.

Definition NStop : list ident := nil.

Bind Scope string_scope with globname.
Bind Scope string_scope with obj_name.
Bind Scope string_scope with ident.
Bind Scope string_scope with localname.
Bind Scope Z_scope with Z.

Declare Custom Entry cppglobal.
Delimit Scope cppfield_scope with field.
Bind Scope cppfield_scope with field.

Notation "` e `" := e (e custom cppglobal at level 200, at level 0) : cppfield_scope.
