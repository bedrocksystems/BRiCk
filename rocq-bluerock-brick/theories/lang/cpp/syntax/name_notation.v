(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require bedrock.lang.cpp.syntax.core.
Require Export bedrock.lang.cpp.syntax.notations.
Require bedrock.lang.cpp.syntax.name_notation.parser.
Require bedrock.lang.cpp.syntax.name_notation.printer.

Require Import bedrock.prelude.bytestring_core.

Bind Scope cpp_name_scope with core.name.

#[local]
Definition parse_name (bs : list Byte.byte) := parser.parse_name (BS.parse bs).
#[local]
Definition print_name (bs : core.name) :=
  match printer.print_name bs with
  | Some x => Some (BS.print x)
  | None => None
  end.
String Notation core.name parse_name print_name : cpp_name_scope.

(* Name Aliases *)
Bind Scope cpp_name_scope with core.globname.
Bind Scope cpp_name_scope with core.obj_name.

(* the parser for fields adds a sanity check that it starts with [Nscoped] *)
#[local]
Definition field_parser (ls : list Byte.byte) : option core.field :=
  match parse_name ls with
  | Some (core.Nscoped _ _) as x => x
  | _ => None
  end.
#[local]
Definition field_printer (f : core.field) : option (list Byte.byte) :=
  match f with
  | core.Nscoped _ _ => print_name f
  | _ => None
  end.
String Notation core.field field_parser field_printer : cpp_field_scope.

Fail Check "foo"%cpp_field.
Succeed Example _0 : "foo"%cpp_name = "foo"%cpp_name := eq_refl.

(** String Notations for types *)
#[local]
Definition parse_type (bs : list Byte.byte) := parser.parse_type (BS.parse bs).
#[local]
Definition print_type (bs : core.type) :=
  match printer.print_type bs with
  | Some x => Some (BS.print x)
  | None => None
  end.
String Notation core.type parse_type print_type : cpp_type_scope.
Bind Scope cpp_type_scope with core.type.
