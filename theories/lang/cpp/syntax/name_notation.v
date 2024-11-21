(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require bedrock.lang.cpp.syntax.core.
Require Export bedrock.lang.cpp.syntax.notations.
Require bedrock.lang.cpp.syntax.name_notation.parser.
Require bedrock.lang.cpp.syntax.name_notation.printer.

Bind Scope cpp_name_scope with core.name.

String Notation core.name parser.parse_name printer.print_name : cpp_name_scope.

(* Name Aliases *)
Bind Scope cpp_name_scope with core.globname.
Bind Scope cpp_name_scope with core.obj_name.

(* the parser for fields adds a sanity check that it starts with [Nscoped] *)
#[local]
Definition field_parser (ls : list Byte.byte) : option core.field :=
  match parser.parse_name ls with
  | Some (core.Nscoped _ _) as x => x
  | _ => None
  end.
#[local]
Definition field_printer (f : core.field) : option (list Byte.byte) :=
  match f with
  | core.Nscoped _ _ => printer.print_name f
  | _ => None
  end.
String Notation core.field field_parser field_printer : cpp_field_scope.

Fail Check "foo"%cpp_field.
Succeed Example _0 : "foo"%cpp_name = "foo"%cpp_name := eq_refl.

(** String Notations for types *)
String Notation core.type parser.parse_type printer.print_type : cpp_type_scope.
Bind Scope cpp_type_scope with core.type.
