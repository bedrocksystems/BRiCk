(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.parser.prelude.
Require Import bedrock.lang.cpp.parser.lang.

(** * Derived declaration helpers emitted by cpp2v *)

Module ParserDecl (Import Lang : PARSER_LANG).
  #[local] Notation obj_name := (obj_name' parser_lang).

  Definition pure_virt (on : obj_name) : obj_name * option obj_name :=
    (on, None).
  Definition impl_virt (on : obj_name) : obj_name * option obj_name :=
    (on, Some on).

  (* This is used for base classes. *)
  Definition mkBase (on : classname' parser_lang) (li : LayoutInfo) : classname' parser_lang * LayoutInfo :=
    (on, li).

End ParserDecl.
