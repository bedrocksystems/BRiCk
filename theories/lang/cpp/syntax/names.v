(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
From Coq.Strings Require Import
     Ascii String.
Require Import stdpp.strings.
Require Import bedrock.Util.

Set Primitive Projections.

Local Open Scope N_scope.

(* this represents names that exist in object files. *)
Definition obj_name : Set := string.
Global Instance obj_name_eq: EqDecision obj_name := _.

Definition ident : Set := string.
Global Instance ident_eq: EqDecision ident := _.

(* naming in C++ is complex.
 * - everything has a path, e.g. namespaces, classes, etc.
 *   examples: ::foo         -- the namespace `foo`
 *             ::Foo         -- the class/struct/enum `Foo`
 *             ::Foo<int, 1> -- templated class (template parameters are types *and* expressions)
 * - functions (but not variables) can be overloaded.
 *   (this is addressed via name mangling)
 * - types (classes, structs, typedefs, etc) are not mangled because they are
 *   not present in the object file
 * - there are also "unnamed" functions, e.g. constructors and destructors
 *)
Definition globname : Set := string.
  (* these are mangled names. for consistency, we're going to
   * mangle everything.
   *)
Global Instance globname_eq: EqDecision globname := _.

(* local names *)
Definition localname : Set := ident.
Global Instance localname_eq: EqDecision localname := _.

Record field : Set :=
{ f_type : globname (* name of struct or class *)
; f_name : ident
}.
Global Instance field_eq: EqDecision field.
Proof. solve_decision. Defined.
