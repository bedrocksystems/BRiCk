(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
From Coq.Strings Require Import
     Ascii String.

Require Import Cpp.Util.

Set Primitive Projections.

Local Open Scope N_scope.


(* this represents names that exist in object files. *)
Definition obj_name : Set := string.

Definition ident : Set := string.

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
Global Instance Decidable_eq_globname : forall a b : globname, Decidable (a = b) :=
  Decidable_eq_string.

(* local names *)
Definition localname : Set := ident.

Global Instance Decidable_eq_localname : forall a b : localname, Decidable (a = b) :=
  Decidable_eq_string.

Record field : Set :=
{ f_type : globname (* name of struct or class *)
; f_name : ident
}.
Global Instance Decidable_eq_field (a b : field) : Decidable (a = b).
Proof.
refine
  {| Decidable_witness :=
       decide (a.(f_type) = b.(f_type)) && decide (a.(f_name) = b.(f_name))
   ; Decidable_spec := _ |}.
  rewrite Bool.andb_true_iff. repeat rewrite decide_ok.
  destruct a, b; simpl; split; firstorder congruence.
Defined.
