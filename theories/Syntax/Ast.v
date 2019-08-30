(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
Require Import Coq.NArith.BinNatDef.
From Coq.Strings Require Import
     Ascii String.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.

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

Record type_qualifiers : Set :=
{ q_const : bool
; q_volatile : bool }.
Global Instance Decidable_eq_type_qualifiers (a b : type_qualifiers) : Decidable (a = b).
Proof.
refine
  {| Decidable_witness := decide (a.(q_const) = b.(q_const)) && decide (a.(q_volatile) = b.(q_volatile))
   |}.
rewrite Bool.andb_true_iff. repeat rewrite decide_ok.
destruct a; destruct b; simpl; firstorder; congruence.
Defined.

Definition merge_tq (a b : type_qualifiers) : type_qualifiers :=
  {| q_const := a.(q_const) || b.(q_const)
   ; q_volatile := a.(q_volatile) || b.(q_volatile)
   |}.

Variant size : Set :=
| W8
| W16
| W32
| W64
| W128.

Definition N_of_size (s : size) : N :=
  match s with
  | W8   => 8
  | W16  => 16
  | W32  => 32
  | W64  => 64
  | W128 => 128
  end.

Definition Z_of_size (s : size) : Z :=
  Z.of_N (N_of_size s).

Bind Scope N_scope with size.

Coercion N_of_size : size >-> N.
Lemma of_size_gt_O w :
  (0 < 2 ^ Z_of_size w)%Z.
Proof. unfold Z_of_size. unfold BinIntDef.Z.of_N. unfold N_of_size. destruct w; reflexivity. Qed.
Hint Resolve of_size_gt_O.






(*
(* global declarations *)
Variant Decl : Set :=
| Dvar         (name : obj_name) (_ : type) (_ : option Expr)

| Dfunction    (name : obj_name) (_ : Func)
| Dmethod      (name : obj_name) (_ : Method)
| Dconstructor (name : obj_name) (_ : Ctor)
| Ddestructor  (name : obj_name) (_ : Dtor)

| Dunion       (name : globname) (_ : option Union)
| Dstruct      (name : globname) (_ : option Struct)
  (* ^ structures & classes *)

| Denum        (name : globname) (_ : option type) (branches : list (ident * option Expr))
  (* ^ enumerations (the initializers need to be constant expressions) *)
| Dconstant    (name : globname) (_ : type) (_ : Expr)

| Dtypedef     (name : globname) (_ : type)
(*
| Dtemplated   (_ : list (OrType type * ident)) (_ : Decl)
               (instantiations : list Decl)
*)
  (* ^ right now this just expands the template, it should change *)
.

Definition module : Set :=
  list Decl.
*)
