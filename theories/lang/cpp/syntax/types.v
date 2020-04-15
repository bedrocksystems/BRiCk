(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.NArith.BinNatDef.
From Coq.Strings Require Import
     Ascii String.
Require Import Coq.ZArith.BinInt.

Require Import bedrock.Util.
Require Import bedrock.lang.cpp.syntax.names.

Set Primitive Projections.

(* Type qualifiers *)
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

(* Bit-widths *)
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
Proof. destruct w; reflexivity. Qed.
(* Hint Resolve of_size_gt_O. *)

(* Signed and Unsigned *)
Variant signed : Set := Signed | Unsigned.

(* types *)
Inductive type : Set :=
| Tpointer (_ : type)
| Treference (_ : type)
| Trv_reference (_ : type)
| Tint (size : size) (signed : signed)
| Tchar (size : size) (signed : signed)
| Tvoid
| Tarray (_ : type) (_ : N) (* unknown sizes are represented by pointers *)
| Tnamed (_ : globname)
| Tfunction (_ : type) (_ : list type)
| Tbool
| Tmember_pointer (_ : globname) (_ : type)
| Tqualified (_ : type_qualifiers) (_ : type)
| Tnullptr
.
Definition Talias (underlying : type) (name : globname) : type :=
  underlying.
Definition type_eq_dec : forall (ty1 ty2 : type), { ty1 = ty2 } + { ty1 <> ty2 }.
Proof.
  fix IHty1 1.
  repeat (decide equality).
Defined.
Global Instance Decidable_eq_type (a b : type) : Decidable (a = b) :=
  dec_Decidable (type_eq_dec a b).

Definition Qconst_volatile : type -> type :=
  Tqualified {| q_const := true ; q_volatile := true |}.
Definition Qconst : type -> type :=
  Tqualified {| q_const := true ; q_volatile := false |}.
Definition Qmut_volatile : type -> type :=
  Tqualified {| q_const := false ; q_volatile := true |}.
Definition Qmut : type -> type :=
  Tqualified {| q_const := false ; q_volatile := false |}.

Definition Tref : globname -> type := Tnamed.

(*
Record TypeInfo : Set :=
{ alignment : nat
; size : nat
; offset : list (field * nat)
}.
*)

Variant PrimCast : Set :=
| Cdependent (* this doesn't have any semantics *)
| Cbitcast
| Clvaluebitcast
| Cl2r
| Cnoop
| Carray2pointer
| Cfunction2pointer
| Cint2pointer
| Cpointer2int
| Cptr2bool
| Cderived2base
| Cintegral
| Cint2bool
| Cnull2ptr
| Cbuiltin2function
| Cconstructorconversion
| C2void
.
Global Instance Decidable_eq_PrimCast (a b : PrimCast) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality) : {a = b} + {a <> b}).

Variant Cast : Set :=
| CCcast       (_ : PrimCast)
| Cuser        (conversion_function : obj_name)
| Creinterpret (_ : type)
| Cstatic      (from to : globname)
| Cdynamic     (from to : globname)
| Cconst       (_ : type)
.
Global Instance Decidable_eq_Cast (a b : Cast) : Decidable (a = b) :=
  dec_Decidable (ltac:(decide equality; eapply Decidable_dec; refine _) : {a = b} + {a <> b}).

Section qual_norm.
  Context {A : Type}.
  Variable f : type_qualifiers -> type -> A.

  Fixpoint qual_norm' q t :=
    match t with
    | Tqualified q' t =>
      qual_norm' (merge_tq q q') t
    | _ =>
      f q t
    end.

  Definition qual_norm := qual_norm' {| q_const := false ; q_volatile := false |}.

End qual_norm.

Definition tqualified (q : type_qualifiers) (t : type) : type :=
  match q with
  | {| q_const := false ; q_volatile := false |} => t
  | _ => Tqualified q t
  end.

(** normalization of types
    - compresses adjacent [Tqualified] constructors
    - drops (irrelevant) qualifiers on function arguments and return types
 *)
Fixpoint normalize_type (t : type) : type :=
  let drop_norm :=
      qual_norm (fun _ t => normalize_type t)
  in
  let qual_norm :=
      (* merge adjacent qualifiers and then normalize *)
      qual_norm' (fun q t => tqualified q (normalize_type t))
  in
  match t with
  | Tpointer t => Tpointer (normalize_type t)
  | Treference t => Treference (normalize_type t)
  | Trv_reference t => Trv_reference (normalize_type t)
  | Tarray t n => Tarray (normalize_type t) n
  | Tfunction r args =>
    Tfunction (drop_norm r) (List.map drop_norm args)
  | Tmember_pointer gn t => Tmember_pointer gn (normalize_type t)
  | Tqualified q t => qual_norm q t
  | Tint _ _ => t
  | Tchar _ _ => t
  | Tbool => t
  | Tvoid => t
  | Tnamed _ => t
  | Tnullptr => t
  end.

Definition decompose_type : type -> type_qualifiers * type :=
  qual_norm (fun q t => (q, t)).


(* types with explicit size information
 *)
Definition T_int8    := Tint W8 Signed.
Definition T_uint8   := Tint W8 Unsigned.
Definition T_int16   := Tint W16 Signed.
Definition T_uint16  := Tint W16 Unsigned.
Definition T_int32   := Tint W32 Signed.
Definition T_uint32  := Tint W32 Unsigned.
Definition T_int64   := Tint W64 Signed.
Definition T_uint64  := Tint W64 Unsigned.
Definition T_int128  := Tint W128 Signed.
Definition T_uint128 := Tint W128 Unsigned.

(* note(gmm): types without explicit size information need to
 * be parameters of the underlying code, otherwise we can't
 * describe the semantics correctly.
 * - cpp2v should probably insert these types.
 *)
(**
https://en.cppreference.com/w/cpp/language/types
The 4 definitions below use the LP64 data model.
LLP64 and LP64 agree except for the [long] type: see
the warning below.
In future, we may want to parametrize by a data model, or
the machine word size.
*)
Definition char_bits : size := W8.
Definition short_bits : size := W16.
Definition int_bits : size := W32.
Definition long_bits : size := W64. (** warning: LLP64 model uses 32 *)
Definition long_long_bits : size := W64.

Definition T_ushort : type := Tint short_bits Unsigned.
Definition T_short : type := Tint short_bits Signed.
Definition T_ulong : type := Tint long_bits Unsigned.
Definition T_long : type := Tint long_bits Signed.
Definition T_ulonglong : type := Tint long_long_bits Unsigned.
Definition T_longlong : type := Tint long_long_bits Signed.
Definition T_uint : type := Tint int_bits Unsigned.
Definition T_int : type := Tint int_bits Signed.

Definition T_schar : type := Tchar char_bits Signed.
Definition T_uchar : type := Tchar char_bits Unsigned.


Coercion CCcast : PrimCast >-> Cast.
