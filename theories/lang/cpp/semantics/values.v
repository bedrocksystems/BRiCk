(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** The "operational" style definitions about C++ values. *)
From Coq Require Import Strings.Ascii.
From bedrock.lang.prelude Require Import base addr option numbers.

Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.semantics Require Export types sub_module genv ptrs.

Local Close Scope nat_scope.
Local Open Scope Z_scope.
Implicit Types (σ : genv).

Module Type RAW_BYTES.
  (** * Raw bytes
      Raw bytes represent the low-level view of data.
      [raw_byte] abstracts over the internal structure of this low-level view of data.
      E.g. in the [simple_pred] model, [raw_byte] would be instantiated with [runtime_val].

      [raw_int_byte] is a raw byte that is a concrete integer values (i.e. not a
      pointer fragment or poison).
   *)
  Parameter raw_byte : Set.
  Parameter raw_byte_eq_dec : EqDecision raw_byte.
  Existing Instance raw_byte_eq_dec.

  Axiom raw_int_byte : N -> raw_byte.
End RAW_BYTES.

Module Type VAL_MIXIN (Import P : PTRS) (Import R : RAW_BYTES).

(** * Values
    Primitive abstract C++ runtime values come in two flavors.
    - pointers (also used for references)
    - integers (used for everything else)
    Aggregates are not represented directly, but only by talking about
    primitive subobjects.

    There is also a distinguished undefined element [Vundef] that
    models uninitialized values (https://eel.is/c++draft/basic.indet).
    Operations on [Vundef] are all undefined behavior.
    [Vraw] (a raw byte) represents the low-level bytewise view of data.
    See [logic/layout.v] for more axioms about it.
 *)
Variant val : Set :=
| Vint (_ : Z)
| Vptr (_ : ptr)
| Vraw (_ : raw_byte)
| Vundef
.
#[global] Notation Vref := Vptr (only parsing).

Definition val_dec : forall a b : val, {a = b} + {a <> b}.
Proof. solve_decision. Defined.
#[global] Instance val_eq_dec : EqDecision val := val_dec.
#[global] Instance val_inhabited : Inhabited val := populate (Vint 0).

End VAL_MIXIN.

(* Collect all the axioms. *)
Module Type PTRS_INTF_MINIMAL := PTRS <+ PTRS_DERIVED.
Module Type PTRS_INTF := PTRS_INTF_MINIMAL <+ RAW_BYTES.
Declare Module PTRS_INTF_AXIOM : PTRS_INTF.

(* Plug mixins. *)
Module Type PTRS_FULL_INTF := PTRS_INTF <+ VAL_MIXIN <+ PTRS_MIXIN.
Module Export PTRS_FULL_AXIOM : PTRS_FULL_INTF :=
  PTRS_INTF_AXIOM <+ VAL_MIXIN <+ PTRS_MIXIN.

Instance ptr_inhabited : Inhabited ptr := populate nullptr.

(** wrappers for constructing certain values *)
Definition Vchar (a : Ascii.ascii) : val :=
  Vint (Z.of_N (N_of_ascii a)).
Definition Vbool (b : bool) : val :=
  Vint (if b then 1 else 0).
Definition Vnat (b : nat) : val :=
  Vint (Z.of_nat b).
Definition Vn (b : N) : val :=
  Vint (Z.of_N b).
Notation Vz := Vint (only parsing).

(** we use [Vundef] as our value of type [void] *)
Definition Vvoid := Vundef.

Definition is_true (v : val) : option bool :=
  match v with
  | Vint v => Some (negb (Z.eqb v 0))
  | Vptr p => Some match ptr_eq_dec p nullptr with
                  | left _ => false
                  | right _ => true
                  end
  | Vundef | Vraw _ => None
  end.

Theorem is_true_int : forall i,
    is_true (Vint i) = Some (negb (BinIntDef.Z.eqb i 0)).
Proof. reflexivity. Qed.

Theorem Vptr_inj : forall p1 p2, Vptr p1 = Vptr p2 -> p1 = p2.
Proof. inversion 1; reflexivity. Qed.
Theorem Vint_inj : forall a b, Vint a = Vint b -> a = b.
Proof. inversion 1; reflexivity. Qed.
Theorem Vbool_inj : forall a b, Vbool a = Vbool b -> a = b.
Proof. by move=>[] [] /Vint_inj. Qed.

(** * regions
    to model the stack frame in separation logic, we use a notion of regions
    that are threaded through the semantics.

    we instantiate [region] as a stack of finite maps from variables
    to their addresses.
 *)
Inductive region : Type :=
| Remp (this : option ptr) (result : option ptr)
| Rbind (_ : localname) (_ : ptr) (_ : region).

Fixpoint get_location (ρ : region) (b : localname) : option ptr :=
  match ρ with
  | Remp _ _ => None
  | Rbind x p rs =>
    if decide (b = x) then Some p
    else get_location rs b
  end.

Fixpoint get_this (ρ : region) : option ptr :=
  match ρ with
  | Remp this _ => this
  | Rbind _ _ rs => get_this rs
  end.

Fixpoint get_result (ρ : region) : option ptr :=
  match ρ with
  | Remp _ result => result
  | Rbind _ _ rs => get_result rs
  end.

Definition max_val (bits : bitsize) (sgn : signed) : Z :=
  match bits , sgn with
  | W8   , Signed   => 2^7 - 1
  | W8   , Unsigned => 2^8 - 1
  | W16  , Signed   => 2^15 - 1
  | W16  , Unsigned => 2^16 - 1
  | W32  , Signed   => 2^31 - 1
  | W32  , Unsigned => 2^32 - 1
  | W64  , Signed   => 2^63 - 1
  | W64  , Unsigned => 2^64 - 1
  | W128 , Signed   => 2^127 - 1
  | W128 , Unsigned => 2^128 - 1
  end.

Definition min_val (bits : bitsize) (sgn : signed) : Z :=
  match sgn with
  | Unsigned => 0
  | Signed =>
    match bits with
    | W8   => -2^7
    | W16  => -2^15
    | W32  => -2^31
    | W64  => -2^63
    | W128 => -2^127
    end
  end.

Definition bound (bits : bitsize) (sgn : signed) (v : Z) : Prop :=
  min_val bits sgn <= v <= max_val bits sgn.

(** typedness of values
    note that only primitives fit into this, there is no [val] representation
    of aggregates, except through [Vptr p] with [p] pointing to the contents.
 *)

(**
[has_type v ty] is an approximation in [Prop] of "[v] is an initialized value
of type [t]." This implies:
- if [ty <> Tvoid], then [v <> Vundef].
- if [ty = Tint sz sgn], then [v] fits the appropriate bounds (see
[has_int_type']).
- if [ty] is a type of pointers/references/aggregates, we only ensure that [v
= Vptr p].
  *)
Parameter has_type : val -> type -> Prop.

Axiom has_type_pointer : forall v ty,
    has_type v (Tpointer ty) -> exists p, v = Vptr p.
Axiom has_type_nullptr : forall v,
    has_type v Tnullptr -> v = Vptr nullptr.
Axiom has_type_reference : forall v ty,
    has_type v (Treference ty) -> exists p, v = Vptr p /\ p <> nullptr.
Axiom has_type_rv_reference : forall v ty,
    has_type v (Trv_reference ty) -> exists p, v = Vptr p /\ p <> nullptr.
Axiom has_type_array : forall v ty n,
    has_type v (Tarray ty n) -> exists p, v = Vptr p /\ p <> nullptr.
Axiom has_type_named : forall v name,
    has_type v (Tnamed name) -> exists p, v = Vptr p /\ p <> nullptr.
Axiom has_type_function : forall v cc rty args,
    has_type v (Tfunction (cc:=cc) rty args) -> exists p, v = Vptr p /\ p <> nullptr.
Axiom has_type_member_pointer : forall v name ty,
    has_type v (Tmember_pointer name ty) -> exists p, v = Vptr p /\ p <> nullptr.

(* Not supported at the moment *)
Axiom has_type_arch : forall v osz bs,
    has_type v (Tarch osz bs) -> False.

(* Not supported at the moment *)
Axiom has_type_float : forall v sz,
    has_type v (Tfloat sz) -> False.

Axiom has_type_void : forall v,
    has_type v Tvoid -> v = Vundef.

Axiom has_nullptr_type : forall ty,
    has_type (Vptr nullptr) (Tpointer ty).

Axiom has_type_bool : forall v,
    has_type v Tbool <-> exists b, v = Vbool b.

Lemma has_bool_type : forall z,
  0 <= z < 2 <-> has_type (Vint z) Tbool.
Proof.
  intros z. rewrite has_type_bool. split=>Hz.
  - destruct (decide (z = 0)); simplify_eq; first by exists false.
    destruct (decide (z = 1)); simplify_eq; first by exists true. lia.
  - unfold Vbool in Hz. destruct Hz as [b Hb].
    destruct b; simplify_eq; lia.
Qed.

(** Note that from [has_type v (Tint sz sgn)] does not follow
  [v = Vint _] since [v] might also be [Vraw _] (for [T_uchar]). *)
Axiom has_int_type' : forall sz sgn v,
    has_type v (Tint sz sgn) <-> (exists z, v = Vint z /\ bound sz sgn z) \/ (exists r, v = Vraw r /\ Tint sz sgn = T_uchar).

Lemma has_int_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tint sz sgn).
Proof. move => *. rewrite has_int_type'. naive_solver. Qed.

Theorem has_char_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tchar sz sgn).
Proof. apply has_int_type. Qed.

Axiom has_type_qual : forall t q x,
    has_type x (drop_qualifiers t) ->
    has_type x (Tqualified q t).

#[global] Hint Resolve has_type_qual : has_type.

Arguments Z.add _ _ : simpl never.
Arguments Z.sub _ _ : simpl never.
Arguments Z.mul _ _ : simpl never.
Arguments Z.pow _ _ : simpl never.
Arguments Z.opp _ : simpl never.
Arguments Z.pow_pos _ _ : simpl never.

(* XXX adapter. *)
Definition glob_addr (σ : genv) (o : obj_name) : option ptr :=
  (fun _ => global_ptr σ.(genv_tu) o) <$> σ.(genv_tu) !! o.
