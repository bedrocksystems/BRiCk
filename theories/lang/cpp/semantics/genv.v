(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License. 
 * See the LICENSE-BedRock file in the repository root for details. 
 *)
From bedrock.lang.prelude Require Import base.
From bedrock.lang.cpp.syntax Require Export types translation_unit.
From bedrock.lang.cpp.semantics Require Export sub_module.

(**
A [genv] describes the dynamic semantics of one (TODO: or more?) translation
units.
It contains the represented translation units, plus any additional
information supplied by compiler/linker/loader/...

If we want to do things like word-size agnostic verification, then
information about sizes etc. would need to move in here as well.

TODO: seal this?
*)
Record genv : Type :=
{ genv_tu : translation_unit
  (* ^ the [translation_unit] *)
; pointer_size_bitsize : bitsize
  (* ^ the size of a pointer *)
}.
Existing Class genv.
Definition genv_byte_order (g : genv) : endian :=
  g.(genv_tu).(byte_order).
Definition pointer_size (g : genv) := bytesN (pointer_size_bitsize g).

(** * global environments *)

(** [genv_leq a b] states that [b] is an extension of [a] *)
Record genv_leq {l r : genv} : Prop :=
{ tu_le : sub_module l.(genv_tu) r.(genv_tu)
; pointer_size_le : l.(pointer_size_bitsize) = r.(pointer_size_bitsize) }.
Arguments genv_leq _ _ : clear implicits.

Instance PreOrder_genv_leq : PreOrder genv_leq.
Proof.
  constructor.
  { constructor; auto; reflexivity. }
  { red. destruct 1; destruct 1; constructor; try etransitivity; eauto. }
Qed.
Instance: RewriteRelation genv_leq := {}.

Definition genv_eq (l r : genv) : Prop :=
  genv_leq l r /\ genv_leq r l.

Instance genv_tu_proper : Proper (genv_leq ==> sub_module) genv_tu.
Proof. solve_proper. Qed.
Instance genv_tu_flip_proper : Proper (flip genv_leq ==> flip sub_module) genv_tu.
Proof. solve_proper. Qed.

(* Sadly, neither instance is picked up by [f_equiv]. *)
Instance pointer_size_bitsize_proper : Proper (genv_leq ==> eq) pointer_size_bitsize.
Proof. solve_proper. Qed.
Instance pointer_size_bitsize_flip_proper : Proper (flip genv_leq ==> eq) pointer_size_bitsize.
Proof. by intros ?? <-. Qed.
Instance pointer_size_proper : Proper (genv_leq ==> eq) pointer_size.
Proof. unfold pointer_size; intros ???. f_equiv. exact: pointer_size_bitsize_proper. Qed.
Instance pointer_size_flip_proper : Proper (flip genv_leq ==> eq) pointer_size.
Proof. by intros ?? <-. Qed.

Instance genv_byte_order_proper : Proper (genv_leq ==> eq) genv_byte_order.
Proof. intros ???. apply sub_module.byte_order_proper. solve_proper. Qed.
Instance genv_byte_order_flip_proper : Proper (flip genv_leq ==> eq) genv_byte_order.
Proof. by intros ?? <-. Qed.
(* this states that the [genv] is compatible with the given [translation_unit]
 * it essentially means that the [genv] records all the types from the
 * compilation unit and that the [genv] contains addresses for all globals
 * defined in the [translation_unit]
 *)
Class genv_compat {tu : translation_unit} {g : genv} : Prop :=
{ tu_compat : sub_module tu g.(genv_tu) }.
Arguments genv_compat _ _ : clear implicits.
Infix "⊧" := genv_compat (at level 1).

Theorem genv_byte_order_tu tu g :
    tu ⊧ g ->
    genv_byte_order g = translation_unit.byte_order tu.
Proof. intros. apply byte_order_flip_proper, tu_compat. Qed.

Theorem genv_compat_submodule : forall m σ, m ⊧ σ -> sub_module m σ.(genv_tu).
Proof. by destruct 1. Qed.

Instance genv_compat_proper : Proper (flip sub_module ==> genv_leq ==> impl) genv_compat.
Proof.
  intros ?? Heq1 ?? [Heq2 _] [Heq3]; constructor.
  by rewrite Heq1 Heq3.
Qed.
Instance genv_compat_flip_proper : Proper (sub_module ==> flip genv_leq ==> flip impl) genv_compat.
Proof. solve_proper. Qed.

(* XXX rename/deprecate? *)
Theorem subModuleModels a b σ : b ⊧ σ -> sub_module a b -> a ⊧ σ.
Proof. by intros ? ->. Qed.
