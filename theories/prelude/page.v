(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import base addr.

(** page attributes *)
Module attrs.
Record t : Set :=
{ read  : bool
; write : bool
; exec  : bool
; user  : bool }.

Definition R : t :=
{| read := true ; write := false ; exec := false ; user := true |}.

Definition RW : t :=
{| read := true ; write := true ; exec := false ; user := true |}.

Definition RWX : t :=
{| read := true ; write := true ; exec := true ; user := true |}.

#[global] Instance t_eqdec : EqDecision t.
Proof. solve_decision. Defined.

#[global] Instance t_inh : Inhabited t := populate R.

#[global] Instance t_countable : Countable t.
Proof.
  apply (inj_countable'
    (λ a : t, ((read a, write a), (exec a, user a)))
    (λ n, {| read := n.1.1 ; write := n.1.2 ; exec := n.2.1 ; user := n.2.2 |})).
  abstract (by intros []).
Qed.
End attrs.

(* XXX Module [base] is a compatibility hack that will be inlined. *)
Module Export base.
#[deprecated(note="")]
Notation Attrs := attrs.t (only parsing).
End base.

(** page table levels, 0 is the smallest page table level *)
Definition Level : Set := nat.
Bind Scope nat_scope with Level.
