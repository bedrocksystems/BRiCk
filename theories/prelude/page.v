(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import base addr.

(** Page attributes *)
Module attrs.
(**
TODO FM-1051: Strictly speaking, this belongs to the NOVA specs, since this is
NOVA's abstraction of page mapping attributes, and need not have a canonical
mapping to hardware page attributes.
*)
Record t : Set :=
{ read  : bool
; write : bool
; uexec : bool
; sexec : bool }.
(** Page Table Entry *)
Definition pteT : Set := paddr * attrs.t.
(** Optional Page Table Entry *)
Definition opteT : Set := option pteT.

#[deprecated(note="")]
Notation user := uexec (only parsing).

Definition R : t :=
{| read := true ; write := false ; sexec := false ; uexec := false |}.

Definition RW : t :=
{| read := true ; write := true ; sexec := false ; uexec := false |}.

Definition RWX : t :=
{| read := true ; write := true ; sexec := true ; uexec := true |}.

#[global] Instance t_eqdec : EqDecision t.
Proof. solve_decision. Defined.

#[global] Instance t_inh : Inhabited t := populate R.

#[global] Instance t_countable : Countable t.
Proof.
  apply (inj_countable'
    (λ a : t, ((read a, write a), (uexec a, sexec a)))
    (λ n, {| read := n.1.1 ; write := n.1.2 ; uexec := n.2.1 ; sexec := n.2.2 |})).
  abstract (by intros []).
Qed.

Definition is_r (a : attrs.t) : bool :=
  a.(read).

Definition is_rw (a : attrs.t) : bool :=
  a.(read) && a.(write).

Definition is_rwux (a : attrs.t) : bool :=
  is_rw a && a.(uexec).

Definition is_rwsx (a : attrs.t) : bool :=
  is_rw a && a.(sexec).

Definition nonnull (a : attrs.t) : bool :=
  read a || write a || uexec a || sexec a.

Definition masked (perm_mask : N) (a : attrs.t) : attrs.t :=
  {| read  := andb (N.testbit perm_mask 0) (read  a)
   ; write := andb (N.testbit perm_mask 1) (write a)
   ; uexec := andb (N.testbit perm_mask 2) (uexec a)
   ; sexec := andb (N.testbit perm_mask 3) (sexec a)
  |}.

Definition masked_opt (perm_mask : N) (a : attrs.t) : option attrs.t :=
  let res := masked perm_mask a in
  guard (nonnull res); Some res.

Definition opte_mask (perm_mask : N) (opte : opteT) : opteT :=
  '(pa, pte) ← opte;
  masked ← masked_opt perm_mask pte;
  Some (pa, masked).

End attrs.
Notation pteT := attrs.pteT.
Notation opteT := attrs.opteT.

(** page table levels, 0 is the smallest page table level *)
Definition Level : Set := nat.
Bind Scope nat_scope with Level.
