(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.prelude.base.

(* Bit-widths *)
Variant bitsize : Set :=
| W8
| W16
| W32
| W64
| W128.
Instance bitsize_eq: EqDecision bitsize.
Proof. solve_decision. Defined.
Instance bitsize_countable : Countable bitsize.
Proof.
  apply (inj_countable'
    (λ b,
      match b with
      | W8 => 0 | W16 => 1 | W32 => 2 | W64 => 3 | W128 => 4
      end)
    (λ n,
      match n with
      | 0 => W8 | 1 => W16 | 2 => W32 | 3 => W64 | 4 => W128
      | _ => W8	(* dummy *)
      end)).
  abstract (by intros []).
Defined.

Definition bitsN (s : bitsize) : N :=
  match s with
  | W8   => 8
  | W16  => 16
  | W32  => 32
  | W64  => 64
  | W128 => 128
  end.

Definition bitsZ (s : bitsize) : Z :=
  Z.of_N (bitsN s).

Definition bytesNat (s : bitsize) : nat :=
  match s with
  | W8 => 1
  | W16 => 2
  | W32 => 4
  | W64 => 8
  | W128 => 16
  end.

Definition bytesN (s : bitsize) : N :=
  N.of_nat (bytesNat s).

Definition bytesZ (s : bitsize) : Z :=
  Z.of_N (bytesN s).

Bind Scope N_scope with bitsize.

Lemma of_size_gt_O w :
  (0 < 2 ^ bitsZ w)%Z.
Proof. destruct w; reflexivity. Qed.
(* Hint Resolve of_size_gt_O. *)

(* Signed and Unsigned *)
Variant signed : Set := Signed | Unsigned.
Instance signed_eq_dec: EqDecision signed.
Proof. solve_decision. Defined.
Instance signed_countable : Countable signed.
Proof.
  apply (inj_countable'
    (λ s, if s is Signed then true else false)
    (λ b, if b then Signed else Unsigned)).
  abstract (by intros []).
Defined.

