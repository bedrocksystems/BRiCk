(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.bi.ChargeCompat.
From bedrock.lang.cpp Require Import ast semantics.
Require Import bedrock.lang.cpp.arith.builtins.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp.

Section with_Σ.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.
  Variables (M : coPset) (ti : thread_info).

  (****** Wp Semantics for builtins
   *)
  Parameter wp_builtin :
      forall {resolve:genv}, coPset -> thread_info ->
        BuiltinFn -> type (* the type of the builtin *) ->
        list val -> (val -> mpred) -> mpred.

  Local Notation BUILTIN := (wp_builtin (resolve:=resolve) M ti).

  Lemma wp_unreachable : forall Q,
      False |-- BUILTIN Bin_unreachable (Tfunction Tvoid nil) nil Q.
  Proof. intros. iIntros "[]". Qed.

  Lemma wp_trap : forall Q,
      False |-- BUILTIN Bin_trap (Tfunction Tvoid nil) nil Q.
  Proof. intros. iIntros "[]". Qed.

  Axiom wp_expect : forall exp c Q,
      Q exp |-- BUILTIN Bin_expect (Tfunction (Tint W64 Signed) (Tint W64 Signed :: Tint W64 Signed :: nil)) (exp :: c :: nil) Q.

  (** Bit computations
   *)

  (* Returns one plus the index of the least significant 1-bit of x,
     or if x is zero, returns zero. *)
  Definition ffs_spec (sz : bitsize) (n : Z) (Q : val -> mpred) : mpred :=
    [| has_type (Vint n) (Tint sz Signed) |] ** Q (Vint (first_set sz n)).

  Axiom wp_ffs : forall sz c Q,
          ffs_spec sz c Q
      |-- BUILTIN Bin_ffs (Tfunction (Tint sz Signed) (Tint sz Signed :: nil)) (Vint c :: nil) Q.

  Axiom wp_ffsl : forall sz c Q,
          ffs_spec sz c Q
      |-- BUILTIN Bin_ffsl (Tfunction (Tint sz Signed) (Tint sz Signed :: nil)) (Vint c :: nil) Q.

  Axiom wp_ffsll : forall sz c Q,
          ffs_spec sz c Q
      |-- BUILTIN Bin_ffsll (Tfunction (Tint sz Signed) (Tint sz Signed :: nil)) (Vint c :: nil) Q.

  (* Returns the number of trailing 0-bits in x, starting at the least
     significant bit position. If x is 0, the result is undefined. *)


  Definition ctz_spec (sz : bitsize) (n : Z) (Q : val -> mpred) : mpred :=
    [| has_type (Vint n) (Tint sz Unsigned) |] ** [| n <> 0 |] ** Q (Vint (trailing_zeros sz n)).

  Axiom wp_ctz : forall sz c Q,
          ctz_spec sz c Q
      |-- BUILTIN Bin_ctz (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_ctzl : forall sz c Q,
          ctz_spec sz c Q
      |-- BUILTIN Bin_ctzl (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_ctzll : forall sz c Q,
          ctz_spec sz c Q
      |-- BUILTIN Bin_ctzll (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  (* Returns the number of leading 0-bits in x, starting at the most significant
     bit position. If x is 0, the result is undefined. *)
  Definition clz_spec (sz : bitsize) (n : Z) (Q : val -> mpred) : mpred :=
    [| has_type (Vint n) (Tint sz Unsigned) |] ** [| n <> 0 |] ** Q (Vint (leading_zeros sz n)).

  Axiom wp_clz : forall sz c Q,
          clz_spec sz c Q
      |-- BUILTIN Bin_clz (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_clzl : forall sz c Q,
          clz_spec sz c Q
      |-- BUILTIN Bin_clzl (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_clzll : forall sz c Q,
          clz_spec sz c Q
      |-- BUILTIN Bin_clzll (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  (* Returns x with the order of the bytes reversed; for example, 0xaabb becomes
     0xbbaa. Byte here always means exactly 8 bits. *)
  Axiom wp_bswap16 : forall x Q,
          [| has_type (Vint x) (Tint W16 Unsigned) |] ** Q (Vint (bswap W16 x))
      |-- BUILTIN Bin_bswap16 (Tfunction (Tint W16 Unsigned) (Tint W16 Unsigned :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap32 : forall x Q,
          [| has_type (Vint x) (Tint W32 Unsigned) |] ** Q (Vint (bswap W32 x))
      |-- BUILTIN Bin_bswap32 (Tfunction (Tint W32 Unsigned) (Tint W32 Unsigned :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap64 : forall x Q,
          [| has_type (Vint x) (Tint W64 Unsigned) |] ** Q (Vint (bswap W64 x))
      |-- BUILTIN Bin_bswap64 (Tfunction (Tint W64 Unsigned) (Tint W64 Unsigned :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap128 : forall x Q,
          [| has_type (Vint x) (Tint W128 Unsigned) |] ** Q (Vint (bswap W128 x))
      |-- BUILTIN Bin_bswap128 (Tfunction (Tint W128 Unsigned) (Tint W128 Unsigned :: nil))
          (Vint x :: nil) Q.


  (** std::launder (http://eel.is/c++draft/ptr.launder) *)
  Axiom wp_launder : forall ty res newp Q,
      provides_storage res newp ty ** (provides_storage res newp ty -* Q (Vptr newp))
      |-- BUILTIN Bin_launder (Tfunction (Tptr Tvoid) (Tptr Tvoid :: nil))
          (Vptr res :: nil) Q.

End with_Σ.
