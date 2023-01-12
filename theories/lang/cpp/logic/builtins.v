(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import iris.proofmode.proofmode.
Require Import bedrock.lang.bi.ChargeCompat.
From bedrock.lang.cpp Require Import ast semantics.
Require Import bedrock.lang.cpp.arith.builtins.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp.

Section with_Σ.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

  (****** Wp Semantics for builtins

    NOTE: we use a non-standard calling convention where values are passed
          as if they were all evaluated using [wp_operand].
   *)
  Parameter wp_builtin :
      forall {resolve:genv},
        BuiltinFn -> type (* the type of the builtin *) ->
        list val -> (val -> mpred) -> mpred.

  Fixpoint read_args (targs : list type) (ls : list ptr) (Q : list val -> mpred) : mpred :=
    match targs , ls with
    | nil , nil => Q nil
    | t :: ts , p :: ps =>
      Exists v, (Exists q, _at p (primR t q v)) //\\ read_args ts ps (fun vs => Q (v :: vs))
    | _ , _ => False
    end.

  (** [wp_builtin_func b fty ls Q] captures the semantics of a builtin function in the
      standard calling convention.
   *)
  Definition wp_builtin_func (b : BuiltinFn) (fty : type)
             (ls : list ptr) (Q : ptr -> mpred) : mpred :=
    match fty with
    | Tfunction rty targs =>
      read_args targs ls $ fun vs => wp_builtin b fty vs $ fun v => Forall p, _at p (primR rty (cQp.mut 1) v) -* Q p
    | _ => False
    end.

  Lemma wp_unreachable : forall Q,
      False |-- wp_builtin Bin_unreachable (Tfunction Tvoid nil) nil Q.
  Proof. intros. iIntros "[]". Qed.

  Lemma wp_trap : forall Q,
      False |-- wp_builtin Bin_trap (Tfunction Tvoid nil) nil Q.
  Proof. intros. iIntros "[]". Qed.

  Axiom wp_expect : forall exp c Q,
      Q exp |-- wp_builtin Bin_expect (Tfunction Ti64 (Ti64 :: Ti64 :: nil)) (exp :: c :: nil) Q.

  (** Bit computations
   *)

  (* Returns one plus the index of the least significant 1-bit of x,
     or if x is zero, returns zero. *)
  Definition ffs_spec (sz : bitsize) (n : Z) (Q : val -> mpred) : mpred :=
    [| has_type (Vint n) (Tnum sz Signed) |] ** Q (Vint (first_set sz n)).

  Axiom wp_ffs : forall sz c Q,
          ffs_spec sz c Q
      |-- wp_builtin Bin_ffs (Tfunction (Tnum sz Signed) (Tnum sz Signed :: nil)) (Vint c :: nil) Q.

  Axiom wp_ffsl : forall sz c Q,
          ffs_spec sz c Q
      |-- wp_builtin Bin_ffsl (Tfunction (Tnum sz Signed) (Tnum sz Signed :: nil)) (Vint c :: nil) Q.

  Axiom wp_ffsll : forall sz c Q,
          ffs_spec sz c Q
      |-- wp_builtin Bin_ffsll (Tfunction (Tnum sz Signed) (Tnum sz Signed :: nil)) (Vint c :: nil) Q.

  (* Returns the number of trailing 0-bits in x, starting at the least
     significant bit position. If x is 0, the result is undefined. *)


  Definition ctz_spec (sz : bitsize) (n : Z) (Q : val -> mpred) : mpred :=
    [| has_type (Vint n) (Tnum sz Unsigned) |] ** [| n <> 0 |] ** Q (Vint (trailing_zeros sz n)).

  Axiom wp_ctz : forall sz c Q,
          ctz_spec sz c Q
      |-- wp_builtin Bin_ctz (Tfunction (Tnum sz Unsigned) (Tnum sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_ctzl : forall sz c Q,
          ctz_spec sz c Q
      |-- wp_builtin Bin_ctzl (Tfunction (Tnum sz Unsigned) (Tnum sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_ctzll : forall sz c Q,
          ctz_spec sz c Q
      |-- wp_builtin Bin_ctzll (Tfunction (Tnum sz Unsigned) (Tnum sz Unsigned :: nil)) (Vint c :: nil) Q.

  (* Returns the number of leading 0-bits in x, starting at the most significant
     bit position. If x is 0, the result is undefined. *)
  Definition clz_spec (sz : bitsize) (n : Z) (Q : val -> mpred) : mpred :=
    [| has_type (Vint n) (Tnum sz Unsigned) |] ** [| n <> 0 |] ** Q (Vint (leading_zeros sz n)).

  Axiom wp_clz : forall sz c Q,
          clz_spec sz c Q
      |-- wp_builtin Bin_clz (Tfunction (Tnum sz Unsigned) (Tnum sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_clzl : forall sz c Q,
          clz_spec sz c Q
      |-- wp_builtin Bin_clzl (Tfunction (Tnum sz Unsigned) (Tnum sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_clzll : forall sz c Q,
          clz_spec sz c Q
      |-- wp_builtin Bin_clzll (Tfunction (Tnum sz Unsigned) (Tnum sz Unsigned :: nil)) (Vint c :: nil) Q.

  (* Returns x with the order of the bytes reversed; for example, 0xaabb becomes
     0xbbaa. Byte here always means exactly 8 bits. *)
  Axiom wp_bswap16 : forall x Q,
          [| has_type (Vint x) Tu16 |] ** Q (Vint (bswap W16 x))
      |-- wp_builtin Bin_bswap16 (Tfunction Tu16 (Tu16 :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap32 : forall x Q,
          [| has_type (Vint x) Tu32 |] ** Q (Vint (bswap W32 x))
      |-- wp_builtin Bin_bswap32 (Tfunction Tu32 (Tu32 :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap64 : forall x Q,
          [| has_type (Vint x) Tu64 |] ** Q (Vint (bswap W64 x))
      |-- wp_builtin Bin_bswap64 (Tfunction Tu64 (Tu64 :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap128 : forall x Q,
          [| has_type (Vint x) Tu128 |] ** Q (Vint (bswap W128 x))
      |-- wp_builtin Bin_bswap128 (Tfunction Tu128 (Tu128 :: nil))
          (Vint x :: nil) Q.


  (** std::launder (http://eel.is/c++draft/ptr.launder) *)
  Axiom wp_launder : forall ty res newp Q,
      provides_storage res newp ty ** (provides_storage res newp ty -* Q (Vptr newp))
      |-- wp_builtin Bin_launder (Tfunction (Tptr Tvoid) (Tptr Tvoid :: nil))
          (Vptr res :: nil) Q.

End with_Σ.
