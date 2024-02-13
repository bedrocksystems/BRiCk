(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.lang.proofmode.proofmode.
Require Import bedrock.lang.bi.ChargeCompat.
Require Import bedrock.lang.bi.errors.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.arith.builtins.
Require Import bedrock.lang.cpp.logic.pred.
Require Import bedrock.lang.cpp.logic.path_pred.
Require Import bedrock.lang.cpp.logic.heap_pred.
Require Import bedrock.lang.cpp.logic.wp.

#[local] Arguments ERROR {_ _} _%_bs : assert.

(** ** Wp Semantics for builtins *)
(**
NOTE: we use a non-standard calling convention where values are passed
as if they were all evaluated using [wp_operand].
*)
Parameter wp_builtin : ∀ `{Σ : cpp_logic, σ : genv}
    (b : BuiltinFn) (fty : functype) (** the type of the builtin *)
    (args : list val) (Q : val -> epred), mpred.

Section wp_builtin.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : val -> epred).

  Axiom wp_builtin_frame : ∀ b fty args Q Q',
    Forall v, Q v -* Q' v
    |-- wp_builtin b fty args Q -* wp_builtin b fty args Q'.

  Axiom wp_builtin_shift : ∀ b fty args Q,
    (|={top}=> wp_builtin b fty args (fun v => |={top}=> Q v))
    |-- wp_builtin b fty args Q.

  #[local] Notation PROPER R := (
    ∀ b fty args,
    Proper (pointwise_relation _ R ==> R) (wp_builtin b fty args)
  ) (only parsing).
  #[global] Instance: Params (@wp_builtin) 6 := {}.
  #[global] Instance wp_builtin_mono : PROPER bi_entails.
  Proof.
    intros * Q1 Q2 HQ.
    iApply wp_builtin_frame. iIntros (?).
    by iApply HQ.
  Qed.
  #[global] Instance wp_builtin_flip_mono : PROPER (flip bi_entails).
  Proof. repeat intro. exact: wp_builtin_mono. Qed.
  #[global] Instance wp_builtin_proper : PROPER equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply: wp_builtin_mono=>?; rewrite HQ. Qed.

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
  Definition ffs_spec (sz : bitsize) (n : Z) (Q : val -> epred) : mpred :=
    [| has_type_prop (Vint n) (Tnum sz Signed) |] ** Q (Vint (first_set sz n)).

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


  Definition ctz_spec (sz : bitsize) (n : Z) (Q : val -> epred) : mpred :=
    [| has_type_prop (Vint n) (Tnum sz Unsigned) |] ** [| n <> 0 |] ** Q (Vint (trailing_zeros sz n)).

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
  Definition clz_spec (sz : bitsize) (n : Z) (Q : val -> epred) : mpred :=
    [| has_type_prop (Vint n) (Tnum sz Unsigned) |] ** [| n <> 0 |] ** Q (Vint (leading_zeros sz n)).

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
          [| has_type_prop (Vint x) Tu16 |] ** Q (Vint (bswap W16 x))
      |-- wp_builtin Bin_bswap16 (Tfunction Tu16 (Tu16 :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap32 : forall x Q,
          [| has_type_prop (Vint x) Tu32 |] ** Q (Vint (bswap W32 x))
      |-- wp_builtin Bin_bswap32 (Tfunction Tu32 (Tu32 :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap64 : forall x Q,
          [| has_type_prop (Vint x) Tu64 |] ** Q (Vint (bswap W64 x))
      |-- wp_builtin Bin_bswap64 (Tfunction Tu64 (Tu64 :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap128 : forall x Q,
          [| has_type_prop (Vint x) Tu128 |] ** Q (Vint (bswap W128 x))
      |-- wp_builtin Bin_bswap128 (Tfunction Tu128 (Tu128 :: nil))
          (Vint x :: nil) Q.


  (** std::launder (http://eel.is/c++draft/ptr.launder) *)
  Axiom wp_launder : forall ty res newp Q,
      provides_storage res newp ty ** (provides_storage res newp ty -* Q (Vptr newp))
      |-- wp_builtin Bin_launder (Tfunction (Tptr Tvoid) (Tptr Tvoid :: nil))
          (Vptr res :: nil) Q.

End wp_builtin.

(** ** Endianness *)
(**
TODO: Justify these things being in this file, or move them where they
belong.
*)
Section endian_conversion.
  Context `{Σ : cpp_logic} {σ : genv}.

  Definition to_big_end (sz : bitsize) : Z -> Z :=
    match genv_byte_order σ with
    | Little => bswap sz
    | Big => fun x => x
    end.

  Definition to_little_end (sz : bitsize) : Z -> Z :=
    match genv_byte_order σ with
    | Big => bswap sz
    | Little => fun x => x
    end.

  Definition to_end (endianness: endian) (sz: bitsize) : Z -> Z :=
    match endianness with
    | Big    => to_big_end sz
    | Little => to_little_end sz
    end.

  Definition of_big_end := @to_big_end.
  (** move to builtins.v *)
  Definition of_little_end := @to_little_end.
  (** move to builtins.v *)
  Definition of_end := @to_end.

End endian_conversion.

(** ** Builtin functions *)

Definition read_args `{Σ : cpp_logic, σ : genv} :=
  fix read_args (targs : list decltype) (ls : list ptr) (Q : list val -> epred) : mpred :=
  match targs , ls with
  | nil , nil => Q nil
  | t :: ts , p :: ps =>
    Exists v, (Exists q, p |-> primR t q v ** True) //\\
    read_args ts ps (fun vs => Q (v :: vs))
  | _ , _ => ERROR "read_args"
  end.
#[global] Hint Opaque read_args : typeclass_instances.

Section with_Σ.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : list val -> epred).

  Lemma read_args_frame targs args Q Q' :
    Forall vs, Q vs -* Q' vs
    |-- read_args targs args Q -* read_args targs args Q'.
  Proof.
    move: Q Q' args. induction targs; intros; destruct args; cbn; auto.
    { iIntros "HQ ?". by iApply "HQ". }
    { iIntros "HQ (%v & A)". iExists v.
      iSplit; [by iDestruct "A" as "[$ _]" | iDestruct "A" as "[_ A]"].
      iApply (IHtargs with "[HQ] A"). iIntros (?) "?".
      by iApply "HQ". }
  Qed.

  #[local] Notation PROPER R := (
    ∀ targs args,
    Proper (pointwise_relation _ R ==> R) (read_args targs args)
  ) (only parsing).
  #[global] Instance: Params (@read_args) 5 := {}.
  #[global] Instance read_args_mono : PROPER bi_entails.
  Proof.
    intros * Q1 Q2 HQ.
    iApply read_args_frame. iIntros (?).
    by iApply HQ.
  Qed.
  #[global] Instance read_args_flip_mono : PROPER (flip bi_entails).
  Proof. repeat intro. exact: read_args_mono. Qed.
  #[global] Instance read_args_proper : PROPER equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply: read_args_mono=>?; rewrite HQ. Qed.
End with_Σ.

(**
[wp_builtin_func b fty args Q] captures the semantics of applying
builtin [b] with type [fty] to arguments [args] in the standard
calling convention.
*)
#[local]
Definition wp_builtin_func' `{Σ : cpp_logic, σ : genv} (u : bool)
    (b : BuiltinFn) (fty : functype) (args : list ptr) (Q : ptr -> epred) : mpred :=
  |={top}=>?u
  match fty with
  | Tfunction rty targs =>
    let* vs := read_args targs args in
    let* v := wp_builtin b fty vs in
    Forall p : ptr, p |-> primR rty (cQp.mut 1) v -* |={top}=>?u Q p
  | _ => ERROR "wp_builtin_func"
  end.
Definition wp_builtin_func `{Σ : cpp_logic, σ : genv} :=
  Cbn (Reduce (wp_builtin_func' true)).
#[global] Hint Opaque wp_builtin_func : typeclass_instances.

Section with_Σ.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : ptr -> epred).

  Lemma wp_builtin_func_frame b fty args Q Q' :
    Forall p, Q p -* Q' p
    |-- wp_builtin_func b fty args Q -* wp_builtin_func b fty args Q'.
  Proof.
    rewrite /wp_builtin_func. iIntros "HQ >wp !>".
    destruct fty; try by rewrite {1}ERROR_elim.
    iApply (read_args_frame with "[HQ] wp"). iIntros (?).
    iApply wp_builtin_frame.  iIntros "% HR % R".
    iApply "HQ". by iApply "HR".
  Qed.

  #[local] Notation PROPER R := (
    ∀ b fty args,
    Proper (pointwise_relation _ R ==> R) (wp_builtin_func b fty args)
  ) (only parsing).
  #[global] Instance: Params (@wp_builtin_func) 6 := {}.
  #[global] Instance wp_builtin_func_mono : PROPER bi_entails.
  Proof.
    intros * Q1 Q2 HQ.
    iApply wp_builtin_func_frame. iIntros (?).
    by iApply HQ.
  Qed.
  #[global] Instance wp_builtin_func_flip_mono : PROPER (flip bi_entails).
  Proof. repeat intro. exact: wp_builtin_func_mono. Qed.
  #[global] Instance wp_builtin_func_proper : PROPER equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply: wp_builtin_func_mono=>?; rewrite HQ. Qed.

  Lemma wp_builtin_func_shift b fty args Q :
    (|={top}=> wp_builtin_func b fty args (fun p => |={top}=> Q p))
    |-- wp_builtin_func b fty args Q.
  Proof.
    rewrite /wp_builtin_func. iIntros ">>wp !>".
    destruct fty; try by rewrite {1}ERROR_elim.
    iApply (read_args_frame with "[] wp"). iIntros (?).
    iApply wp_builtin_frame.  iIntros "% HR % R".
    by iMod ("HR" with "R").
  Qed.

  Lemma wp_builtin_func_intro b fty args Q :
    Cbn (Reduce (wp_builtin_func' false b fty args Q))
    |-- wp_builtin_func b fty args Q.
  Proof.
    rewrite /wp_builtin_func. destruct fty; auto. rewrite -fupd_intro.
    iApply read_args_frame. iIntros (?).
    iApply wp_builtin_frame. iIntros "% HQ % ? !>". by iApply "HQ".
  Qed.

  Lemma wp_builtin_func_elim b fty args Q :
    wp_builtin_func b fty args Q
    |-- Cbn (Reduce (wp_builtin_func' true b fty args Q)).
  Proof. done. Qed.
End with_Σ.
