(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From Cpp Require Import
     Auto.

Definition Vchar (a : Ascii.ascii) : val :=
  Vint (Z.of_N (N_of_ascii a)).

Definition T_char := Tchar (Some 8)%nat true.

(* representation of c-style strings, i.e. null-terminated *)
Fixpoint c_string (p : val) (ls : string) : mpred :=
  match ls with
  | EmptyString => tptsto T_char p (Vchar "000"%char)
  | String c cs =>
    tptsto T_char p (Vchar c) **
    c_string (offset_ptr p 1) cs
  end.

Section array.
  Context {T : Type}.
  Variable sz : Z.
  Variable (P : val -> T -> mpred).
  Fixpoint array' (p : val) (ls : list T) : mpred :=
    match ls with
    | nil => empSP
    | l :: ls =>
      P p l ** array' (offset_ptr p sz) ls
    end.
End array.

(* typed arrays *)
Definition tarray (t : type) {T : Type} (P : val -> T -> mpred)
           (base : val) (ls : list T) : mpred :=
  Exists sz, with_genv (fun g => [| @size_of g t sz |]) **
             array' sz P base ls.

Lemma array'_split : forall T sz P m base i,
    @array' T sz P base (firstn i m) **
    @array' T sz P (offset_ptr base (Z.of_nat i * sz)) (skipn i m) (* sz is problematic *)
    -|- @array' T sz P base m.
Proof.
  induction m; destruct i; simpl.
  { split; work. }
  { split; work. }
  { rewrite offset_ptr_0. split; work. }
  { rewrite <- (IHm (offset_ptr base sz) i); clear IHm.
    cutrewrite (offset_ptr base
       match sz with
       | 0 => 0
       | Z.pos y' => Z.pos (Pos.of_succ_nat i * y')
       | Z.neg y' => Z.neg (Pos.of_succ_nat i * y')
       end = offset_ptr (offset_ptr base sz) (Z.of_nat i * sz)).
    { split; work. }
    rewrite offset_ptr_combine.
    f_equal.
    change (Z.of_nat (S i) * sz = sz + Z.of_nat i * sz).
    lia. }
Qed.

Lemma tarray_split : forall ty T P base m i sz,
    @tarray ty T P base (firstn i m) **
    @tarray ty T P (offset_ptr base sz) (skipn i m) (* sz is problematic *)
    -|- @tarray ty T P base m.
Proof. Admitted.

Lemma tarray_first : forall ty T P base ms sz,
    (length ms > 0)%nat ->
    Exists m, Exists ms',
      P base m ** @tarray ty T P (offset_ptr base sz) ms' **
      [| ms = m :: ms' |]
    -|- @tarray ty T P base ms.
Proof. Admitted.

Lemma tarray_cell : forall resolve {T} (P : val -> T -> mpred) ty base ms i m sz,
    size_of (c:=resolve) ty sz ->
    nth_error ms i = Some m ->
    tarray ty P base ms -|-
           tarray ty P base (firstn i ms) **
           P (offset_ptr base (Z.of_nat i * sz)) m **
           tarray ty P base (skipn (S i) ms).
Admitted.