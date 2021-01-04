(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.operator.

Local Open Scope Z_scope.
(* see
 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
 *)

(* Returns one plus the index of the least significant 1-bit of x,
   or if x is zero, returns zero. *)
Definition first_set (sz : bitsize) (n : Z) : Z :=
  let n := trim (bitsN sz) n in
  if Z.eqb n 0 then 0
  else
    (fix get ls : Z :=
       match ls with
       | nil => 64
       | l :: ls =>
         if Z.testbit n l
         then 1 + l
         else get ls
       end)%Z (List.map Z.of_nat (seq 0 (N.to_nat (bitsN sz)))).

(* Returns the number of trailing 0-bits in x, starting at the least
   significant bit position. If x is 0, the result is undefined. *)
Definition trailing_zeros (sz : bitsize) (n : Z) : Z :=
  (fix get ls : Z :=
     match ls with
     | nil => 64
     | l :: ls =>
       if Z.testbit n l
       then l
       else get ls
     end)%Z (List.map Z.of_nat (seq 0 (N.to_nat (bitsN sz)))).

(* Returns the number of leading 0-bits in x, starting at the most significant
   bit position. If x is 0, the result is undefined. *)
Definition leading_zeros (sz : bitsize) (l : Z) : Z :=
  bitsZ sz - Z.log2 (l mod (2^64)).


Local Definition bswap16 (n : Z) : Z :=
  Z.lor (Z.shiftl (Z.land n 255) 8) (Z.land (Z.shiftr n 8) 255).
Local Definition bswap32 (n : Z) : Z :=
  let low := bswap16 n in
  let high := bswap16 (Z.shiftr n 16) in
  Z.lor (Z.shiftl low 16) high.
Local Definition bswap64 (n : Z) : Z :=
  let low := bswap32 n in
  let high := bswap32 (Z.shiftr n 32) in
  Z.lor (Z.shiftl low 32) high.
Local Definition bswap128 (n : Z) : Z :=
  let low := bswap64 n in
  let high := bswap64 (Z.shiftr n 64) in
  Z.lor (Z.shiftl low 64) high.

Definition bswap (sz : bitsize) : Z -> Z :=
  match sz with
  | W8 => id
  | W16 => bswap16
  | W32 => bswap32
  | W64 => bswap64
  | W128 => bswap128
  end.

Local Definition bytes (ls : list Z) :=
  fold_left (fun a b => a * 256 + b)%Z ls 0%Z.
Arguments bytes _%Z.

Local Definition _bswap16_test : bswap W16 (bytes (1::2::nil)%Z) = bytes (2::1::nil)%Z := eq_refl.
Local Definition _bswap32_test :
  bswap W32 (bytes (1::2::3::4::nil)%Z) = bytes (4::3::2::1::nil)%Z := eq_refl.
Local Definition _bswap64_test :
  bswap W64 (bytes (1::2::3::4::5::6::7::8::nil)%Z) = bytes (8::7::6::5::4::3::2::1::nil)%Z := eq_refl.
