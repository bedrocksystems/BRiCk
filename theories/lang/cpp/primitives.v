(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.logic.

Notation boolR q v := (primR Tbool q (Vbool v)).

(* integers with implicit sizes *)
(* note(gmm): these might need to become definitions if we want to be generic
 * across sizes
 *)
Notation scharR q v := (primR (Tschar) q (Vint v)).
Notation ucharR q v := (primR (Tuchar) q (Vint v)).
Notation charR q v := (ucharR q v).

Notation sshortR q v := (primR (Tint W16 Signed) q (Vint v)) (only parsing).
Notation ushortR q v := (primR (Tint W16 Unsigned) q (Vint v)) (only parsing).
Notation shortR q v := (sshortR q v) (only parsing).


Notation sintR q v := (primR (Tint int_bits Signed) q (Vint v)) (only parsing).
Notation uintR q v := (primR (Tint int_bits Unsigned) q (Vint v)) (only parsing).
Notation intR q v := (sintR q v) (only parsing).

Notation slongR q v := (primR (Tint long_bits Signed) q (Vint v)) (only parsing).
Notation ulongR q v := (primR (Tint long_bits Unsigned) q (Vint v)) (only parsing).
Notation longR q v := (slongR q v) (only parsing).

Notation slonglongR q v := (primR (Tint W64 Signed) q (Vint v)) (only parsing).
Notation ulonglongR q v := (primR (Tint W64 Unsigned) q (Vint v)) (only parsing).
Notation longlongR q v := (slonglongR q v) (only parsing).

(* integers with explict sizes *)

Notation u8R  q v := (primR Tu8  q (Vint v)).
Notation u16R q v := (primR Tu16 q (Vint v)).
Notation u32R q v := (primR Tu32 q (Vint v)).
Notation u64R q v := (primR Tu64 q (Vint v)).

Notation i8R  q v := (primR Ti8  q (Vint v)).
Notation i16R q v := (primR Ti16 q (Vint v)).
Notation i32R q v := (primR Ti32 q (Vint v)).
Notation i64R q v := (primR Ti64 q (Vint v)).

#[deprecated(since="2022-04-1", note="use [u8R]")]
Notation uint8R q v := (u8R q v) (only parsing).
#[deprecated(since="2022-04-1", note="use [u16R]")]
Notation uint16R q v := (u16R q v) (only parsing).
#[deprecated(since="2022-04-1", note="use [u32R]")]
Notation uint32R q v := (u32R q v) (only parsing).
#[deprecated(since="2022-04-1", note="use [u64R]")]
Notation uint64R q v := (u64R q v) (only parsing).

#[deprecated(since="2022-04-1", note="use [i8R]")]
Notation int8R q v := (i8R q v) (only parsing).
#[deprecated(since="2022-04-1", note="use [i16R]")]
Notation int16R q v := (i16R q v) (only parsing).
#[deprecated(since="2022-04-1", note="use [i32R]")]
Notation int32R q v := (i32R q v) (only parsing).
#[deprecated(since="2022-04-1", note="use [i64R]")]
Notation int64R q v := (i64R q v) (only parsing).


Notation "'ptrR<' ty '>' q p" := (primR (Tpointer ty) q (Vptr p)) (at level 10, ty at level 20, q at level 1, p at level 1, format "'ptrR<' ty '>'  q  p").

Notation "'refR<' ty '>' p" := (primR (Tref ty) (Vptr p)) (at level 10, ty at level 20, p at level 1, format "'refR<' ty '>'  p").
