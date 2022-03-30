(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.logic.

Notation "'boolR' q v" := (primR Tbool q (Vbool v)) (at level 10, q at level 1, v at level 1).

(* integers with implicit sizes *)
(* note(gmm): these might need to become definitions if we want to be generic
 * across sizes
 *)
Notation "'scharR' q v" := (primR (Tschar) q (Vint v)) (at level 10, q at level 1, v at level 1).
Notation "'ucharR' q v" := (primR (Tuchar) q (Vint v)) (at level 10, q at level 1, v at level 1).
Notation "'charR' q v" := (ucharR q v) (at level 10, q at level 1, v at level 1).

Notation "'sshortR' q v" := (primR (Tint W16 Signed) q (Vint v)) (only parsing, at level 10, q at level 1, v at level 1).
Notation "'ushortR' q v" := (primR (Tint W16 Unsigned) q (Vint v)) (only parsing, at level 10, q at level 1, v at level 1).
Notation "'shortR' q v" := (sshortR q v) (only parsing, at level 10, q at level 1, v at level 1).


Notation "'sintR' q v" := (primR (Tint int_bits Signed) q (Vint v)) (only parsing, at level 10, q at level 1, v at level 1).
Notation "'uintR' q v" := (primR (Tint int_bits Unsigned) q (Vint v)) (only parsing, at level 10, q at level 1, v at level 1).
Notation "'intR' q v" := (sintR q v) (only parsing, at level 10, q at level 1, v at level 1).

Notation "'slongR' q v" := (primR (Tint long_bits Signed) q (Vint v)) (only parsing, at level 10, q at level 1, v at level 1).
Notation "'ulongR' q v" := (primR (Tint long_bits Unsigned) q (Vint v)) (only parsing, at level 10, q at level 1, v at level 1).
Notation "'longR' q v" := (slongR q v) (only parsing, at level 10, q at level 1, v at level 1).

Notation "'slonglongR' q v" := (primR (Tint W64 Signed) q (Vint v)) (only parsing, at level 10, q at level 1, v at level 1).
Notation "'ulonglongR' q v" := (primR (Tint W64 Unsigned) q (Vint v)) (only parsing, at level 10, q at level 1, v at level 1).
Notation "'longlongR' q v" := (slonglongR q v) (only parsing, at level 10, q at level 1, v at level 1).

(* integers with explict sizes *)

Notation "'u8R'  q v" := (primR Tu8  q (Vint v)) (at level 10, q at level 1, v at level 1).
Notation "'u16R' q v" := (primR Tu16 q (Vint v)) (at level 10, q at level 1, v at level 1).
Notation "'u32R' q v" := (primR Tu32 q (Vint v)) (at level 10, q at level 1, v at level 1).
Notation "'u64R' q v" := (primR Tu64 q (Vint v)) (at level 10, q at level 1, v at level 1).

Notation "'i8R'  q v" := (primR Ti8  q (Vint v)) (at level 10, q at level 1, v at level 1).
Notation "'i16R' q v" := (primR Ti16 q (Vint v)) (at level 10, q at level 1, v at level 1).
Notation "'i32R' q v" := (primR Ti32 q (Vint v)) (at level 10, q at level 1, v at level 1).
Notation "'i64R' q v" := (primR Ti64 q (Vint v)) (at level 10, q at level 1, v at level 1).

#[deprecated(since="2022-04-1", note="use [u8R]")]
Notation "'uint8R' q v" := (ucharR q v) (only parsing, at level 10, q at level 1, v at level 1).
#[deprecated(since="2022-04-1", note="use [u16R]")]
Notation "'uint16R' q v" := (ushortR q v) (only parsing, at level 10, q at level 1, v at level 1).
#[deprecated(since="2022-04-1", note="use [u32R]")]
Notation "'uint32R' q v" := (uintR q v) (only parsing, at level 10, q at level 1, v at level 1).
#[deprecated(since="2022-04-1", note="use [u64R]")]
Notation "'uint64R' q v" := (ulonglongR q v) (only parsing, at level 10, q at level 1, v at level 1).

#[deprecated(since="2022-04-1", note="use [i8R]")]
Notation "'int8R' q v" := (scharR q v) (only parsing, at level 10, q at level 1, v at level 1).
#[deprecated(since="2022-04-1", note="use [i16R]")]
Notation "'int16R' q v" := (shortR q v) (only parsing, at level 10, q at level 1, v at level 1).
#[deprecated(since="2022-04-1", note="use [i32R]")]
Notation "'int32R' q v" := (intR q v) (only parsing, at level 10, q at level 1, v at level 1).
#[deprecated(since="2022-04-1", note="use [i64R]")]
Notation "'int64R' q v" := (longlongR q v) (only parsing, at level 10, q at level 1, v at level 1).


Notation "'ptrR<' ty '>' q p" := (primR (Tpointer ty) q (Vptr p)) (at level 10, ty at level 20, q at level 1, p at level 1, format "'ptrR<' ty '>'  q  p").

Notation "'refR<' ty '>' p" := (primR (Tref ty) (Vptr p)) (at level 10, ty at level 20, p at level 1, format "'refR<' ty '>'  p").
