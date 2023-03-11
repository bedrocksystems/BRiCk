(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.logic.

Notation boolR q v := (primR Tbool q (Vbool v)).

(* integers with explict sizes *)

Notation u8R  q v := (primR Tu8  q (Vint v)).
Notation u16R q v := (primR Tu16 q (Vint v)).
Notation u32R q v := (primR Tu32 q (Vint v)).
Notation u64R q v := (primR Tu64 q (Vint v)).

Notation i8R  q v := (primR Ti8  q (Vint v)).
Notation i16R q v := (primR Ti16 q (Vint v)).
Notation i32R q v := (primR Ti32 q (Vint v)).
Notation i64R q v := (primR Ti64 q (Vint v)).

(* integers with implicit sizes *)
(* note(gmm): these might need to become definitions if we want to be generic
 * across sizes
 *)
Notation scharR q v := (i8R q v) (only parsing).
Notation ucharR q v := (u8R q v) (only parsing).

Notation sshortR q v := (i16R q v) (only parsing).
Notation ushortR q v := (u16R q v) (only parsing).
Notation shortR q v := (i16R q v) (only parsing).


Notation sintR q v := (i32R q v) (only parsing).
Notation uintR q v := (u32R q v) (only parsing).
Notation intR q v := (i32R q v) (only parsing).

Notation slongR q v := (i64R q v) (only parsing).
Notation ulongR q v := (u64R q v) (only parsing).
Notation longR q v := (i64R q v) (only parsing).

Notation slonglongR q v := (i64R q v) (only parsing).
Notation ulonglongR q v := (u64R q v) (only parsing).
Notation longlongR q v := (i64R q v) (only parsing).

(** Character notations *)
Notation charR q v := (primR Tchar q (Vchar v)).
Notation wcharR q v := (primR Twchar q (Vchar v)).
Notation char32R q v := (primR Tchar32 q (Vchar v)).
Notation char16R q v := (primR Tchar16 q (Vchar v)).
Notation char8R q v := (primR Tchar8 q (Vchar v)).

Notation "'ptrR<' ty '>' q p" := (primR (Tpointer ty) q (Vptr p)) (at level 10, ty at level 20, q at level 1, p at level 1, format "'ptrR<' ty '>'  q  p").

Notation "'refR<' ty '>' q p" := (primR (Tref ty) q (Vptr p)) (at level 10, ty at level 20, q at level 1, p at level 1, format "'refR<' ty '>'  q  p").
