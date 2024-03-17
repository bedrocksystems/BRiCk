(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.prelude.
Require Import bedrock.lang.cpp.syntax.types.

Notation T := (Tnum (lang:=lang.cpp) W32 Signed).
Notation C := (tqualified (lang:=lang.cpp) QC) (only parsing).
Notation V := (tqualified (lang:=lang.cpp) QV) (only parsing).
Notation L := (tref (lang:=lang.cpp) QM) (only parsing).
Notation R := (trv_ref (lang:=lang.cpp) QM) (only parsing).

(** qualified reference types (via [tqualified]) *)
Goal C $ Tref T = Tref T. Proof. done. Qed.
Goal C $ Trv_ref T = Trv_ref T. Proof. done. Qed.

(** nested qualifiers (via [tqualified]) *)
Goal C $ V $ C $ V $ T = Tqualified QCV T. Proof. done. Qed.

(** stripping qualifiers on reference types *)
Goal C $ L $ C $ L T = Tref T. Proof. done. Qed.
Goal C $ R $ C $ L T = Tref T. Proof. done. Qed.
Goal C $ L $ C $ R T = Tref T. Proof. done. Qed.
Goal C $ R $ C $ R T = Trv_ref T. Proof. done. Qed.

(** preserving and collapsing qualifiers on reference target types *)
Goal C $ L $ C $ R $ C T = Tref (Tqualified QC T). Proof. done. Qed.
Goal C $ L $ C $ R $ C $ V $ C $ V T = Tref (Tqualified QCV T). Proof. done. Qed.
