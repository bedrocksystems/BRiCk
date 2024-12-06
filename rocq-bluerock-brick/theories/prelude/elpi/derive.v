(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** This file exports BedRock derive extensions. *)

(* WARNING: importing [elpi.apps.derive] has the side effect of setting
   [Uniform Inductive Parameters], so each individual extension should
   instead use [bedrock.prelude.elpi.derive.common]. *)

Require Export bedrock.prelude.elpi.derive.eq_dec.
(*Test Uniform Inductive Parameters.*)
Require Export bedrock.prelude.elpi.derive.inhabited.
(*Test Uniform Inductive Parameters.*)
Require Export bedrock.prelude.elpi.derive.finite.
(*Test Uniform Inductive Parameters.*)
Require Export bedrock.prelude.elpi.derive.countable.
(*Test Uniform Inductive Parameters.*)
Require Export bedrock.prelude.elpi.derive.finite_type.
(*Test Uniform Inductive Parameters.*)
Require Export bedrock.prelude.elpi.derive.bitset.
(*Test Uniform Inductive Parameters.*)
Require Export bedrock.prelude.elpi.derive.lens.
(*Test Uniform Inductive Parameters.*)
