(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** This file exports BedRock derive extensions. *)

(* WARNING: importing [elpi.apps.derive] has the side effect of setting
   [Uniform Inductive Parameters], so each individual extension should
   instead use [bedrock.prelude.elpi.derive.common]. *)

From bedrock.prelude.elpi.derive Require Export eq_dec.
(*Test Uniform Inductive Parameters.*)
From bedrock.prelude.elpi.derive Require Export inhabited.
(*Test Uniform Inductive Parameters.*)
From bedrock.prelude.elpi.derive Require Export finite.
(*Test Uniform Inductive Parameters.*)
From bedrock.prelude.elpi.derive Require Export countable.
(*Test Uniform Inductive Parameters.*)
From bedrock.prelude.elpi.derive Require Export finite_type.
(*Test Uniform Inductive Parameters.*)
From bedrock.prelude.elpi.derive Require Export bitset.
(*Test Uniform Inductive Parameters.*)
From bedrock.prelude.elpi.derive Require Export lens.
(*Test Uniform Inductive Parameters.*)
