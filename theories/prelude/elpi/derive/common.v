(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(* This file is a wrapper around [elpi.apps.derive] that doesn't have the side
   effect of setting [Uniform Inductive Parameters]. *)

Require Export elpi.apps.derive.
#[global] Unset Uniform Inductive Parameters.

(* Patch for the driver of the derive command. *)
Elpi Accumulate derive lp:{{
  derivation (const C) Prefix HasSynterp D :-
    coq.env.const C (some (global T)) Ty_,
    derivation T Prefix HasSynterp D.
}}.
Elpi Typecheck derive.
