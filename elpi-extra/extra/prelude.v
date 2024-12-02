(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Make the plugin available downstream *)

Require Export elpi.elpi.

(**
Make warnings from, e.g., <<Elpi Typecheck>> fatal.
*)
#[global] Set Warnings "+elpi.typecheck".	(* promote future warnings *)
