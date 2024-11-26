(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Make the plugin available downstream *)

Require Export elpi.elpi.

(**
Make warnings from, e.g., <<Elpi Typecheck>> fatal. Elpi lazily
registers the warning with Coq, hence the run-around.
*)

#[local] Set Warnings "+unknown-warning".
Fail #[export] Set Warnings "+elpi.typecheck".
Module Type ELPI_TYPECHECK_WARNING.
  Elpi Program register_warning lp:{{ }}.
  #[warnings="-elpi.typecheck"]	(* silence this warning *)
  Elpi Query lp:{{ coq.warning "elpi" "elpi.typecheck" _L _M }}.
End ELPI_TYPECHECK_WARNING.
#[global] Set Warnings "+elpi.typecheck".	(* promote future warnings *)
