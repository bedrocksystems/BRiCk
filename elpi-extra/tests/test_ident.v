(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From bedrock_tests.elpi.extra Extra Dependency "test.elpi" as test.
Require Import bedrock.ltac2.extra.extra.
Require Import bedrock.elpi.extra.extra.

Elpi Program test lp:{{ }}.
Elpi Accumulate Db extra.Program.
Elpi Accumulate File test.

Definition cats : Ident.rep := Ident.Rep (fun cats => tt).

Fail Elpi Query lp:{{ check "dogs" { ident.of_rep {{ cats }} } }}.	(* <<check>> can fail *)
Succeed Elpi Query lp:{{ det (ident.of_rep {{ cats }} Id), check "cats" Id }}.
Succeed Elpi Query lp:{{ det (ident.as_rep "dogs" T), check {{ Ident.Rep (fun dogs : unit => tt) }} T }}.
Succeed Elpi Query lp:{{ check "dogs" { ident.of_rep { ident.as_rep "dogs" } } }}.

Fail Elpi Query lp:{{ ident.of_rep {{ Ident.Rep (fun _ : unit => tt) }} S }}.
Succeed Elpi Query lp:{{ det (ident.of_rep_opt {{ Ident.Rep (fun _ : unit => tt) }} O), check none O }}.
