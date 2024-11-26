(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import bedrock.elpi.extra.extra.

Elpi Program test lp:{{ }}.
#[phase="both"] Elpi Accumulate Db extra.Program.
Elpi Typecheck.