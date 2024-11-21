(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import bedrock.elpi.extra.extra.

Elpi Tactic test.
#[interp] Elpi Accumulate File extra.Tactic.
(** Avoid an anomaly --- see tc_tactic_synterp.DISABLED *)
From bedrock.elpi.extra.Tactic Extra Dependency "synterp.elpi" as extra_synterp.
#[synterp] Elpi Accumulate File extra_synterp.
