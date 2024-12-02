(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import bedrock.elpi.extra.NES.

Elpi Command test.
#[phase="both"] Elpi Accumulate Db NES.db.
#[phase="both"] Elpi Accumulate File bedrock.elpi.extra.NES.code.
