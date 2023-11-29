(*
 * Copyright (C) BedRock Systems Inc. 2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
 * This file declares some Dbs for our developments.
 *)

(* [br_opacity] is a database for marking definitions opaque.
   It is intended to be extended by users of [Hint Opaque] entries.
 *)
Create HintDb br_opacity discriminated.

Create HintDb pure discriminated.
