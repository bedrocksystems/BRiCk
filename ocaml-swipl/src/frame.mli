(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

type frame_terminator = Close | Discard

(** [with_frame f] TODO
    - the function [f] should not leak prolog values created in its body.
    - no way to rewind for now. *)
val with_frame : (unit -> frame_terminator) -> unit

val with_closed_frame : (unit -> unit) -> unit

val with_discarded_frame : (unit -> unit) -> unit
