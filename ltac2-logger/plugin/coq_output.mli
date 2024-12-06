(*
 * Copyright (C) BlueRock Security Inc. 2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Type representing a buffer capturing Coq output. *)
type buffer

(** [start_capture ()] changes the buffers underlying the Coq output functions
    to record the output in the returned buffer. The previous state of the Coq
    buffers is saved, so that it can be restored by [end_capture]. *)
val start_capture : unit -> buffer

(** [contents buf] returns the current contents of buffer [buf]. *)
val contents : buffer -> string

(** [clear buf] clears the contents of buffer [buf]. *)
val clear : buffer -> unit

(** [end_capture buf] restores the buffers underlying the Coq output functions
    to their original state, prior to the call to [start_capture] that gave us
    [buf] in the first place. *)
val end_capture : buffer -> unit
