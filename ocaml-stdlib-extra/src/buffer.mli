(*
 * Copyright (C) BlueRock Security Inc. 2021-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Extension of [Stdlib.Buffer]. *)

include module type of Stdlib.Buffer

(** [iter f b] calls [f] on each character of buffer [b] in order. In the case
    where [f] modifies [b] while iterating, the behaviour is unspecified. *)
val iter : (char -> unit) -> t -> unit

(** [iter_lines f b] calls [f] on every line of [b] (delimited by ['\n']). The
    trailing newline is not included when calling [f]. As for [iter], function
    [f] should not modify [b] while iterating. *)
val iter_lines : (string -> unit) -> t -> unit

(** [is_empty b] indicates whether the buffer [b] is empty. *)
val is_empty : t -> bool
