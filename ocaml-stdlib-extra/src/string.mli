(*
 * Copyright (C) BlueRock Security Inc. 2021-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Extension of [Stdlib.String]. *)

include module type of Stdlib.String

(** [take i s] returns a string containing the first [i] characters of [s]. If
    [i] is less than [0], or if [s] has less than [i] elements,  the exception
    [Invalid_argument("String.take")] is raised. *)
val take : int -> string -> string

(** [drop i s] returns a copy of [s] with its first [i] characters removed. If
    [i] is less than [0], or if [s] has less than [i] elements,  the exception
    [Invalid_argument("String.drop")] is raised. *)
val drop : int -> string -> string

(** [of_char_list cs] converts a list of characters into a string. *)
val of_char_list : char list -> string
