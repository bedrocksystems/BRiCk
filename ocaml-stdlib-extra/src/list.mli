(*
 * Copyright (C) BlueRock Security Inc. 2021-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Extension of [Stdlib.List]. *)

open Prelude

include module type of Stdlib.List

(** [is_empty l] indicates whether list [l] is empty. *)
val is_empty : 'a list -> bool

(** [drop_while p l] returns the longest suffix of list [l] whose head,  if it
    has one, does not satisfy predicate [p]. *)
val drop_while : ('a -> bool) -> 'a list -> 'a list

(** [take_while p l] returns a pair containing the longest prefix of [l] whose
    elements satisfy predicate [p], and the corresponding suffix of [l] (if it
    is non-empty, its first element does not satisfy [p]).  *)
val take_while : ('a -> bool) -> 'a list -> 'a list * 'a list

(** [choose bs] takes as input a list of buckets [bs], and it generates a list
    of all the possible ways to pick one element from each bucket. *)
val choose : 'a list list -> 'a list list

(** [has_dups cmp l] indicates whether the list [l] has duplicates  (according
    to the comparison function [cmp]). *)
val has_dups : 'a compare -> 'a list -> bool

(** [exists_or_empty p l] is similar to [exists p l], but it returns [true] if
    the list [l] is empty. *)
val exists_or_empty : ('a -> bool) -> 'a list -> bool
