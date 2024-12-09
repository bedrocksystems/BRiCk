(*
 * Copyright (C) 2023-2024 BlueRock Security Inc.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; version 2.1.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *)

(** Short name for a standard formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [panic fmt ...] aborts the program with the given message, specified using
    a format string and arguments similar to [Format.fprintf]. A newline and a
    flush instructions are automatically added to the message. *)
val panic : ('a, 'b) koutfmt -> 'a

(** [failwith ~fail fmt] is equivalent to calling [fail msg] (or, if [fail] is
    not given, [Stdlib.failwith msg]), where [msg] is an error message that is
    specified using a format string and arguments similar to [Format.fprintf].
    Warning: [fail] is only called once the function is fully applied. *)
val failwith : ?fail:(string -> 'b) -> ('a, 'b) koutfmt -> 'a
