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

(** Type of a string encoded using Base 64 Encoding (RFC4648). *)
type t

(** [encode s] encodes [s] using Base 64 Encoding (RFC4648). *)
val encode : string -> t

(** [decode e] decodes [e] according to Base 64 Encoding (RFC4648). *)
val decode : t -> string

(** [of_string s] injects the string [s] into type [t], assuming it represents
    Base 64 Encoded data. If [s] contains invalid characters, or if it has the
    wrong length, [Invalid_argument] is raised. *)
val of_string : string -> t

(** [to_string e] injects [e] into the underlying string representation. *)
val to_string : t -> string
