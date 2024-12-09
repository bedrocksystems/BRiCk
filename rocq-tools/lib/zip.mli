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

(** Exception raised on compression/decompression error. *)
exception Error of string

(** [compress ~level input] returns a compressed version of [input]. Note that
    the compression level can be controlled using the [level] integer. It must
    be between 0 (no compression) and 9 (highest level of compression). If the
    compression fails, exception [Error] is raised. *)
val compress : level:int -> string -> string

(** [decompress ~level input] returns a decompressed version of [input]. If an
    error occurs, exception [Error] is raised. *)
val decompress : string -> string
