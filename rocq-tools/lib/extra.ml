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

type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

let panic : ('a, 'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter
    ("\027[31m[Panic] " ^^ fmt ^^ "\027[0m\n%!")

let failwith : ?fail:(string -> 'b) -> ('a, 'b) koutfmt -> 'a =
    fun ?(fail=Stdlib.failwith) fmt ->
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  let k _ =
    Format.pp_print_flush ff ();
    fail (Buffer.contents buf)
  in
  Format.kfprintf k ff fmt
