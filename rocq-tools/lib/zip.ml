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

exception Error of string

let compress ~level input =
  let input_len = String.length input in
  let input_pos = ref 0 in
  let refill buf =
    let remaining = input_len - !input_pos in
    let n = min remaining (Bytes.length buf) in
    Bytes.blit_string input !input_pos buf 0 n;
    input_pos := !input_pos + n; n
  in
  let output = Buffer.create input_len in
  let flush buf n = Buffer.add_subbytes output buf 0 n in
  let _ =
    try Zlib.compress ~level ~header:false refill flush with
    | Zlib.Error(_,_) -> raise (Error("compression failed"))
  in
  Buffer.contents output

let decompress input =
  let input_len = String.length input in
  let input_pos = ref 0 in
  let refill buf =
    let remaining = input_len - !input_pos in
    let n = min remaining (Bytes.length buf) in
    Bytes.blit_string input !input_pos buf 0 n;
    input_pos := !input_pos + n; n
  in
  let output = Buffer.create input_len in
  let flush buf n = Buffer.add_subbytes output buf 0 n in
  let _ =
    try Zlib.uncompress ~header:false refill flush with
    | Zlib.Error(_,_) -> raise (Error("decompression failed"))
  in
  Buffer.contents output
