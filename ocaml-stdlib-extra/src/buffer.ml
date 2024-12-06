(*
 * Copyright (C) BlueRock Security Inc. 2021-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

include Stdlib.Buffer

let iter : (char -> unit) -> t -> unit = fun f buf ->
  Seq.iter f (to_seq buf)

let iter_lines : (string -> unit) -> t -> unit = fun f buf ->
  let b = create 2048 in
  let handle_char c =
    match c with
    | '\n' -> f (contents b); clear b
    | _    -> add_char b c
  in
  iter handle_char buf;
  if length b <> 0 then f (contents b)

let is_empty : t -> bool = fun b ->
  try ignore (nth b 0); false with Invalid_argument(_) -> true
