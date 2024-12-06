(*
 * Copyright (C) BlueRock Security Inc. 2021-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

type 'a compare = 'a -> 'a -> int

let failwith ?(fail=Stdlib.failwith) fmt =
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  let k _ =
    Format.pp_print_flush ff ();
    fail (Buffer.contents buf)
  in
  Format.kfprintf k ff fmt
