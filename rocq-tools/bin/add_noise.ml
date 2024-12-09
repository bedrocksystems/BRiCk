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

open Rocq_tools
open Rocq_tools.Extra

let usage () =
  panic "Usage: %s [FLOAT] INFILE OUTFILE" Sys.argv.(0)

let (p, ifile, ofile) =
  match Sys.argv with
  | [|_; p; ifile; ofile|] -> (p     , ifile, ofile)
  | [|_;    ifile; ofile|] -> ("0.05", ifile, ofile)
  | _                      -> usage ()
 
let _ =
  try
    let p = Float.of_string p in
    let data = Data.read_json ifile in
    let data = Data.add_noise p data in
    Data.write_json ofile data
  with
  | Sys_error(s)       -> panic "Error: %s" s
  | Data.Read_error(s) -> panic "Error: %s" s
  | Failure(s)         -> panic "Error: %s" s

