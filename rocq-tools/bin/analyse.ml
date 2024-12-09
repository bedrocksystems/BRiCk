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
  panic "Usage: %s INFILE [OUTFILE]" Sys.argv.(0)

let (ifile, ofile) =
  match Sys.argv with
  | [|_; ifile; ofile|] -> (ifile, Some(ofile))
  | [|_; ifile       |] -> (ifile, None       )
  | _                   -> usage ()

(* Reading the input JSON. *)
let json : JSON.t =
  try Yojson.Basic.from_file ifile with
  | Yojson.Json_error(msg) ->
      panic "Parse error (expecting JSON data). %s" msg
  | Sys_error(msg) ->
      panic "Error: %s" msg

(* Interprete the JSON input as profiling data. *)
let data =
  try Profile.extract json with
  | Profile.Error(msg) -> panic "Ill-formed input: %s." msg
  | Profile.NoInstr    -> panic "No instruction counts in profile."

(* Write the data in JSON format. *)
let _ =
  let data = Data.to_json data in
  try
    match ofile with
    | None        -> Yojson.Basic.to_channel stdout data
    | Some(ofile) -> Yojson.Basic.to_file ofile data
  with
  | Sys_error(msg) -> panic "Error: %s" msg
