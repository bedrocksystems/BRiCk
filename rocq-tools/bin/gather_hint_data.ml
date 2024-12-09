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

let gather_hint_data : In_channel.t -> Spandata.map = fun ic ->
  let map = ref Spandata.M.empty in
  let handle_file file =
    match Filename.extension file with
    | ".json" -> map := Spandata.add_log_file file !map
    | ".csv"  -> map := Spandata.add_csv_file file !map
    | _       -> panic "File %s does not have a json or csv extension." file
  in
  let rec loop () =
    match Option.map String.trim (In_channel.input_line ic) with
    | Some(""  ) -> loop ()
    | Some(file) -> handle_file file; loop ()
    | None       -> ()
  in
  loop (); !map

let _ =
  if Sys.word_size <> 64 then assert false;
  match List.tl (Array.to_list Sys.argv) with
  | o :: _ when List.mem o ["-h"; "--help"] ->
      Printf.printf "Usage: %s [-h | --help] < file_list\n%!" Sys.argv.(0)
  | o :: _ ->
      Printf.eprintf "Error: unknown command line opton %S\n%!" o;
      panic "Usage: %s [-h | --help] < file_list\n%!" Sys.argv.(0)
  | [] ->
      let map = gather_hint_data stdin in
      Printf.printf "%a%!" Spandata.output_csv map
