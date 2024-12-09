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

(* Filters the input to remove lines forming mimimal segments such that:
   - the first line starts with: "Warning: cache store error",
   - a line ends with "after executing",
   - the last line ends with ")". *)

let _ =
  let ignore_cache_store_lines start_line =
    (* Wrapper around [input_line] to print all ignored lines upon error. *)
    let input_line : in_channel -> string =
      let lines = ref [start_line] in
      let input_line ic =
        let line =
          try input_line ic with End_of_file ->
            List.iter (Printf.printf "%s\n%!") (List.rev !lines);
            raise End_of_file
        in
        lines := line :: !lines; line
      in
      input_line
    in
    let found = ref false in
    while not !found do
      let line = input_line stdin in
      if String.ends_with ~suffix:"after executing" line then found := true
    done;
    let found = ref false in
    while not !found do
      let line = input_line stdin in
      if String.ends_with ~suffix:")" line then found := true
    done
  in
  try while true do
    let line = input_line stdin in
    if String.starts_with ~prefix:"Warning: cache store error" line then
      ignore_cache_store_lines line
    else
      Printf.printf "%s\n%!" line
  done with End_of_file -> ()
