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

type pos = {
  line : int; (* Line number.  *)
  c0   : int; (* Start column. *)
  c1   : int; (* End column.   *)
}

let dummy_pos : pos = {line = 0; c0 = -1; c1 = -1}

type warning = {
  w_file : string;     (* File where the warning originated.     *)
  w_pos  : pos option; (* Optional warning position in the file. *)
  w_name : string;     (* Name for the warning.                  *)
  w_text : string;     (* Text from the warning.                 *)
}

let get_lines : In_channel.t -> (string -> 'a) -> 'a list = fun ic f ->
  let rec loop rev_lines =
    match In_channel.input_line ic with
    | None -> List.rev rev_lines
    | Some(line) -> loop (f line :: rev_lines)
  in
  loop []

type line =
  | Header of string * pos option
  | Data of string * bool (* Is this the last warning line? *)

let normalize_path : string -> string = fun path ->
  if String.starts_with ~prefix:"./" path then
    String.sub path 2 (String.length path - 2)
  else
    path

let parse_line : string -> line = fun line ->
  try
    Scanf.sscanf line "File %S, line %i, characters %i-%i:" @@
      fun w_file line c0 c1 ->
    let w_file = normalize_path w_file in
    let w_pos = if line = 0 then None else Some({line; c0; c1}) in
    Header(w_file, w_pos)
  with
  | End_of_file
  | Scanf.Scan_failure(_) ->
    let last_warning_line =
      let re = "^.*[[][^ ]+[]]$" in
      Str.string_match (Str.regexp re) line 0
    in
    Data(line, last_warning_line)

type item =
  | Warning of warning
  | Line of int * string

let make_warning : string -> pos option -> string list -> warning =
    fun w_file w_pos data ->
  let data = String.trim (String.concat "\n" data) in
  let (w_name, w_text) =
    if not (String.starts_with ~prefix:"Warning:" data) then
      panic "Invalid warning (no leading  \"Warning:\").";
    let len = String.length data in
    let ibracket = String.rindex_from data (len - 1) '[' in
    let tags = String.sub data (ibracket + 1) (len - ibracket - 2) in
    let tags = String.split_on_char ',' tags in
    let text = String.sub data 9 (len - 8 - (len - ibracket) - 2) in
    (List.hd tags, String.trim text)
  in
  {w_file; w_pos; w_name; w_text}

let gather : line list -> item list = fun lines ->
  let rec gather i rev_items header lines =
    let gather = gather (i+1) in
    match (header, lines) with
    | (None                 , []                        ) ->
        List.rev rev_items
    | (Some(_, _, _)        , []                        ) ->
        panic "Unexpected end of warning at line %i." i
    | (None                 , Header(file, pos) :: lines) ->
        gather rev_items (Some(file, pos, [])) lines
    | (None                 , Data(line, false) :: lines) ->
        gather (Line(i, line) :: rev_items) header lines
    | (None                 , Data(line, true ) :: lines) ->
        panic "Dangling end of warning at line %i." i
    | (Some(file, pos, data), Data(line, false) :: lines) ->
        gather rev_items (Some(file, pos, line :: data)) lines
    | (Some(file, pos, data), Data(line, true ) :: lines) ->
        let item = Warning(make_warning file pos (List.rev (line :: data))) in
        gather (item :: rev_items) None lines
    | (Some(_   , _  , _   ), Header(_   , _  ) :: _    ) ->
        panic "Nested warning at line %i." i
  in
  gather 1 [] None lines

let main () =
  let items = gather (get_lines stdin parse_line) in
  let (lines, warnings) =
    let f item (lines, warnings) =
      match item with
      | Line(i, line) -> ((i, line) :: lines, warnings)
      | Warning(w)    -> (lines, w :: warnings)
    in
    List.fold_right f items ([], [])
  in
  let warn_line (i, line) =
    Printf.eprintf "Warning: dangling input line.\n% 5i | %s\n%!" i line
  in
  List.iter warn_line lines;
  let to_json w =
    let fingerprint =
      let data =
        let pos = match w.w_pos with Some(pos) -> pos | None -> dummy_pos in
        Printf.sprintf "%s,%i,%i,%i,%s,%s"
          w.w_file pos.line pos.c0 pos.c1 w.w_name w.w_text
      in
      Digest.to_hex (Digest.string data)
    in
    let pos =
      let pos = match w.w_pos with Some(pos) -> pos | None -> dummy_pos in
      let line = ("line", `Int(pos.line)) in
      let b = `Assoc([line; ("column", `Int(pos.c0))]) in 
      let e = `Assoc([line; ("column", `Int(pos.c1))]) in 
      `Assoc([("begin", b); ("end", e)])
    in
    let location = [("path", `String(w.w_file)); ("positions", pos)] in
    let fields =
      ("description", `String(w.w_text)             ) ::
      ("check_name" , `String("warning:" ^ w.w_name)) ::
      ("fingerprint", `String(fingerprint)          ) ::
      ("severity"   , `String("minor")              ) ::
      ("location"   , `Assoc(location)              ) :: []
    in
    `Assoc(fields)
  in
  let json = `List(List.map to_json warnings) in
  Printf.printf "%a\n%!" (Yojson.Basic.pretty_to_channel ~std:true) json

let _ =
  try main () with
  | Sys_error(msg) -> panic "System error: %s" msg
