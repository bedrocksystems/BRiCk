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

exception NoInstr

let error fmt =
  Extra.failwith ~fail:(fun msg -> raise (Error(msg))) fmt

let int_of_string : string -> int = fun s ->
  try Stdlib.int_of_string s with Failure _ ->
  error "the string %S cannot be parsed as an integer" s

let get_assoc : JSON.t -> (string * JSON.t) list = fun o ->
  match o with `Assoc(fs) -> fs | _ ->
  error "the given JSON element is not an association list"

let get_list : JSON.t -> JSON.t list = fun o ->
  match o with `List(os) -> os | _ ->
  error "the given JSON element is not an array"

let get_string : JSON.t -> string = fun o ->
  match o with `String(s) -> s | _ ->
  error "the given JSON element is not a string"

let get_words : JSON.t -> int = fun o ->
  let s =
    match String.split_on_char ' ' (get_string o) with
    | [s; "w"] -> s
    | _ -> error "the given JSON element does not contain a GC word count"
  in
  try Int.of_float (Float.of_string s) with Failure(_) ->
    error "the given JSON element does not contain a GC word count"

let get_int : JSON.t -> int = fun o ->
  match o with
  | `Int(i)    -> i
  | `String(s) -> int_of_string s
  | _          ->
  error "the given JSON element cannot be interpreted as an integer"

let get_field : JSON.t -> string -> JSON.t = fun o f ->
  try List.assoc f (get_assoc o) with Not_found ->
  error "no field named %S in the given JSON association list" f

let get_instr : JSON.t -> int = fun e ->
  let instr = try get_field e "instr" with Error _ -> raise NoInstr in
  get_int instr

let collect_dur_events : JSON.t list -> (JSON.t * JSON.t) list = fun evs ->
  let rec collect acc stack evs =
    match evs with
    | [] when stack <> [] -> error "duration events not well-bracketed"
    | []                  -> acc
    | event :: evs        ->
    match (get_string (get_field event "ph"), stack) with
    | ("B", _         ) -> collect acc (event :: stack) evs
    | ("E", []        ) -> error "duration event not well-bracketed"
    | ("E", b :: stack) -> collect ((b, event) :: acc) stack evs
    | _                 -> error "event type not supported"
  in
  collect [] [] evs

let extract_cmd : JSON.t -> JSON.t -> Data.cmd = fun b e ->
  let b = get_field b "args" in
  let e = get_field e "args" in
  let line = get_int (get_field b "line") in
  let (sbyte, ebyte, text) =
    let full_text = get_string (get_field b "cmd") in
    let (sbyte, ebyte, text) =
      match String.split_on_char ' ' full_text with
      | ["Chars"; sbyte; "-"; ebyte; text; ""] -> (sbyte, ebyte, text)
      | _                                      ->
      error "ill-formed command text %S" full_text
    in
    let sbyte = int_of_string sbyte in
    let ebyte = int_of_string ebyte in
    let text =
      let len = String.length text in
      if len < 2 then error "ill-formed command text %S" full_text;
      String.sub text 1 (len - 2)
    in
    (sbyte, ebyte, text)
  in
  let ic = get_instr e in
  Data.make_cmd ~line ~sbyte ~ebyte ~text ~ic ()

let extract : JSON.t -> Data.t = fun json ->
  let evs = get_list (get_field json "traceEvents") in
  let (ic, tm, mj, mn, evs) =
    match collect_dur_events evs with
    | []                            -> error "empty list of events"
    | (full_start, full_end) :: evs ->
    assert (get_string (get_field full_start "name") = "process");
    let args = get_field full_end "args" in
    let ic = get_instr args in
    let tm =
      let tm0 = get_int (get_field full_start "ts") in
      let tm1 = get_int (get_field full_end "ts") in
      tm1 - tm0
    in
    let mj = get_words (get_field args "major_words") in
    let mn = get_words (get_field args "minor_words") in
    (* TODO: also save "minor/major_collect" *)
    (ic, tm, mj, mn, evs)
  in
  let cs =
    let fn (b, e) =
      match get_string (get_field b "name") with
      | "command" -> Some (extract_cmd b e)
      | _         -> None
    in
    Array.of_list (List.filter_map fn (List.rev evs))
  in
  Data.make ~ic ~tm ~mj ~mn cs
