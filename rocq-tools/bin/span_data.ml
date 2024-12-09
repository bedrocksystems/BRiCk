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

let with_generic_hint_name : Spandata.Span.t -> Spandata.Span.t = fun span ->
  let Spandata.Span.{name; status} = span in
  let name =
    match status with
    | Some("hintOK" | "hintKO") -> "<hint>"
    | _                         -> name
  in
  Spandata.Span.{name; status}

let span_data : string -> unit = fun file ->
  let data = Spandata.add_csv_file file Spandata.M.empty in
  let with_generic_hint_name Spandata.Key.{span_path; span} =
    let span_path = List.map with_generic_hint_name span_path in
    let span = with_generic_hint_name span in
    Some(Spandata.Key.{span_path; span})
  in
  let data = Spandata.aggregate_filter with_generic_hint_name data in
  Printf.printf "%a%!" Spandata.output_csv data

let _ =
  match List.tl (Array.to_list Sys.argv) with
  | args when List.exists (fun o -> List.mem o ["-h"; "--help"]) args ->
      Printf.printf "Usage: %s [-h | --help] DATA.csv\n%!" Sys.argv.(0)
  | data_file :: [] ->
      span_data data_file
  | _ :: o :: _ ->
      Printf.eprintf "Error: unknown command line opton %S\n%!" o;
      panic "Usage: %s [-h | --help] DATA.csv\n%!" Sys.argv.(0)
  | [] ->
      panic "Usage: %s [-h | --help] DATA.csv\n%!" Sys.argv.(0)
