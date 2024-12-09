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

let auto_re =
  let names =
    [ "go"; "work"; "verify_"; "wthrough"; "wuntil"; "wp_if"; "wp_for";
      "wp_while"; "wp_do"; "wp_eif"; ]
  in
  {|.*\(\(|} ^ String.concat {|\)\|\(|} names ^ {|\)\).*|}

let config = [|
  ({|Qed\.|}                       , "Qed"       );
  ({|\(\(From\)\|\(Require\)\)~.*|}, "Require"   );
  ({|Definition~module~.*|}        , "TU def"    );
  (auto_re                         , "automation");
  ({|.*cpp\.spec.*|}               , "cpp.spec"  );
  ({|.*cpp\.enum.*|}               , "cpp.enum"  );
  ({|.*cpp\.model.*|}              , "cpp.model" );
  ({|.*cpp\.rep.*|}                , "cpp.rep"   );
  ({|.*cpp\.class.*|}              , "cpp.class" );
  ({|.*wapply.*|}                  , "wapply"    );
  ({|.*wmod.*|}                    , "wmod"      );
  ({|.*vc_split.*|}                , "vc_split"  );
  ({|.*NES.*|}                     , "NES"       );
  ({|.*rewrite.*|}                 , "rewrite"   );
  ({|.*\bi[A-Z].*|}                , "IPM"       );
  ({|.*|}                          , "others"    );
|]

let regexps = Array.map (fun (re, _) -> Str.regexp re) config

let exactly_matches : Str.regexp -> string -> bool = fun re s ->
  Str.string_match re s 0 && Str.matched_group 0 s = s

let matches : string -> int = fun s ->
  let exception Found of int in
  let matches i re = if exactly_matches re s then raise (Found(i)) in
  try
    Array.iteri matches regexps;
    panic "Command %S did not match any regexp." s
  with Found(i) -> i

let icounts = Array.make (Array.length regexps) 0

let cmd_data : string -> unit = fun file ->
  let Data.{cs; ic; _} = Data.read_json file in
  let handle_cmd Data.{cmd_text; cmd_ic; _} =
    let i = matches cmd_text in
    icounts.(i) <- icounts.(i) + cmd_ic
  in
  Array.iter handle_cmd cs;
  Printf.printf "Command RE,Description,Instruction #,Instructions %%\n%!";
  let print_line (re, descr) i =
    let p = Float.of_int (i * 100) /. Float.of_int ic in
    Printf.printf "%S,%s,%i,%02.2f%%\n%!" re descr i p
  in
  Array.iter2 print_line config icounts

let _ =
  match List.tl (Array.to_list Sys.argv) with
  | args when List.exists (fun o -> List.mem o ["-h"; "--help"]) args ->
      Printf.printf "Usage: %s [-h | --help] DATA.csv\n%!" Sys.argv.(0)
  | data_file :: [] ->
      cmd_data data_file
  | _ :: o :: _ ->
      Printf.eprintf "Error: unknown command line opton %S\n%!" o;
      panic "Usage: %s [-h | --help] DATA.csv\n%!" Sys.argv.(0)
  | [] ->
      panic "Usage: %s [-h | --help] DATA.csv\n%!" Sys.argv.(0)
