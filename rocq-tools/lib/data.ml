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

type cmd = {
  cmd_line  : int;
  cmd_sbyte : int;
  cmd_ebyte : int;
  cmd_text  : string;
  cmd_ic    : int;
}

(* Hash-table containing all strings, for hash-consing. *)
let strings : (string, string) Hashtbl.t = Hashtbl.create 73

let make_cmd ~line ~sbyte ~ebyte ~text ~ic () =
  let text =
    try Hashtbl.find strings text with Not_found ->
    Hashtbl.add strings text text; text
  in
  {cmd_line=line; cmd_sbyte=sbyte; cmd_ebyte=ebyte; cmd_text=text; cmd_ic=ic}

type t = {
  ic : int;
  tm : int;
  mj : int;
  mn : int;
  cs : cmd array
}

let make ~ic ~tm ~mj ~mn cmds =
  {ic; tm; mj; mn; cs=cmds}

let to_json {ic; tm; mj; mn; cs} =
  let cmd {cmd_line=l; cmd_sbyte=s; cmd_ebyte=e; cmd_text=p; cmd_ic=i} =
    `Assoc([
      ("l", `Int(l));
      ("s", `Int(s));
      ("e", `Int(e));
      ("p", `String(p));
      ("i", `Int(i));
    ])
  in
  let cs = Array.fold_right (fun c acc -> cmd c :: acc) cs [] in
  `Assoc([
    ("i", `Int(ic));
    ("t", `Int(tm));
    ("mj", `Int(mj));
    ("mn", `Int(mn));
    ("cs", `List(cs));
  ])

let of_json o =
  let exception E in
  let get_int fs f =
    match List.assoc_opt f fs with Some(`Int(i)) -> i | _ -> raise E
  in
  let get_str fs f =
    match List.assoc_opt f fs with Some(`String(s)) -> s | _ -> raise E
  in
  let get_list fs f =
    match List.assoc_opt f fs with Some(`List(l)) -> l | _ -> raise E
  in
  let process ~ic ~tm ~mj ~mn cs =
    let process_cmd e =
      let fs = match e with `Assoc(fs) -> fs | _ -> raise E in
      let line = get_int fs "l" in
      let sbyte = get_int fs "s" in
      let ebyte = get_int fs "e" in
      let text = get_str fs "p" in
      let ic = get_int fs "i" in
      make_cmd ~line ~sbyte ~ebyte ~text ~ic ()
    in
    make ~ic ~tm ~mj ~mn (Array.of_list (List.map process_cmd cs))
  in
  let process_cmd fs =
    let ic = get_int fs "i" in
    let tm = get_int fs "t" in
    let mj = get_int fs "mj" in
    let mn = get_int fs "mn" in
    let cs = get_list fs "cs" in
    process ~ic ~tm ~mj ~mn cs
  in
  match o with
  | `Assoc(fs) -> (try Some(process_cmd fs) with E -> None)
  | _          -> None

exception Read_error of string

let read_json : string -> t = fun path ->
  let data =
    let open Yojson in
    try Basic.from_file path with
    | Json_error(s) -> raise (Read_error(s))
  in
  match of_json data with
  | Some(data) -> data
  | None -> raise (Read_error("cannot interpret JSON data"))

let write_json : string -> t -> unit = fun path data ->
  let json = to_json data in
  Yojson.Basic.to_file path json

let _ = Random.self_init ()

let add_noise_int : Float.t -> int -> int = fun p i ->
  let i = Float.of_int i in
  let r = Random.float (Float.abs (p *. i)) in
  Float.to_int (if Random.bool () then i +. r else i -. r)

let add_noise_cmd : Float.t -> cmd -> cmd = fun p cmd ->
  {cmd with cmd_ic = add_noise_int p cmd.cmd_ic}

let add_noise : Float.t -> t -> t = fun p {ic; tm; mj; mn; cs} ->
  let ic = add_noise_int p ic in
  let tm = add_noise_int p tm in
  let mj = add_noise_int p mj in
  let mn = add_noise_int p mn in
  let cs = Array.map (add_noise_cmd p) cs in
  {ic; tm; mj; mn; cs}
