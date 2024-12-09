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

type metadata = string * JSON.t

type event = {
  metadata : metadata list;
  header   : string option;
  event    : JSON.t;
}

type span = {
  uid      : int;
  name     : string;
  metadata : metadata list;
}

type item =
  | Span  of {
      span  : span;
      items : item list;
    }
  | Event of {
      event : event;
    }

type t = item list

let iter : (span list -> event -> unit) ->
    (span list -> span -> item list -> unit) -> t -> unit = fun fe fs is ->
  let rec iter path is =
    match is with
    | []                              -> ()
    | Event({event=e})          :: is ->
        fe path e;
        iter path is
    | Span({span=s; items=iss}) :: is ->
        fs path s iss;
        iter (s :: path) iss;
        iter path is
  in
  iter [] is

exception Error of string

let error fmt =
  Extra.failwith ~fail:(fun msg -> raise (Error(msg))) fmt

let get_assoc : JSON.t -> (string * JSON.t) list = fun o ->
  match o with `Assoc(fs) -> fs | _ ->
  error "the given JSON element is not an association list"

let get_list : JSON.t -> JSON.t list = fun o ->
  match o with `List(os) -> os | _ ->
  error "the given JSON element is not an array"

let get_string : JSON.t -> string = fun o ->
  match o with `String(s) -> s | _ ->
  error "the given JSON element is not a string"

let get_int : JSON.t -> int = fun o ->
  match o with `Int(i)    -> i | _ ->
  error "the given JSON element is not an integer"

let get_field : JSON.t -> string -> JSON.t = fun o f ->
  try List.assoc f (get_assoc o) with Not_found ->
  error "no field named %S in the given JSON association list" f

let get_opt_field : JSON.t -> string -> JSON.t option = fun o f ->
  List.assoc_opt f (get_assoc o)

let of_json : JSON.t -> t = fun json ->
  let rec to_item json =
    let metadata =
      match get_opt_field json "meta" with
      | None       -> []
      | Some(json) -> get_assoc json
    in
    match get_opt_field json "uid" with
    | None      ->
        let header = Option.map get_string (get_opt_field json "header") in
        let event = get_field json "data" in
        Event({event = {metadata; header; event}})
    | Some(uid) ->
        let uid = get_int uid in
        let name = get_string (get_field json "name") in
        let items = get_list (get_field json "items") in
        let items = List.map to_item items in
        Span({span = {uid; name; metadata}; items})
  in
  List.map to_item (get_list json)
