(*
 * Copyright (C) BlueRock Security Inc. 2021-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Stdlib_extra.Extra

module type PPJSON = sig
  include Format.PP

  val to_json : t -> JSON.t
end

module MakePPJSON(P : Format.PP) : PPJSON with type t = P.t = struct
  include P

  let to_json : t -> JSON.t = fun v ->
    let buf = Buffer.create 64 in
    let ff = Format.formatter_of_buffer buf in
    pp ff v; Format.pp_print_flush ff ();
    `String(Buffer.contents buf)
end

module type EventSpec = PPJSON
module type MetadataSpec = PPJSON

module IntMetadataSpec = struct
  type t = int
  let pp = Format.pp_print_int
  let to_json i = `Int(i)
end

module StringMetadataSpec = struct
  type t = string
  let pp = Format.pp_print_string
  let to_json s = `String(s)
end

module Metadata = struct
  type 'a spec = (module MetadataSpec with type t = 'a)

  type t = T : {
    name : string;
    spec : 'a spec;
    data : 'a;
  } -> t

  let make : string -> 'a spec -> 'a -> t = fun name spec data ->
    T({name; spec; data})

  let make_int : ('a -> int) -> string -> 'a -> t = fun f name v ->
    make name (module IntMetadataSpec) (f v)

  let make_string : ('a -> string) -> string -> 'a -> t = fun f name v ->
    make name (module StringMetadataSpec) (f v)

  let pp : t Format.pp = fun ff meta ->
    let T({name; spec = (module S); data}) = meta in
    Format.fprintf ff "%s=%a" name S.pp data

  let to_json : t -> string * JSON.t = fun meta ->
    let T({name; spec = (module S); data}) = meta in
    (name, S.to_json data)
end

type 'a event_spec = (module EventSpec with type t = 'a)

type event = E : {
  metadata : Metadata.t list;
  header : string option;
  spec : 'a event_spec;
  event : 'a;
} -> event

(* The integer is a unique key, the string just a name. *)
type span = {
  uid : int;
  name : string;
  mutable metadata : Metadata.t list
}

module Item = struct
  type item =
    | Span  of {
        span : span;
        items : item list;
      }
    | Event of {
        event : event;
      }
end

include Item

type path =
  | P_top
  | P_span of span * item list * path

type zipper = item list * path

let zipper_empty = ([], P_top)

type state = {
  mutable zipper          : zipper;
  mutable last_span_uid   : int;
  mutable event_counter   : int;
  mutable start_span_hook : span -> unit;
  mutable end_span_hook   : span -> unit;
  mutable direct_printing : unit -> bool;
}

let state = {
  zipper          = zipper_empty;
  last_span_uid   = -1;
  event_counter   = 0;
  start_span_hook = ignore;
  end_span_hook   = ignore;
  direct_printing = (fun _ -> false);
}

module Span = struct
  type t = span

  let uid : t -> int = fun s -> s.uid
  let name : t -> string = fun s -> s.name
  let metadata : t -> Metadata.t list = fun s -> s.metadata

  let equal : t -> t -> bool = fun s1 s2 -> s1.uid = s2.uid

  let next_uid : unit -> int = fun _ ->
    let uid = state.last_span_uid + 1 in
    state.last_span_uid <- uid; uid

  let push : ?metadata:Metadata.t list -> string -> t =
      fun ?(metadata=[]) name ->
    let span = {uid = next_uid (); name; metadata} in
    state.start_span_hook span;
    let (rev_items, path) = state.zipper in
    state.zipper <- ([], P_span(span, rev_items, path));
    span

  let pop : t -> unit = fun span ->
    let (rev_items, path) = state.zipper in
    let check_span found =
      let pp_span ff s = Format.fprintf ff "%s (key %i)" s.name s.uid in
      if not (equal found span) then
        failwith "Span.pop: expected %a, found %a." pp_span span pp_span found
    in
    match path with
    | P_top                     ->
        failwith "Span.pop: no open span named %S." span.name
    | P_span(span, items, path) ->
        let s =
          state.end_span_hook span;
          let items = List.rev rev_items in
          Span({span; items})
        in
        check_span span;
        state.zipper <- (s :: items, path)

  let pop_until : t -> unit = fun target_span ->
    let rec pop_until (rev_items, path) =
      match path with
      | P_top                     ->
          failwith "Span.pop_until: could not find span %S." target_span.name
      | P_span(span, items, path) ->
          let s =
            state.end_span_hook span;
            let items = List.rev rev_items in
            Span({span; items})
          in
          let state = (s :: items, path) in
          if equal span target_span then state else pop_until state
    in
    state.zipper <- pop_until state.zipper

  let pop_all : unit -> unit = fun _ ->
    let rec pop_all ((rev_items, path) as zipper) =
      match path with
      | P_top                     -> zipper
      | P_span(span, items, path) ->
          let s =
            state.end_span_hook span;
            let items = List.rev rev_items in
            Span({span; items})
          in
          pop_all (s :: items, path)
    in
    state.zipper <- pop_all state.zipper

  let update_metadata : t -> (Metadata.t list -> Metadata.t list) -> unit =
    fun span f -> span.metadata <- f span.metadata

  let set_start_span_hook : (t -> unit) -> unit = fun f ->
    state.start_span_hook <- f

  let set_end_span_hook : (t -> unit) -> unit = fun f ->
    state.end_span_hook <- f
end

module Event = struct
  type 'a spec = 'a event_spec

  type t = event = E : {
    metadata : Metadata.t list;
    header : string option;
    spec : 'a spec;
    event : 'a;
  } -> t

  let pp_metadata ff (E({metadata; _})) =
    List.iter (Format.fprintf ff ", %a" Metadata.pp) metadata

  let pp : t Format.pp = fun ff event ->
    let E({header; spec = (module M); event; _}) = event in
    Option.iter (Format.fprintf ff "%s:\n") header; M.pp ff event

  let to_json : t -> JSON.t = fun event ->
    let E({header; spec = (module M); event; metadata}) = event in
    let metadata = `Assoc(List.map Metadata.to_json metadata) in
    let event = M.to_json event in
    let assoc = ("meta", metadata) :: ("data", event) :: [] in
    match header with
    | None -> `Assoc(assoc)
    | Some(h) -> `Assoc(("header", `String(h)) :: assoc)

  type 'a recorder = ?metadata:Metadata.t list -> ?header:string -> 'a -> unit

  let pp_txt : Format.formatter -> path -> event -> unit = fun ff path e ->
    let rec span_path : string -> path -> string = fun acc path ->
      match path with
      | P_top            -> acc
      | P_span(s,_,path) -> span_path (s.name ^ ":" ^ acc) path
    in
    let path = span_path "" path in
    let path = if path = "" then "toplevel" else path in
    Format.fprintf ff "[%s%a] %a\n%!" path pp_metadata e pp e

  let make_recorder : type a. a event_spec -> a recorder =
      fun (module M) ?(metadata=[]) ?header event ->
    let event = E({metadata; header; spec = (module M); event}) in
    let (rev_items, path) = state.zipper in
    if state.direct_printing () then pp_txt Format.err_formatter path event;
    state.event_counter <- state.event_counter + 1;
    state.zipper <- (Event({event}) :: rev_items, path)

  let set_direct_printing : (unit -> bool) -> unit = fun f ->
    state.direct_printing <- f
end

let static_css = Static_css.contents
let static_js  = Static_js.contents

let html_template : (_, _, _, _, _, _) format6 =
{html|<!DOCTYPE html>
<html>
  <head>
    <meta charset="UTF-8">
    <title>BedRock log viewer</title>
    <style>
%s
    </style>
    <script>
%s
    </script>
  </head>
  <body>
    <div id="contents"></div>
    <script>
      var data = %a;
      generate_page(document.getElementById('contents'), data);
    </script>
  </body>
</html>
%!|html}

module Log = struct
  include Item

  type t = item list

  let collect : unit -> t = fun _ ->
    let exception Not_at_the_top of span * span list in
    let collect_top (rev_items, path) =
      match path with
      | P_top              -> List.rev rev_items
      | P_span(span, _, p) ->
          let rec get_path p =
            match p with
            | P_top           -> []
            | P_span(s, _, p) -> s :: get_path p
          in
          raise (Not_at_the_top(span, get_path p))
    in
    try collect_top state.zipper with
    | Not_at_the_top(s, []) ->
        failwith "Log.collect: span %S is still open." (Span.name s)
    | Not_at_the_top(s, ss) ->
        let ss = String.concat ", " (List.map Span.name (s :: ss)) in
        failwith "Log.collect: spans %S are still open." ss

  let collect_debug : unit -> t = fun _ ->
    let rec collect (rev_items, path) =
      match path with
      | P_top                     -> List.rev rev_items
      | P_span(span, items, path) ->
          let s =
            state.end_span_hook span;
            let items = List.rev rev_items in
            Span({span; items})
          in
          collect (s :: items, path)
    in
    collect state.zipper

  let pp : t Format.pp = fun ff items ->
    let rec pp path_list path item =
      match item with
      | Span({span; items}) ->
          let path =
            match path with
            | None    -> Span.name span
            | Some(p) -> p ^ ":" ^ Span.name span
          in
          List.iter (pp (span :: path_list) (Some(path))) items
      | Event({event = e})  ->
          let path = match path with Some(p) -> p | _ -> "toplevel" in
          Format.fprintf ff "[%s%a] %a\n" path Event.pp_metadata e Event.pp e
    in
    List.iter (pp [] None) items

  let to_json : t -> JSON.t = fun items ->
    let rec to_json item =
      match item with
      | Span({span; items}) ->
          let metadata = List.map Metadata.to_json (Span.metadata span) in
          `Assoc([
            ("name" , `String(Span.name span));
            ("uid"  , `Int(Span.uid span));
            ("meta" , `Assoc(metadata));
            ("items", `List(List.map to_json items));
          ])
      | Event({event})      -> Event.to_json event
    in
    `List(List.map to_json items)

  let output_text : Stdlib.out_channel -> t -> unit = fun oc log ->
    let ff = Format.formatter_of_out_channel oc in
    pp ff log;
    Format.pp_print_flush ff ()

  let output_json : Stdlib.out_channel -> t -> unit = fun oc log ->
    JSON.write oc (to_json log)

  let output_html : Stdlib.out_channel -> t -> unit = fun oc log ->
    Printf.fprintf oc html_template static_css static_js output_json log

  let write : ?debug:bool -> string -> unit = fun ?(debug=false) path ->
    let log = if debug then collect_debug () else collect () in
    let output =
      match path with
      | _ when Filename.extension path = ".txt"  -> output_text
      | _ when Filename.extension path = ".json" -> output_json
      | _ when Filename.extension path = ".html" -> output_html
      | _                                        ->
      failwith "Invalid extension on %S." path
    in
    try Out_channel.with_open_text path (fun oc -> output oc log)
    with Sys_error(err) -> failwith "Error while writing the log.\n%s" err

  let write_tmp : ?debug:bool -> ?prefix:string -> string -> string =
      fun ?(debug=false) ?(prefix="log") ext ->
    if ext = "" || ext.[0] <> '.' then
      failwith "The string %S is not a valid extension." ext;
    let path =
      try Filename.temp_file prefix ext with Sys_error(_) ->
        failwith "Error while creating the temporary file."
    in
    write ~debug path; path

  let write_buffer : ?debug:bool -> unit -> Buffer.t = fun ?(debug=false) _ ->
    let b = Buffer.create 2048 in
    let ff = Format.formatter_of_buffer b in
    pp ff (if debug then collect_debug () else collect ());
    Format.pp_print_flush ff (); b

  let count_events : unit -> int = fun () -> state.event_counter

  module State = struct
    type t = state

    let save : unit -> t = fun _ ->
      {
        zipper          = state.zipper;
        last_span_uid   = state.last_span_uid;
        event_counter   = state.event_counter;
        start_span_hook = state.start_span_hook;
        end_span_hook   = state.end_span_hook;
        direct_printing = state.direct_printing;
      }

    let restore : t -> unit = fun s ->
      state.zipper          <- s.zipper;
      state.last_span_uid   <- s.last_span_uid;
      state.event_counter   <- s.event_counter;
      state.start_span_hook <- s.start_span_hook;
      state.end_span_hook   <- s.end_span_hook;
      state.direct_printing <- s.direct_printing
  end
end
