(*
 * Copyright (C) BlueRock Security Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Stdlib_extra.Extra
module Pp = Extra_pp

(** Standard formatter with continuation. *)
type 'a fmt = ('a, unit) Format.koutfmt

let buf = Buffer.create 100
let buf_ff = Format.formatter_of_buffer buf
let flush_buf_ff () =
  Format.pp_print_flush buf_ff ();
  let msg = Buffer.contents buf in
  Buffer.clear buf; msg

let make_msg : only_if_verbose:bool -> (Pp.t -> unit) -> 'a fmt -> 'a =
    fun ~only_if_verbose print_msg fmt ->
  let k _ =
    let run () =
      let msgs = String.split_on_char '\n' (flush_buf_ff ()) in
      List.iter (fun msg -> print_msg (Pp.str msg)) msgs
    in
    if only_if_verbose then Flags.if_verbose run () else run ()
  in
  Format.kfprintf k buf_ff fmt

let wrn : 'a fmt -> 'a = fun fmt ->
  make_msg ~only_if_verbose:false Feedback.msg_warning fmt

let as_pp : (Pp.t -> unit) -> 'a fmt -> 'a = fun emit fmt ->
  make_msg ~only_if_verbose:false emit fmt

let notice : 'a fmt -> 'a = fun fmt ->
  make_msg ~only_if_verbose:false Feedback.msg_notice fmt

let info : 'a fmt -> 'a = fun fmt ->
  make_msg ~only_if_verbose:true Feedback.msg_info fmt

let debug : 'a fmt -> 'a = fun fmt ->
  make_msg ~only_if_verbose:false Feedback.msg_debug fmt

let notice_divider : ?w:int -> string option -> unit = fun ?(w=78) os ->
  if w < 0 then invalid_arg "Dnet_core.Msg.notice_divider";
  match os with
  | None    -> notice "%s" (String.make w '=')
  | Some(s) ->
  let n = String.length s in
  if n + 10 > w then invalid_arg "Dnet_core.Msg.notice_divider";
  notice "==== %s %s" s (String.make (w - 6 - n) '=')

let convert : ('a -> Pp.t) -> 'a Format.pp = fun pp ff e ->
  Pp.pp_with ff (Pp.no_box (pp e))
