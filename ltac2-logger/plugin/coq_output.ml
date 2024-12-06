(*
 * Copyright (C) BlueRock Security Inc. 2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

type buffer = {
  saved_std_ff  : Format.formatter;
  saved_err_ff  : Format.formatter;
  saved_deep_ff : Format.formatter;
  buffer        : Buffer.t;
  formatter     : Format.formatter;
}

let start_capture () =
  (* Create the internal buffer and associated formatter. *)
  let buffer = Buffer.create 1024 in
  let formatter = Format.formatter_of_buffer buffer in
  (* Save the current state of the Coq internal formatters. *)
  let saved_std_ff  = !Topfmt.std_ft  in
  let saved_err_ff  = !Topfmt.err_ft  in
  let saved_deep_ff = !Topfmt.deep_ft in
  (* Write our own formatter. *)
  Topfmt.std_ft  := formatter;
  Topfmt.err_ft  := formatter;
  Topfmt.deep_ft := formatter;
  {saved_std_ff; saved_err_ff; saved_deep_ff; buffer; formatter}

let contents buf =
  Format.pp_print_flush buf.formatter ();
  Buffer.contents buf.buffer

let clear buf =
  Format.pp_print_flush buf.formatter ();
  Buffer.clear buf.buffer

let end_capture buf =
  Topfmt.std_ft  := buf.saved_std_ff;
  Topfmt.err_ft  := buf.saved_err_ff;
  Topfmt.deep_ft := buf.saved_deep_ff
