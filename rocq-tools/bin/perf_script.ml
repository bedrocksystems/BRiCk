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

(* This program turns the spans of a JSON log file into "perf script" format.
   The result can be used with flamegraph-related tools. In particular, this
   includes https://profiler.firefox.com. Note that the spans are always put
   int the log, independently of log files.

   The output data can be directly concatenated with simultaneously generated
   Linux perf data ("perf record -k MONOTONIC_CLOCK" should be used for the
   clocks to be in sync), and then loaded similarly in a profiler. *)

type span = S of {key : string; t0 : int; t1 : int; spans : span list}

let spans_of_log : Log.t -> span list = fun log ->
  let rec to_span log =
    match log with
    | Log.Event(_)            -> []
    | Log.Span({span; items}) ->
        let key = span.Log.name in
        let (t0, t1) =
          let metadata = span.Log.metadata in
          let t0 =
            match List.assoc "t0" metadata with
            | `Int(t0)            -> t0
            | _                   ->
                panic "Integer expected in t0 metadata field."
            | exception Not_found ->
                panic "Missing t0 metadata field on span."
          in
          let t1 =
            match List.assoc "t1" metadata with
            | `Int(t1)            -> t1
            | _                   ->
                panic "Integer expected in t1 metadata field."
            | exception Not_found ->
                panic "Missing t1 metadata field on span."
          in
          (t0, t1)
        in
        let spans = List.concat_map to_span items in
        [S({key; t0; t1; spans})]
  in
  List.concat_map to_span log

let sample : int -> span -> string list = fun i s ->
  let contains_time i (S({t0; t1})) = t0 <= i && i <= t1 in
  let rec sample ctx (S({key; spans})) =
    match List.find_opt (contains_time i) spans with
    | None    -> key :: ctx
    | Some(s) -> sample (key :: ctx) s
  in
  sample [] s

let perf_script : int -> span -> unit = fun intv (S({t0; t1; _}) as span) ->
  let time = ref t0 in
  while !time < t1 do
    let span_stack = sample !time span in
    Printf.printf "work 400000 %f:     1 instructions:u: \n"
      (Float.of_int !time /. 1000.0 /. 1000.0);
    let pp_stack_item key =
      Printf.printf "\t           10000 %s (ltac2_profiling)\n" key
    in
    List.iter pp_stack_item span_stack;
    Printf.printf "\n%!";
    time := !time + intv
  done

let perf_script : int -> string -> unit = fun intv file ->
  let log =
    try Log.of_json (Yojson.Basic.from_file file) with
    | Yojson.Json_error(s) -> panic "JSON error: %s.\n%!" s
    | Sys_error(s)         -> panic "System error: %s.\n%!" s
    | Log.Error(s)         -> panic "Invalid log: %s.\n%!" s
  in
  let span =
    let spans = spans_of_log log in
    match spans with
    | []             -> S({key="toplevel"; t0=0; t1=1; spans=[]})
    | [s]            -> s
    | S({t0;_}) :: _ ->
        let S({t1;_}) = List.hd (List.rev spans) in
        S({key="toplevel"; t0; t1; spans})
  in
  perf_script intv span

let _ =
  let prog = Sys.argv.(0) in
  let args = List.tl (Array.to_list Sys.argv) in
  match args with
  | args when List.exists (fun o -> List.mem o ["-h"; "--help"]) args ->
      Printf.printf "Usage: %s [-h | --help] [μsINTV] LOG.json\n%!" prog
  | intv :: logfile :: [] ->
      let intv =
        try int_of_string intv with Invalid_argument(_) ->
        panic "Command line argument %S was expected to be an integer." intv
      in
      if intv < 1 then panic "The interval value (in μs) must be at least 1.";
      perf_script intv logfile
  | logfile :: [] ->
      perf_script 1000 logfile
  | _ :: _ :: o :: _ ->
      Printf.eprintf "Error: unknown command line opton %S\n%!" o;
      panic "Usage: %s [-h | --help] [INTV] LOG.json\n%!" Sys.argv.(0)
  | [] ->
      Printf.eprintf "Error: arguments expected\n%!";
      panic "Usage: %s [-h | --help] [INTV] LOG.json\n%!" Sys.argv.(0)
