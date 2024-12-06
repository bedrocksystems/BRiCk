(*
 * Copyright (C) BlueRock Security Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Stdlib_extra.Extra

include Pp

let rec no_box : t -> t = fun t ->
  match repr t with
  | Ppcmd_empty
  | Ppcmd_string(_)        -> t
  | Ppcmd_glue(ts)         -> unrepr (Ppcmd_glue(List.map no_box ts))
  | Ppcmd_box(_,t)
  | Ppcmd_tag(_,t)         -> no_box t
  | Ppcmd_print_break(_,_)
  | Ppcmd_force_newline    -> str " "
  | Ppcmd_comment(_)       -> unrepr Ppcmd_empty

let to_flat_string : t -> string =
  let b = Buffer.create 1024 in
  let rec to_string t =
    match repr t with
    | Ppcmd_empty            -> ()
    | Ppcmd_string(s)        -> Buffer.add_string b s
    | Ppcmd_glue(ts)         -> List.iter to_string ts
    | Ppcmd_box(_,t)
    | Ppcmd_tag(_,t)         -> to_string t
    | Ppcmd_print_break(_,_)
    | Ppcmd_force_newline    -> Buffer.add_char b ' '
    | Ppcmd_comment(_)       -> ()
  in
  fun t -> Buffer.clear b; to_string t; Buffer.contents b
