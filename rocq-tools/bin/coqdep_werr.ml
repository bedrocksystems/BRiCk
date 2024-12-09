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

let coqdep_command : string list -> string = fun args ->
  let coqc =
    match Sys.getenv_opt "DUNE_SOURCEROOT" with
    | None       -> "coqdep"
    | Some(root) -> Filename.concat root "_build/install/default/bin/coqdep"
  in
  Filename.quote_command coqc args

let _ =
  let args = List.tl (Array.to_list Sys.argv) in
  exit (Sys.command (coqdep_command ("-w" :: "+all" :: args)))
