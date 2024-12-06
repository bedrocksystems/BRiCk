(*
 * Copyright (C) BlueRock Security Inc. 2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Ltac2_plugin
open Tac2ffi
open Tac2externals

type t = CWarnings.warning

let repr =
  let tag : t Tac2dyn.Val.tag = Tac2dyn.Val.create "CWarnings.t" in
  Tac2ffi.repr_ext tag

let define s =
  define Tac2expr.{ mltac_plugin = "warnings"; mltac_tactic = s }

let _ =
  define "emit_warning" (repr @-> pp @-> ret unit) @@ fun w pp ->
  CWarnings.create_in w Fun.id ?loc:None pp
