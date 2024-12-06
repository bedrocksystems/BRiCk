(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Internal

type frame_terminator = Close | Discard

let with_frame : (unit -> frame_terminator) -> unit = fun f ->
  let i = C.F.open_foreign_frame () in
  match Ctypes.Uintptr.equal i Ctypes.Uintptr.zero with
  | true -> prolog_error "Failed while opening a foreign frame."
  | _    ->
  match f () with
  | Close       -> C.F.close_foreign_frame i
  | Discard     -> C.F.discard_foreign_frame i
  | exception e -> C.F.discard_foreign_frame i; raise e

let with_closed_frame : (unit -> unit) -> unit = fun f ->
  with_frame (fun _ -> f (); Close)

let with_discarded_frame : (unit -> unit) -> unit = fun f ->
  with_frame (fun _ -> f (); Discard)
