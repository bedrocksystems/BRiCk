(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

type version = {
  major: int;
  minor: int;
  patch: int;
}

let make : Unsigned.UInt.t -> version = fun i ->
  let open Unsigned.UInt in
  let i100 = of_int 100 in
  let patch = to_int (rem i i100) in
  let i = div i i100 in
  let minor = to_int (rem i i100) in
  let i = div i i100 in
  let major = to_int i in
  {major; minor; patch}

let get_SYSTEM : unit -> version = fun () ->
  make (C.F.version_info C.T._VERSION_SYSTEM)

let version : unit -> string = fun () ->
  let {major; minor; patch} = get_SYSTEM () in
  Printf.sprintf "%i.%i.%i" major minor patch

let get_FLI : unit -> int = fun () ->
  Unsigned.UInt.to_int (C.F.version_info C.T._VERSION_FLI)

let get_REC : unit -> int = fun () ->
  Unsigned.UInt.to_int (C.F.version_info C.T._VERSION_REC)

let get_QLF : unit -> int = fun () ->
  Unsigned.UInt.to_int (C.F.version_info C.T._VERSION_QLF)

let get_QLF_LOAD : unit -> int = fun () ->
  Unsigned.UInt.to_int (C.F.version_info C.T._VERSION_QLF)

let get_VM : unit -> int = fun () ->
  Unsigned.UInt.to_int (C.F.version_info C.T._VERSION_VM)

let get_BUILT_IN : unit -> int option = fun () ->
  let i = C.F.version_info C.T._VERSION_BUILT_IN in
  match Unsigned.UInt.to_int i with
  | 0 -> None
  | i -> Some(i)
