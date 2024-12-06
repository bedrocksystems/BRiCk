(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Internal

type t = unit Ctypes.ptr

let none = Ctypes.null

let make : Atom.t -> t = fun a ->
  let m = C.F.new_module (Atom.Unsafe.repr a) in
  if Ctypes.is_null m then prolog_error "Term.Module.make"; m

let _user = lazy (make (Atom.make "user"))

let user : unit -> t = fun _ ->
  Lazy.force _user

let context : unit -> t option = fun _ ->
  let m = C.F.context () in
  if Ctypes.ptr_compare m (Lazy.force _user) = 0 then None else Some(m)

let name : t -> Atom.t = fun m ->
  Atom.Unsafe.make (C.F.module_name m)

module Unsafe = struct
  external repr : t -> unit Ctypes.ptr = "%identity"
  external make : unit Ctypes.ptr -> t = "%identity"
end
