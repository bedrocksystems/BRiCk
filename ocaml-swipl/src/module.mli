(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Representation of a prolog atom. *)
type t

val none : t

val make : Atom.t -> t

val user : unit -> t

val context : unit -> t option

val name : t -> Atom.t

(** Unsafe interface exposing the implementation details of the [t] type. *)
module Unsafe : sig
  val repr : t -> unit Ctypes.ptr
  val make : unit Ctypes.ptr -> t
end
