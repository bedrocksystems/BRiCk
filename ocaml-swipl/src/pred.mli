(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Representation of a prolog predicate. *)
type t

(** [make ~m f] creates a predicate from functor [f] in module [m] (when there
    is no [m], the current context module is used). Exception [Util.Prolog] is
    raised upon allocation errors. *)
val make : ?m:Module.t -> Functor.t -> t

(** Unsafe interface exposing the implementation details of the [t] type. *)
module Unsafe : sig
  val repr : t -> unit Ctypes.ptr
  val make : unit Ctypes.ptr -> t
end
