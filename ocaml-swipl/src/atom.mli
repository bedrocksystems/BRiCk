(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Representation of a prolog atom. *)
type t

(** [make name] creates a new atom named [name]. An [Util.Prolog] exception is
    raised upon allocation errors. Note that the behaviour of this function is
    unspecified if [name] is not a valid UTF-8 encoded string. *)
val make : string -> t

(** [to_string a] gives the string representation of the given atom [a] (i.e.,
    the [name] used when the atom was created with [make name]). In case of an
    error, the [Util.Prolog] exception is raised. *)
val to_string : t -> string

(** [hash a] returns an integer hash of the atom [a]. *)
val hash : t -> int

(** [equal a1 a2] indicates whether [a1] and [a2] refer to the same atom. *)
val equal : t -> t -> bool

(** Unsafe interface exposing the implementation details of the [t] type. *)
module Unsafe : sig
  val repr : t -> Ctypes.Uintptr.t
  val make : Ctypes.Uintptr.t -> t
end
