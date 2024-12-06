(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Query versions information (no initialisation required). *)

(** SWI-Prolog version representation. *)
type version = {
  major: int;
  minor: int; (* Between 0 and 99. *)
  patch: int; (* Between 0 and 99. *)
}

(** [get_SYSTEM ()] gives the SWI-prolog version. *)
val get_SYSTEM : unit -> version

(** [version ()] gives the SWI-prolog version as a string. *)
val version : unit -> string

(** [get_FLI ()] gives the version for the foreign interface, which is
    incremented when a change breaks backward compatibility). *)
val get_FLI : unit -> int

(** [get_REC ()] gives the version for the binary representation, as used
    by [record_external] and [fast_write/2]. *)
val get_REC : unit -> int

(** [get_QLF ()] gives the version of the QLF file format. *)
val get_QLF : unit -> int

(** [get_QLF_LOAD ()] gives the oldest loadable QLF file format version. *)
val get_QLF_LOAD : unit -> int

(** [get_VM ()] gives a hash that represents the VM instructions and their
    arguments. *)
val get_VM : unit -> int

(** [get_BUILT_IN ()] gives a hash that represents the names, arities and
    properties of all built-in predicates defined in C. If this function is
    called before initialisation it returns [None]. *)
val get_BUILT_IN : unit -> int option
