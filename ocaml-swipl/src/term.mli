(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Working with Prolog terms (initialisation required). *)

(** Term reference manipulation. *)
module Ref : sig
  (** Term reference. *)
  type t

  (** [make ()] returns a new term reference, whose pointed term is a fresh
      variable. The exception [Prolog] is raised upon allocation errors. *)
  val make : unit -> t

  (** [reset r] resets the term reference [r] to its initial state. After a
      call to this function, the pointed term is a fresh variable. *)
  val reset : t -> unit

  module Unsafe : sig
    val repr : t -> Ctypes.Uintptr.t
    val make : Ctypes.Uintptr.t -> t
  end
end

(** Array of term references. *)
module Refs : sig
  (** Array of consecutive term references. *)
  type t

  (** [make n] returns an array of fresh new term references of length [n].
      The exception [Invalid_argument] is raised if [n] is striclty smaller
      than [1], and [Prolog] is raised on allocation error. *)
  val make : int -> t

  (** [length ar] gives the length of the reference array [ar]. *)
  val length : t -> int

  (** [unsafe_get ar i] returns the term reference stored in the array [ar] at
      index [i]. This function does not check for bounds, and it is UB to use
      it with an invalid index. *)
  val unsafe_get : t -> int -> Ref.t

  (** [get ar i] returns the term reference stored in the array [ar] at index
      [i]. The exception [Invalid_argument] is raised when the index is not
      valid. *)
  val get : t -> int -> Ref.t

  (** [to_array ar] converts the array of references [ar] into an OCaml array
      of references. *)
  val to_array : t -> Ref.t array

  (** [iter f ar] runs function [f] on the references of [ar] in order. *)
  val iter : (Ref.t -> unit) -> t -> unit

  (** [make2 ()] creates a pair of two consecutive term reference. We provide
      similar functions for creating up to six consecutive term references. *)
  val make2 : unit -> Ref.t * Ref.t
  val make3 : unit -> Ref.t * Ref.t * Ref.t
  val make4 : unit -> Ref.t * Ref.t * Ref.t * Ref.t
  val make5 : unit -> Ref.t * Ref.t * Ref.t * Ref.t * Ref.t
  val make6 : unit -> Ref.t * Ref.t * Ref.t * Ref.t * Ref.t * Ref.t

  module Unsafe : sig
    val base : t -> Ref.t
  end
end

(** Representation of a Prolog term (i.e., a term reference). *)
type term = Ref.t

(** Short synonym of [term]. *)
type t = term

(** Type representing the different kinds of terms. *)
type kind =
  | Variable
  | Atom of Atom.t
  | Nil
  | Blob
  | String of string
  | Integer of int
  | Rational
  | Float of float
  | Term of Functor.t * Refs.t
  | List_pair of t * t
  | Dict

(** Exception raised when a term has an unexpected shape. *)
exception Kind_error of t * string

(** [is_variable t] indicates whether [t] is an unsassigned variable. *)
val is_variable : t -> bool

(** [is_nil t] indicates whether [t] is the empty list constructor. *)
val is_nil : t -> bool

(** [get_atom t] extracts the atom represented by term [t]. If [t] is not an
    atom, [Kind_error(t, _)] is raised. *)
val get_atom : t -> Atom.t

(** [get_string t] extracts the string represented by term [t]. If [t] is not
    a string, [Kind_error(t, _)] is raised. *)
val get_string : t -> string

(** [get_integer t] extracts the integer represented by term [t]. If [t] is
    not an integer, [Kind_error(t, _)] is raised. *)
val get_integer : t -> int

(** [get_float t] extracts the floating-point number represented by term [t].
    If [t] is not a floating-point number, [Kind_error(t, _)] is raised. *)
val get_float : t -> float

(** [get_list_pair t] extracts the list constructor represented by term [t].
    If [t] is not a list constructor, [Kind_error(t, _)] is raised. *)
val get_list_pair : t -> t * t

(** [get_functor t] extracts the functor for the compound term represented by
    [t]. If [t] is an atom, then the function also works and the arity is [0].
    If [t] is any other form of term, [Kind_error(t, _)] is raised. *)
val get_functor : t -> Functor.t

(** [get_arg t i] returns the [i]-th argument of the compound term represented
    by [t]. If [t] is not a compound term, or if [i] is not a valid index, the
    exception [Kind_error(t, _)] is raised. *)
val get_arg : t -> int -> t

(** [get_args t n] returns an array of term refs pointing to the [n] first
    arguments of the compound term represented by [t]. In the case where [t]
    is not a compound term, or if it has less than [n] arguments, exception
    [Kind_error(t, _)] is raised. *)
val get_args : t -> int -> Refs.t

(** [get_list t] returns a list of term refs corresponding to the elements of
    the list pointed to by [t]. If [t] does not correspond to a well-formed
    list, then [Kind_error(t, _)] is raised. *)
(*val get_list : t -> t list*)

(** [extract_list f t] is equivalent to [List.map f (get_list t)], but it does
    not need to allocate an intermediate list. *)
val extract_list : (t -> 'a) -> t -> 'a list

(** [kind_of t] returns the kind of term pointed to by [t], which can be used
    to easily extract data from a term. *)
val kind : t -> kind

val put_term : t -> t -> unit

val put_atom : t -> Atom.t -> unit

val put_nil : t -> unit

val put_string : t -> string -> unit

val put_integer : t -> int -> unit

val put_bool : t -> bool -> unit

val put_float : t -> float -> unit

val put_functor : t -> Functor.t -> Refs.t -> unit

val put_list_pair : t -> t -> t -> unit

val make_atom : Atom.t -> t

val make_nil : unit -> t

val make_string : string -> t

val make_integer : int -> t

val make_float : float -> t

val make_list_pair : t -> t -> t

val make_app : Functor.t -> t array -> t

val make_app_fresh_vars : Functor.t -> t

val inject_list_map : t -> (t -> 'a -> unit) -> 'a list -> unit

val inject_list : t -> (t -> unit) list -> unit

val unify : t -> t -> bool

val compare : t -> t -> int

val equal : t -> t -> bool

val same_compound : t -> t -> bool

val debug_pp : Format.formatter -> t -> unit
