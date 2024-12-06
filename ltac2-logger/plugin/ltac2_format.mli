(*
 * Copyright (C) BlueRock Security Inc. 2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

open Ltac2_plugin
open Tac2print

(** Interface used to implement Ltac2 [Printf]-like primitives in OCaml. *)

(** Type of components of a message. *)
type msg_item =
  | String of string
  (** String literal, or constant section of a format string. *)
  | Int    of int
  (** Integer literal. *)
  | Constr of Environ.env * Evd.evar_map * EConstr.t
  (** Coq term with its environment and evar map. *)
  | Ast    of EConstr.t
  (** Coq term to be printed in debug mode. *)
  | Ident  of Names.Id.t
  (** Coq identifier. *)
  | Msg    of msg_item list
  (** List of items. *)
  | Thunk  of (unit -> msg_item)
  (** Thunked message. *)
  | Pp     of Pp.t
  (** Message built using the [Pp] module. *)

(** Type of a message (i.e., a list of message components). *)
type msg = msg_item list

(** FFI tag form the [msg] type. *)
val msg_tag : msg Tac2dyn.Val.tag

val msg_repr : msg Tac2ffi.repr

(** [eval ~enabled print fs] is an Ltac2 term that represents (if [enabled] is
    [true]) the partial application of a printing primitive (given by [print])
    to a format string that was previously decoded as [fs]. After the produced
    term has been fully applied (to arguments specified by [fs]), a message is
    produced and fed to the [print] function. If [enabled] is not [true], then
    the produced Ltac2 term is a function that does nothing. *)
val eval : enabled:bool -> (msg -> unit) -> format list
    -> Tac2val.valexpr Proofview.tactic

(** [eval_msg fs] is an Ltac2 term representing the (partial) application of a
    format string previously decoded as [fs], to a function that turns it (and
    the specified arguments) into a [msg]. *)
val eval_msg : format list -> Tac2val.valexpr Proofview.tactic

(** [interp_escaped s] returns a copy of [s] in which escaped characters (that
    follow a ['\\']) have been interpreted. An escaped ['n'] character is thus
    replaced by the newline character ['\n'], an escaped ['t'] by ['\t'],  and
    an escaped ['\\'] by itself. If any other character appears to be escaped,
    it is dropped allong with the leading ['\\']. *)
val interp_escaped : string -> string

(** [msg_to_pp m] produces a Coq pretty-printing command from message [m]. *)
val msg_to_pp : msg -> Pp.t

(** [msg_to_string m] produces a string from message [m]. *)
val msg_to_string : msg -> string
