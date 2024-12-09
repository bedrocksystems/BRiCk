(*
 * Copyright (C) 2023-2024 BlueRock Security Inc.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; version 2.1.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *)

(** Type of log event / span metadata. *)
type metadata = string * JSON.t

(** Type of a log event. *)
type event = {
  metadata : metadata list (* Event metadata.  *) ;
  header   : string option (* Optional header. *) ;
  event    : JSON.t        (* Event contents.  *) ;
}

(** Type of a log span. *)
type span = {
  uid      : int           (* Span identifier. *) ;
  name     : string        (* Span name.       *) ;
  metadata : metadata list (* Span metadata. . *) ;
}

(** Type of a log item. *)
type item =
  | Span  of {
      span  : span      (** Description of the span.  *) ;
      items : item list (** Contained items.          *) ;
    }
  (** A span (i.e., section) identified by a [key], containing [items]. *)
  | Event of {
      event : event     (** Description of the event. *) ;
    }

(** Type of a log. *)
type t = item list

(** [iter fe fs log] iterates over all the events and spans of the given [log]
    in a depth-first manner. The functions [fe] and [fs] are applied to events
    and spans respectively, and receive as first argument the reversed list of
    spans traversed to get to the current item. The [fs] function also takes a
    list of contained items. *)
val iter : (span list -> event -> unit) ->
  (span list -> span -> item list -> unit) -> t -> unit

(** Exception raised by [of_json]. *)
exception Error of string

(** [of_json json] turns the given [json] data into a log. In case of failure,
    the [Error] exception is raised. *)
val of_json : JSON.t -> t
