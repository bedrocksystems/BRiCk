(*
 * Copyright (C) BlueRock Security Inc. 2021-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Generic logging library. *)

open Stdlib_extra

(** Type of a module defining a type [t] that is pretty-printable and that can
    be converted to JSON. *)
module type PPJSON = sig
  include Format.PP

  (** [to_json e] returns a JSON representation of the event [e]. *)
  val to_json : t -> JSON.t
end

(** Functor for automatically extending a pretty-printable type with a trivial
    JSON conversion (embedding into a string). *)
module MakePPJSON(P : Format.PP) : PPJSON with type t = P.t

(** Specification of an event type. *)
module type EventSpec = PPJSON

(** Specification of a metadata type. *)
module type MetadataSpec = PPJSON

(** Integer metadata type. *)
module IntMetadataSpec : MetadataSpec with type t = int

(** String metadata type. *)
module StringMetadataSpec : MetadataSpec with type t = string

(** Extensible type of metadata tags. *)
module Metadata : sig
  (** Type-level representation of the [MetadataSpec] module type. *)
  type 'a spec = (module MetadataSpec with type t = 'a)

  (** Generic type of a metadata item. *)
  type t = T : {
    name : string  (* Name for the metadata. *) ;
    spec : 'a spec (* Metadata type spec.    *) ;
    data : 'a      (* The metadata itself.   *) ;
  } -> t

  (** [make name (module M) v] creates a metadata item named [name] with value
      [v], interpreted via the specification module [M]. *)
  val make : string -> 'a spec -> 'a -> t

  (** [make_int f name v] creates an integer metadata item named [name], whose
      value is obtained by computing [f v]. *)
  val make_int : ('a -> int) -> string -> 'a -> t

  (** [make_string f name v] creates an integer metadata item named [name]. It
      has [f v] as its value. *)
  val make_string : ('a -> string) -> string -> 'a -> t
end

(** Extensible type of log events. *)
module Event : sig
  (** Type-level representation of the [EventSpec] module type. *)
  type 'a spec = (module EventSpec with type t = 'a)

  (** Generic type of an event, including metadata and an optional header. *)
  type t = E : {
    metadata : Metadata.t list (* List of metadata. *) ;
    header   : string option   (* Optional header.  *) ;
    spec     : 'a spec         (* Event type spec.  *) ;
    event    : 'a              (* The event itself. *) ;
  } -> t

  (** An event recorder is a function called to register events in the log. It
      expects an optional list of [metadata], an optional [header], as well as
      the event description (type ['a]). *)
  type 'a recorder = ?metadata:Metadata.t list -> ?header:string -> 'a -> unit

  (** [record (module M)] builds an new event recorder from specification [M].
      The produced recorder can then be used to record events in the log. *)
  val make_recorder : 'a spec -> 'a recorder

  (** [set_direct_printing f] sets the function used to control whether direct
      printing of events is enabled. When it is enabled, events are printed to
      [stderr] as soon as they are declared, in text format. This mechanism is
      disabled by default, and is only intended for debugging when the program
      fails before one has a chance to output a log in the normal way. *)
  val set_direct_printing : (unit -> bool) -> unit
end

(** Type of log spans. *)
module Span : sig
  (** Type of a span. *)
  type t

  (** [uid s] gives the unique identifier associated with span [s]. *)
  val uid : t -> int

  (** [name s] gives the name of the span [s]. *)
  val name : t -> string

  (** [metadata s] gives the metadata currently associated to span [s]. *)
  val metadata : t -> Metadata.t list

  (** [push ?metadata name] creates and opens a new span with the given [name]
      and (optional) [metadata]. *)
  val push : ?metadata:Metadata.t list -> string -> t

  (** [pop s] closes the most recently opened span, expecting it to be [s]. If
      that is not the case, then the [Failure] exception is raised. It is also
      raised if no span is currently open. *)
  val pop : t -> unit

  (** [pop_until s] keeps closing spans until the span [s] is closed. In cases
      where [s] is not currently open, the [Failure] exception is raised. *)
  val pop_until : t -> unit

  (** [pop_all ()] closes all open spans. Note that using this function is not
      generally a good idea, since it can break compositionality. *)
  val pop_all : unit -> unit

  (** [update_metadata s f] updates the metadata linked to span [s], using the
      update function [f]. It receives as input the current metadata, and must
      give as output the expected new metadata. *)
  val update_metadata : t -> (Metadata.t list -> Metadata.t list) -> unit

  (** [set_start_span_hook f] sets the hook being run when a new span is first
      pushed to be [f]. Function [f] can call [update_tags] to extend metadata
      to include, e.g., timing or instruction count data. *)
  val set_start_span_hook : (t -> unit) -> unit

  (** [set_end_span_hook f] is similar to [start_span_hook], but sets the hook
      being run when a span is popped. *)
  val set_end_span_hook   : (t -> unit) -> unit
end

module Log : sig
  (** Type of a log item. *)
  type item =
    | Span  of {
        span  : Span.t    (** Description of the span.  *) ;
        items : item list (** Contained items.          *) ;
      }
    (** A span (i.e., section) identified by a [key], containing [items]. *)
    | Event of {
        event : Event.t   (** Description of the event. *) ;
      }
    (** A log [event]. *)

  (** Type of a log. *)
  type t = item list

  (** [collect ()] collects the produced log. Exception [Failure] is raised in
      the case where the log contains open spans. *)
  val collect : unit -> t

  (** [collect_debug ()] is similar to [collect ()], but it does not fail when
      there are open spans in the log. *)
  val collect_debug : unit -> t

  (** [pp ff log] prints [log] to the formatter [ff]. *)
  val pp : t Format.pp

  (** [to_json items] converts the [items] into JSON format. The produced JSON
      has a similar structure to [items] itself, and it consist in an array of
      items (using [`List]) containing events or spans, themselves represented
      as objects (using [`Assoc]). An event has a ["data"] and ["meta"] field,
      and optionally also a ["header"] field. The ["data"] field is build with
      the [to_json] function attached to the event. The ["header" field simply
      contains a string. And the ["meta"] field is an object associating names
      to values constructed using the [to_json] function of the metadata item.
      Spans have the following fields: a string ["name"], an unique identifier
      ["uid"] represented as an integer, a ["meta"] similar to that of events,
      and an ["items"] field with a [`List] of nested spans / events. Metadata
      attached to spans typically includes timing data and instruction counts.
      By convention, fields ["t0"] and ["t1"] contain integers giving the time
      (in microseconds) at the start and end of the span. Likewise, ["c0"] and
      ["c1"] contain integers giving instruction counts. *)
  val to_json : t -> JSON.t

  (** [output_text oc items] outputs the text representation of [items] (given
      by [pp]) to the output channel [oc]. *)
  val output_text : Stdlib.out_channel -> t -> unit

  (** [output_json oc items] outputs the JSON representation of [items] (given
      by [to_json]) to the output channel [oc]. *)
  val output_json : Stdlib.out_channel -> t -> unit

  (** [output_html oc items] outputs a self-contained HTML page containing the
      representation of [items] to the output channel [oc]. *)
  val output_html : Stdlib.out_channel -> t -> unit

  (** [write ?debug path] writes the log to the file at the given [path] using
      its extension to determine the target file type. When [debug] is [true],
      the log is written even if some spans are still open. Otherwise, an open
      span will result in a [Failure] exception. In case of error when dealing
      with the file system, the [Sys_error] exception may be raised. Note that
      the currently supported extensions are: ".txt", ".json" and ".html". *)
  val write : ?debug:bool -> string -> unit

  (** [write_tmp ?debug ?prefix ext] is similar to [write], but it uses a file
      from the system's temporary directory as target. The name of the written
      temporary file, whose name starts with [prefix] (["log"] by default) and
      has extension [ext] (which must start with a ["."] and be supported), is
      then returned by the function. Exception [Failure] is raised if [ext] is
      not valid or supported, and exception [Sys_error] is raised in case of a
      file system error. *)
  val write_tmp : ?debug:bool -> ?prefix:string -> string -> string

  (** [write_buffer ?debug ()] outputs the text representation of the log to a
      buffer. If [debug] is [true] then the operation succeeds even when there
      are open spans. Otherwise, open spans lead to a [Failure] exception. *)
  val write_buffer : ?debug:bool -> unit -> Buffer.t

  (** [count_events ()] returns the number of events currently in the log. *)
  val count_events : unit -> int

  (** Control over the internal logger state. *)
  module State : sig
    (** Internal state of the logger, to be saved and restored. *)
    type t

    (** [save ()] returns the representation of the current logger state. This
        state can then be later restored using [restore]. *)
    val save : unit -> t

    (** [restore s] restores the logger state [s] that was previously saved by
        a call to [save]. *)
    val restore : t -> unit
  end
end
