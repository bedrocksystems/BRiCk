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

(** Log span data gathering. Functions of this module panic on failure. *)

(** Span data. *)
module Data : sig
  (** Type of span data. *)
  type t = {
    (** Number of occurences of the span. *)
    count : int;
    (** Number of instructions spent running the span. *)
    instr : int;
  }
end

(** Span. *)
module Span : sig
  (** Type of a span. *)
  type t = {
    (** Span name. *)
    name   : string;
    (** Optional span status metadata. *)
    status : string option;
  }
end

(** Span key. *)
module Key : sig
  (** Type of span key. *)
  type t = {
    (** Path to the span (list of ancestor spans). *)
    span_path : Span.t list;
    (** The Span. *)
    span      : Span.t;
  }
end

(** Span data map module. *)
module M : Map.S with type key = Key.t

(** Type of a span data map. *)
type map = Data.t M.t

(** [accumulate key data m] extends the mapping of [key] in [m] with [data]. A
    binding of [key] does not need to exist in [m] prior to the call. *)
val accumulate : Key.t -> Data.t -> map -> map

(** [aggregate_filter f m] applies [f] to all keys in [m], and aggregates each
    mapping that ends up with the same key under this transformation. When [f]
    gives [None] on an existing mapping, it is dropped entirely. *)
val aggregate_filter : (Key.t -> Key.t option) -> map -> map

(** [add_log_data log m] extends [m] with the data from [log]. *)
val add_log_data : Log.t -> map -> map

(** [add_log_file file m] extends [m] with the data from [file], which must be
    a path to a file containing a JSON log. *)
val add_log_file : string -> map -> map

(** [add_csv_file file m] extends [m] with the data from [file], which must be
    a path to a CSV file (as produced by [output_csv]). *)
val add_csv_file : string -> map -> map

(** [output_csv oc m] outputs [m] to channel [oc] in CSV format. *)
val output_csv : Out_channel.t -> map -> unit
