(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

val asserta : ?m:Module.t -> Term.t -> unit
val assertz : ?m:Module.t -> Term.t -> unit

type status =
  | True
  | Last
  | False
  | Exception

module Unsafe : sig
  type t

  val open_ : ?m:Module.t -> Pred.t -> Term.Refs.t -> t

  (* If [Exception] is returned you must call [Util.clear_exception ()]. *)
  val next_solution : t -> status

  val cut : t -> unit

  val close : t -> unit

  val current_query : unit -> t option

  val exception_ : t -> Term.t
end

type instr =
  | Continue
  | Cut
  | Close

val run_query : (status -> instr) -> ?m:Module.t -> Pred.t
  -> Term.Refs.t -> unit

exception Multiple_solutions
exception No_solution

val call_predicate : ?m:Module.t -> Pred.t -> Term.Refs.t -> unit

val call : ?m:Module.t -> Term.t -> unit

val load : ?m:Module.t -> string -> unit
