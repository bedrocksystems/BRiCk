(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** SWI-prolog embedding. *)

(** Exception raised in case of SWI-prolog failure. *)
exception Error of string

(** [initialise argv] Initialises the SWI-Prolog heap and stacks, restores the
    Prolog state, loads the system and personal initialisation files, runs the
    [initialization/1] hooks, and finally runs initialization goals registered
    using [-g goal]. Note that [argv] is expected to be of the same form as
    [Sys.argv]: [argv.(0)] should contain the program name, and other elements
    correspond to command-line arguments. The [Invalid_argument] exception is
    raised if [argv] is empty, and [Error] in raised in case of failure. Every
    hook registered via [add_initialisation_hook] is run (in the order they
    were added) before the function returns. *)
val initialise : string array -> unit

(** [add_initialisation_hook f] registers function [f] to be run right after a
    call to [initialise argv]. *)
val add_initialisation_hook : (unit -> unit) -> unit

(** [is_initialised ()] returns a boolean indicating whether the Prolog engine
    has already been initialised (see [initialise]). *)
val is_initialised : unit -> bool

(** [is_initialised_argv ()] is similar to [is_initialised ()], but it returns
    the argument vector [Some(argv)] if if the Prolog engine is initialised,
    and the value [None] otherwise. *)
val is_initialised_argv : unit -> string array option

(** [toplevel ()] Runs the goal of the [-t toplevel] switch (default prolog/0)
    and returns a boolean indicating success. *)
val toplevel : unit -> bool

(** Exception than may be raised by the [cleanup] function. *)
exception Cleanup of [`Cancelled | `Failed | `Recursive]

(** [cleanup ~no_reclaim_memory ~no_cancel ~status] cleans up the Prolog state
    (it performs the reverse of [initialise]). It runs the [PL_on_halt] and
    [at_halt/1] handlers, closes all streams (except for the standard I/O
    streams, which are flushed only), restores all signal handlers and
    reclaims all memory unless [~no_reclaim_memory] is [true]. If [~no_cancel]
    is [true] then Prolog and foreign halt hooks are not allowed to cancel the
    cleanup. In case of failure, the excepton [Cleanup(`Failed)] is raised. If
    the cleanup was cancelled, exception [Cleanup(`Cancelled)] is raised, and
    if [cleanup] was called from a hook called by the cleanup process then
    exception [Cleanup(`Recursive)] is raised.

    NOTE: this function is currently broken, do not use. For more details, see
    https://github.com/SWI-Prolog/swipl/issues/24. *)
val cleanup : no_reclaim_memory:bool -> no_cancel:bool -> status:int -> unit
