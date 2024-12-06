(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

exception Error of string

let error msg = raise (Error(msg))

let initialisation_hooks : (unit -> unit) list ref = ref []

(* Keeping values around (for a while). *)
module Keep : sig
  val value: 'a -> unit
  val clear : unit -> unit
end = struct
  let kept = ref []
  let value v = kept := Obj.repr v :: !kept
  let clear _ = kept := []
end

let initialise : string array -> unit = fun argv ->
  if Array.length argv < 1 then
    invalid_arg "SWI_prolog.API.initialise: missing program name.";
  let argc = Array.length argv in
  let argv = Array.to_list argv in
  let argv =
    let argv = List.map Ctypes.CArray.of_string argv in
    Keep.value argv; (* Keep the strings around to avoid deallocation. *)
    let argv = List.map Ctypes.CArray.start argv in
    let argv = Ctypes.CArray.of_list Ctypes.(ptr char) argv in
    Keep.value argv; (* Keep the array around to avoid deallocation. *)
    Ctypes.CArray.start argv
  in
  let ret = C.F.initialise argc argv in
  Keep.clear (); (* Now safe to deallocate. *)
  match ret with
  | 0 -> error "SWI-prolog initialisation failed."
  | _ ->
  let rec run_hooks hooks =
    match hooks with
    | []            -> ()
    | hook :: hooks -> run_hooks hooks; hook ()
  in
  run_hooks !initialisation_hooks

let add_initialisation_hook : (unit -> unit) -> unit = fun f ->
  initialisation_hooks := f :: !initialisation_hooks

let is_initialised : unit -> bool = fun _ ->
  let argc_p = Ctypes.(from_voidp int null) in
  let argv_p = Ctypes.(from_voidp (ptr (ptr char)) null) in
  C.F.is_initialised argc_p argv_p <> 0

let is_initialised_argv : unit -> string array option = fun _ ->
  let argc_p = Ctypes.(allocate int 0) in
  let argv_p =
    Ctypes.(allocate (ptr (ptr char)) (from_voidp (ptr char) null))
  in
  match C.F.is_initialised argc_p argv_p with
  | 0 -> None
  | _ ->
  let argc = Ctypes.(!@ argc_p) in
  let argv = Ctypes.(CArray.from_ptr (!@ argv_p) argc) in
  let get_string i =
    let p = Ctypes.CArray.unsafe_get argv i in
    Ctypes.(coerce (ptr char) string p)
  in
  Some(Array.init argc get_string)

let toplevel : unit -> bool = fun _ ->
  C.F.toplevel () <> 0

exception Cleanup of [`Cancelled | `Failed | `Recursive]

(* FIXME: see https://github.com/SWI-Prolog/swipl/issues/24. *)
let cleanup : no_reclaim_memory:bool -> no_cancel:bool -> status:int -> unit =
    fun ~no_reclaim_memory ~no_cancel ~status ->
  let cleanup_flags ~no_reclaim_memory:nr ~no_cancel:nc ~status =
    if status land C.T._CLEANUP_STATUS_MASK <> status then
      invalid_arg "SWI_prolog.API.cleanup: invalid status.";
    let nr = if nr then C.T._CLEANUP_NO_RECLAIM_MEMORY else 0 in
    let nc = if nc then C.T._CLEANUP_NO_CANCEL         else 0 in
    nr lor nc lor status
  in
  match C.F.cleanup (cleanup_flags ~no_reclaim_memory ~no_cancel ~status) with
  | i when i = C.T._CLEANUP_SUCCESS   -> ()
  | i when i = C.T._CLEANUP_CANCELED  -> raise (Cleanup(`Cancelled))
  | i when i = C.T._CLEANUP_FAILED    -> raise (Cleanup(`Failed   ))
  | i when i = C.T._CLEANUP_RECURSIVE -> raise (Cleanup(`Recursive))
  | _                                 -> assert false
