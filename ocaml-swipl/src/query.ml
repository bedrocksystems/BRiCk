(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Internal

let asserta : ?m:Module.t -> Term.t -> unit = fun ?(m=Module.none) t ->
  let t = Term.Ref.Unsafe.repr t in
  let m = Module.Unsafe.repr m in
  if C.F._assert t m C.T._ASSERTA = 0 then prolog_error "Term.asserta"

let assertz : ?m:Module.t -> Term.t -> unit = fun ?(m=Module.none) t ->
  let t = Term.Ref.Unsafe.repr t in
  let m = Module.Unsafe.repr m in
  if C.F._assert t m C.T._ASSERTZ = 0 then prolog_error "Term.assertz"

type status =
  | True
  | Last
  | False
  | Exception

module Unsafe = struct
  type t = unit Ctypes.ptr

  let open_ : ?m:Module.t -> Pred.t -> Term.Refs.t -> t =
      fun ?(m=Module.none) p ts ->
    let m = Module.Unsafe.repr m in
    let flags = C.T._Q_NODEBUG lor C.T._Q_EXT_STATUS in
    let p = Pred.Unsafe.repr p in
    let t = Term.Ref.Unsafe.repr (Term.Refs.Unsafe.base ts) in
    let qid = C.F.open_query m flags p t in
    if Ctypes.is_null qid then prolog_error "Term.Query.Unsafe.open_"; qid

  (* If [Exception] is returned you must call [Util.clear_exception ()]. *)
  let next_solution : t -> status = fun qid ->
    match C.F.next_solution qid with
    | i when i = C.T._S_TRUE      -> True
    | i when i = C.T._S_LAST      -> Last
    | i when i = C.T._S_FALSE     -> False
    | i when i = C.T._S_EXCEPTION -> Exception
    | _                           -> assert false

  let cut : t -> unit = fun qid ->
    if C.F.cut_query qid = 0 then prolog_error "Term.Query.Unsafe.cut"

  let close : t -> unit = fun qid ->
    if C.F.close_query qid = 0 then prolog_error "Term.Query.Unsafe.close"

  let current_query : unit -> t option = fun _ ->
    let qid = C.F.current_query () in
    if Ctypes.is_null qid then None else Some(qid)

  let exception_ : t -> Term.t = fun qid ->
    let t = C.F._exception qid in
    Term.Ref.Unsafe.make t
end

type instr =
  | Continue
  | Cut
  | Close

let run_query : (status -> instr) -> ?m:Module.t -> Pred.t -> Term.Refs.t
    -> unit = fun h ?(m=Module.none) p ts ->
  let qid = Unsafe.open_ ~m p ts in
  let rec loop () =
    let s = Unsafe.next_solution qid in
    match h s with
    | Continue when s = True -> loop ()
    | Continue               -> assert false (* TODO *)
    | Cut                    -> Unsafe.cut qid
    | Close                  -> Unsafe.close qid
  in
  loop ()

exception Multiple_solutions
exception No_solution

let call_predicate : ?m:Module.t -> Pred.t -> Term.Refs.t -> unit =
    fun ?(m=Module.none) p ts ->
  let flags = C.T._Q_NODEBUG in
  let m = Module.Unsafe.repr m in
  let p = Pred.Unsafe.repr p in
  let t = Term.Ref.Unsafe.repr (Term.Refs.Unsafe.base ts) in
  if C.F.call_predicate m flags p t = 0 then
    prolog_error "Term.Query.call_predicate"

let call : ?m:Module.t -> Term.t -> unit = fun ?(m=Module.none) t ->
  let m = Module.Unsafe.repr m in
  let t = Term.Ref.Unsafe.repr t in
  if C.F.call t m = 0 then raise No_solution

(* open_string(<PROG>, STREAM), load_files(user, [stream(STREAM)]) *)
let load : ?m:Module.t -> string -> unit = fun ?(m=Module.none) prog ->
  let open Term in
  let loader prog =
    let prog = make_string prog in
    let var_STREAM = Ref.make () in
    let streams =
      let stream1 = Functor.make (Atom.make "stream") 1 in
      make_list_pair (make_app stream1 [|var_STREAM|]) (make_nil ())
    in
    let cmd1 =
      let open_string2 = Functor.make (Atom.make "open_string") 2 in
      make_app open_string2 [|prog; var_STREAM|]
    in
    let cmd2 =
      let load_files2 = Functor.make (Atom.make "load_files") 2 in
      let atom = make_atom (Atom.make "ocaml-bindings") in
      make_app load_files2 [|atom; streams|]
    in
    make_app (Functor.make (Atom.make ",") 2) [|cmd1; cmd2|]
  in
  Frame.with_closed_frame @@ fun _ -> call ~m (loader prog)
