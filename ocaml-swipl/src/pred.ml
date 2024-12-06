(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Internal

type t = unit Ctypes.ptr

let make : ?m:Module.t -> Functor.t -> t = fun ?(m=Module.none) f ->
  let p = C.F.pred f (Module.Unsafe.repr m) in
  if Ctypes.is_null p then prolog_error "Term.Pred.make"; p

module Unsafe = struct
  external repr : t -> unit Ctypes.ptr = "%identity"
  external make : unit Ctypes.ptr -> t = "%identity"
end

