(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Internal

type t = Ctypes.Uintptr.t

let make : Atom.t -> int -> t = fun name arity ->
  if arity < 1 then invalid_arg "Term.Functor.make";
  let arity = Unsigned.Size_t.of_int arity in
  let f = C.F.new_functor (Atom.Unsafe.repr name) arity in
  if Ctypes.Uintptr.(equal f zero) then prolog_error "Term.Functor.make"; f

let arity : t -> int = fun f ->
  Unsigned.Size_t.to_int (C.F.functor_arity f)

let name : t -> Atom.t = fun f ->
  Atom.Unsafe.make (C.F.functor_name f)

module Unsafe = struct
  external repr : t -> Ctypes.Uintptr.t = "%identity"
  external make : Ctypes.Uintptr.t -> t = "%identity"
end
