(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Internal

type t = Ctypes.Uintptr.t

let make : string -> t = fun name ->
  let s = Unsigned.Size_t.of_int (String.length name) in
  let a = C.F.new_atom_mbchars C.T._REP_UTF8 s name in
  if Ctypes.Uintptr.(equal a zero) then prolog_error "Term.Atom.make"; a

let to_string : t -> string =
  let len_p = Ctypes.(allocate size_t Unsigned.Size_t.zero) in
  let s_p = Ctypes.(allocate (ptr char) (from_voidp char null)) in
  fun a ->
    let flags = C.T._REP_UTF8 lor C.T._BUF_DISCARDABLE in
    let flags = Unsigned.UInt.of_int flags in
    if C.F.atom_mbchars a len_p s_p flags = 0 then
      prolog_error "Term.Atom.to_string";
    let len = Unsigned.Size_t.to_int (Ctypes.(!@ len_p)) in
    let s = Ctypes.(!@ s_p) in
    let b = Buffer.create len in
    for i = 0 to len - 1 do
      Buffer.add_char b Ctypes.(!@ (s +@ i))
    done; Buffer.contents b

let hash : t -> int =
  Ctypes.Uintptr.to_int

let equal : t -> t -> bool =
  Ctypes.Uintptr.equal

module Unsafe = struct
  external repr : t -> Ctypes.Uintptr.t = "%identity"
  external make : Ctypes.Uintptr.t -> t = "%identity"
end
