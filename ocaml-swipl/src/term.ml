(* Copyright (C) BlueRock Security Inc. 2023
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Internal

module Ref = struct
  type t = Ctypes.Uintptr.t

  let make : unit -> t = fun _ ->
    let t = C.F.new_term_ref () in
    if Ctypes.Uintptr.(equal t zero) then prolog_error "Term.Ref.make"; t

  let reset : t -> unit = fun t ->
    if C.F.put_variable t = 0 then prolog_error "Term.Ref.reset"

  module Unsafe = struct
    external repr : t -> Ctypes.Uintptr.t = "%identity"
    external make : Ctypes.Uintptr.t -> t = "%identity"
  end
end

module Refs = struct
  type t = {
    base   : Ctypes.Uintptr.t;
    length : int;
  }

  let make : int -> t = fun n ->
    if n < 1 then invalid_arg "Term.Refs.make";
    let t = C.F.new_term_refs (Unsigned.Size_t.of_int n) in
    if Ctypes.Uintptr.(equal t zero) then prolog_error "Term.Refs.make";
    {base = t; length = n}

  let length : t -> int = fun {length; _} -> length

  module Unsafe = struct
    let base : t -> Ref.t = fun {base; _} -> base
  end

  let unsafe_get : t -> int -> Ref.t = fun {base; _} i ->
    Ctypes.Uintptr.(add base (of_int i))

  let get : t -> int -> Ref.t = fun {base; length} i ->
    if i < 0 || i >= length then invalid_arg "Term.Refs.get";
    Ctypes.Uintptr.(add base (of_int i))

  let to_array : t -> Ref.t array = fun {base; length} ->
    Array.init length (fun i -> Ctypes.Uintptr.(add base (of_int i)))

  let iter : (Ref.t -> unit) -> t -> unit = fun f {base; length} ->
    for i = 0 to length - 1 do
      f Ctypes.Uintptr.(add base (of_int i))
    done

  let make2 : unit -> Ref.t * Ref.t = fun _ ->
    let {base = t0; _} = make 2 in
    let t1 = Ctypes.Uintptr.succ t0 in
    (t0, t1)

  let make3 : unit -> Ref.t * Ref.t * Ref.t = fun _ ->
    let {base = t0; _} = make 3 in
    let t1 = Ctypes.Uintptr.succ t0 in
    let t2 = Ctypes.Uintptr.succ t1 in
    (t0, t1, t2)

  let make4 : unit -> Ref.t * Ref.t * Ref.t * Ref.t = fun _ ->
    let {base = t0; _} = make 4 in
    let t1 = Ctypes.Uintptr.succ t0 in
    let t2 = Ctypes.Uintptr.succ t1 in
    let t3 = Ctypes.Uintptr.succ t2 in
    (t0, t1, t2, t3)

  let make5 : unit -> Ref.t * Ref.t * Ref.t * Ref.t * Ref.t = fun _ ->
    let {base = t0; _} = make 5 in
    let t1 = Ctypes.Uintptr.succ t0 in
    let t2 = Ctypes.Uintptr.succ t1 in
    let t3 = Ctypes.Uintptr.succ t2 in
    let t4 = Ctypes.Uintptr.succ t3 in
    (t0, t1, t2, t3, t4)

  let make6 : unit -> Ref.t * Ref.t * Ref.t * Ref.t * Ref.t * Ref.t = fun _ ->
    let {base = t0; _} = make 6 in
    let t1 = Ctypes.Uintptr.succ t0 in
    let t2 = Ctypes.Uintptr.succ t1 in
    let t3 = Ctypes.Uintptr.succ t2 in
    let t4 = Ctypes.Uintptr.succ t3 in
    let t5 = Ctypes.Uintptr.succ t4 in
    (t0, t1, t2, t3, t4, t5)
end

type term = Ref.t

type t = term

type kind =
  | Variable
  | Atom of Atom.t
  | Nil
  | Blob
  | String of string
  | Integer of int
  | Rational
  | Float of float
  | Term of Functor.t * Refs.t
  | List_pair of t * t
  | Dict

exception Kind_error of t * string

let kind_error t msg = raise (Kind_error(t, msg))

let is_variable : t -> bool = fun t ->
  C.F.is_variable t <> 0

let is_nil : t -> bool = fun t ->
  C.F.get_nil t <> 0

let get_atom : t -> Atom.t =
  let a = Ctypes.(allocate C.T.atom_t Uintptr.zero) in
  fun t ->
    if C.F.get_atom t a = 0 then kind_error t "not an atom";
    Atom.Unsafe.make Ctypes.(!@ a)

let get_string : t -> string =
  let str = Ctypes.(allocate (ptr char) (from_voidp char null)) in
  let len = Ctypes.(allocate size_t Unsigned.Size_t.zero) in
  fun t ->
    let flags = C.T._REP_UTF8 lor C.T._BUF_DISCARDABLE lor C.T._CVT_STRING in
    let flags = Unsigned.UInt.of_int flags in
    if C.F.get_nchars t len str flags = 0 then kind_error t "not a string";
    let len = Unsigned.Size_t.to_int Ctypes.(!@ len) in
    let str = Ctypes.(!@ str) in
    String.init len (fun i -> Ctypes.(!@ (str +@ i)))

let get_integer : t -> int =
  let i = Ctypes.(allocate int 0) in
  fun t ->
    if C.F.get_integer t i = 0 then kind_error t "not an integer";
    Ctypes.(!@ i)

let get_float : t -> float =
  let d = Ctypes.(allocate float 0.0) in
  fun t ->
    if C.F.get_float t d = 0 then kind_error t "not a float";
    Ctypes.(!@ d)

let get_list_pair : t -> t * t = fun t ->
  let (hd, tl) as p = Refs.make2 () in
  if C.F.get_list t hd tl = 0 then kind_error t "not a list constructor"; p

let get_functor : t -> Functor.t =
  let f = Ctypes.(allocate uintptr_t Uintptr.zero) in
  fun t ->
    if C.F.get_functor t f = 0 then kind_error t "not a compound or atom";
    Ctypes.(!@ f)

let get_arg : t -> int -> t = fun t i ->
  if i < 0 then invalid_arg "Term.get_arg";
  let a = Ref.make () in
  let i = Unsigned.Size_t.of_int (i + 1) in
  if C.F.get_arg i t a = 0 then kind_error t "not a compound / bad index"; a

let get_args : t -> int -> Refs.t = fun t n ->
  if n < 0 then invalid_arg "Term.get_args";
  let args = Refs.make n in
  for i = 1 to n do
    let a = Refs.unsafe_get args i in
    let i = Unsigned.Size_t.of_int i in
    if C.F.get_arg i t a = 0 then kind_error t "not a compound / bad index"
  done; args

let __hd = Lazy.from_fun Ref.make
let __tl = Lazy.from_fun Ref.make
let _ =
  Embedding.add_initialisation_hook @@ fun () ->
  ignore (Lazy.force __hd);
  ignore (Lazy.force __tl)
let extract_list : (t -> 'a) -> t -> 'a list = fun f t ->
  let lazy hd = __hd in
  let lazy tl = __tl in
  let rec loop t =
    match C.F.get_list t hd tl with
    | 0 -> []
    | _ -> let hd = f hd in hd :: loop tl
  in
  loop t

let kind : t -> kind = fun t ->
  let get_compound t =
    let f = get_functor t in
    Term(f, get_args t (Functor.arity f))
  in
  let get_list_pair t =
    let (h, t) = get_list_pair t in
    List_pair(h, t)
  in
  match C.F.term_type t with
  | i when i = C.T._VARIABLE  -> Variable
  | i when i = C.T._ATOM      -> Atom(get_atom t)
  | i when i = C.T._NIL       -> Nil
  | i when i = C.T._BLOB      -> Blob
  | i when i = C.T._STRING    -> String(get_string t)
  | i when i = C.T._INTEGER   -> Integer(get_integer t)
  | i when i = C.T._RATIONAL  -> Rational
  | i when i = C.T._FLOAT     -> Float(get_float t)
  | i when i = C.T._TERM      -> get_compound t
  | i when i = C.T._LIST_PAIR -> get_list_pair t
  | i when i = C.T._DICT      -> Dict
  | _                         -> assert false

let put_term : t -> t -> unit = fun t1 t2 ->
  if C.F.put_term t1 t2 = 0 then prolog_error "Term.put_term"

let put_atom : t -> Atom.t -> unit = fun t a ->
  if C.F.put_atom t (Atom.Unsafe.repr a) = 0 then prolog_error "Term.put_atom"

let put_nil : t -> unit = fun t ->
  if C.F.put_nil t = 0 then prolog_error "Term.put_nil"

let put_string : t -> string -> unit = fun t s ->
  if C.F.put_string_chars t s = 0 then prolog_error "Term.put_string"

let put_integer : t -> int -> unit = fun t i ->
  let i = Signed.Long.of_int i in
  if C.F.put_integer t i = 0 then prolog_error "Term.put_integer"

let put_bool : t -> bool -> unit = fun t b ->
  let b = if b then 1 else 0 in
  if C.F.put_bool t b = 0 then prolog_error "Term.put_integer"

let put_float : t -> float -> unit = fun t f ->
  if C.F.put_float t f = 0 then prolog_error "Term.put_float"

let put_functor : t -> Functor.t -> Refs.t -> unit = fun t f args ->
  if Functor.arity f <> Refs.length args then invalid_arg "Term.put_functor";
  if C.F.cons_functor_v t f (Refs.Unsafe.base args) = 0 then
    prolog_error "Term.put_functor"

(* NOTE: You cannot rely on [hd] and [tl] being the head and tail of the new
   cons cell after the call, since they just become variables. *)
let put_list_pair : t -> t -> t -> unit = fun t hd tl ->
  if C.F.cons_list t hd tl = 0 then prolog_error "Term.put_list_pair"

let make_atom : Atom.t -> t = fun a ->
  let t = Ref.make () in
  put_atom t a; t

let make_nil : unit -> t = fun _ ->
  let t = Ref.make () in
  put_nil t; t

let make_string : string -> t = fun s ->
  let t = Ref.make () in
  put_string t s; t

let make_integer : int -> t = fun i ->
  let t = Ref.make () in
  put_integer t i; t

let make_float : float -> t = fun f ->
  let t = Ref.make () in
  put_float t f; t

(* See [put_list_pair] for limitations. *)
let make_list_pair : t -> t -> t = fun hd tl ->
  let t = Ref.make () in
  put_list_pair t hd tl; t

let make_app : Functor.t -> t array -> t = fun f args ->
  let t = Ref.make () in
  let ts = Refs.make (Array.length args) in
  Array.iteri (fun i arg -> put_term (Refs.get ts i) arg) args;
  put_functor t f ts; t

let make_app_fresh_vars : Functor.t -> t = fun f ->
  let t = Ref.make () in
  let ts = Refs.make (Functor.arity f) in
  put_functor t f ts; t

let __hd = Lazy.from_fun Ref.make
let __tl = Lazy.from_fun Ref.make
let _ =
  Embedding.add_initialisation_hook @@ fun () ->
  ignore (Lazy.force __hd);
  ignore (Lazy.force __tl)
let inject_list_map : t -> (t -> 'a -> unit) -> 'a list -> unit = fun t f xs ->
  let rec inject t xs =
    match xs with
    | []      -> put_nil t
    | x :: xs ->
    let lazy hd = __hd in
    let lazy tl = __tl in
    inject tl xs;
    f hd x;
    put_list_pair t hd tl
  in
  inject t xs

let __hd = Lazy.from_fun Ref.make
let __tl = Lazy.from_fun Ref.make
let _ =
  Embedding.add_initialisation_hook @@ fun () ->
  ignore (Lazy.force __hd);
  ignore (Lazy.force __tl)
let inject_list : t -> (t -> unit) list -> unit = fun t fs ->
  let rec inject t fs =
    match fs with
    | []      -> put_nil t
    | f :: fs ->
      let lazy hd = __hd in
      let lazy tl = __tl in
      inject tl fs;
      f hd;
      put_list_pair t hd tl
  in
  inject t fs

let unify : t -> t -> bool = fun t1 t2 ->
  C.F.unify t1 t2 <> 0

let compare : t -> t -> int =
  C.F.compare

let equal : t -> t -> bool = fun t1 t2 ->
  compare t1 t2 = 0

let same_compound : t -> t -> bool = fun t1 t2 ->
  C.F.same_compound t1 t2 <> 0

let rec debug_pp : Format.formatter -> t -> unit = fun ff t ->
  match kind t with
  | Variable       -> Format.fprintf ff "<variable>"
  | Atom(a)        -> Format.fprintf ff "%s" (Atom.to_string a)
  | Nil            -> Format.fprintf ff "[]"
  | Blob           -> Format.fprintf ff "<blob>"
  | String(s)      -> Format.fprintf ff "%S" s
  | Integer(i)     -> Format.fprintf ff "%i" i
  | Rational       -> Format.fprintf ff "<rational>"
  | Float(f)       -> Format.fprintf ff "%f" f
  | List_pair(h,t) -> Format.fprintf ff "(%a) :: (%a)" debug_pp h debug_pp t
  | Dict           -> Format.fprintf ff "<dict>"
  | Term(f,rs)     ->
      Format.fprintf ff "%s" (Atom.to_string (Functor.name f));
      Refs.iter (Format.fprintf ff " (%a)" debug_pp) rs
