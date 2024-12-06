(*
 * Copyright (C) BlueRock Security Inc. 2021-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Prelude

include Stdlib.List

let is_empty : 'a list -> bool = fun l ->
  l = []

let rec drop_while : ('a -> bool) -> 'a list -> 'a list = fun p l ->
  match l with
  | []      -> []
  | x :: xs -> if p x then drop_while p xs else l

let take_while : ('a -> bool) -> 'a list -> 'a list * 'a list = fun p l ->
  let rec take_while acc l =
    match l with
    | []      -> (rev acc, [])
    | x :: xs -> if p x then take_while (x :: acc) xs else (rev acc, l)
  in
  take_while [] l

let rec choose : 'a list list -> 'a list list = fun bs ->
  match bs with
  | []      -> [[]]
  | b :: bs ->
  let extend r = map (fun i -> i :: r) b in
  concat (map extend (choose bs))

let has_dups : type a. a compare -> a list -> bool = fun cmp xs ->
  let module S = Set.Make(struct type t = a let compare = cmp end) in
  let rec has_dups seen xs =
    match xs with
    | []      -> false
    | x :: xs -> S.mem x seen || has_dups (S.add x seen) xs
  in
  has_dups S.empty xs

let exists_or_empty : ('a -> bool) -> 'a list -> bool = fun p l ->
  l = [] || exists p l
