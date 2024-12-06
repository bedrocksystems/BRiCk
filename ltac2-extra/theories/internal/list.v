(*
 * Copyright (C) BlueRock Security Inc. 2022-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Ltac2.Ltac2.

(** Minor extensions to [Ltac2.List]. *)
Module List.
  Import Ltac2.
  Export Ltac2.List.

  Ltac2 iteri2 (f : int -> 'a -> 'b -> unit) (xs : 'a list) (ys : 'b list) :=
    let rec loop i xs ys :=
      match (xs, ys) with
      | ([]     , []     ) => ()
      | ([]     , _      ) => Control.throw (Invalid_argument None)
      | (_      , []     ) => Control.throw (Invalid_argument None)
      | (x :: xs, y :: ys) => f i x y; loop (Int.add i 1) xs ys
      end
    in
    loop 0 xs ys.

  (** These variants avoid silly edits when switching direction. *)

  Ltac2 foldl (f : 'a -> 'b -> 'b) (xs : 'a list) (acc : 'b) : 'b :=
    List.fold_left (fun acc x => f x acc) acc xs.
  Ltac2 foldr := List.fold_right.

  Ltac2 foldli (f : int -> 'a -> 'b -> 'b) (xs : 'a list) (acc : 'b) : 'b :=
    let rec go i acc xs :=
      match xs with
      | [] => acc
      | x :: xs => go (Int.add i 1) (f i x acc) xs
      end
    in go 0 acc xs.

  Ltac2 foldl2 (f : 'a -> 'b -> 'c -> 'c)
      (xs : 'a list) (ys : 'b list) (acc : 'c) : 'c :=
    List.fold_left2 (fun acc x y => f x y acc) xs ys acc.
  Ltac2 foldr2 (f : 'a -> 'b -> 'c -> 'c)
      (xs : 'a list) (ys : 'b list) (acc : 'c) : 'c :=
    List.fold_right2 f xs ys acc.

  (** Note: We have a "smart" list mapper in ML that works in the [Proofview]
      monad and uses Caml's [==] to promote sharing.

      We cannot lift it to an external Ltac2 function [List.Smart.map] of type
      [('a -> 'a) -> 'a list -> 'a list] due to the way that Ltac2's [repr]
      for list works. Under the hood, it is roughly [List.map]. Every time a
      list crosses the FFI boundary, we get a new list.

      We could perhaps write a [List.Smart.map] function in Ltac2 by adding an
      external primitive [==] (on ML type [valexpr]). *)
End List.
