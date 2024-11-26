(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

(** * This file contains helper functions useful for efficient term reification in elpi. *)

Require Stdlib.Numbers.BinNums.
Require Stdlib.Numbers.Cyclic.Int63.Sint63.
Require Stdlib.Strings.Byte.

Module Numbers.
  (* Elpi integers are 63 bit signed integers (at least on 64 bit machines). We
     use Coq's own primitive signed integers to efficiently convert any closed
     Coq number term directly to an Elpi-compatible integer.

     NOTE: The functions below do not check for overflow. Neither does Elpi's
     own arithmetic. The naive strategy for translating binary Coq numbers by
     repeated multiplication will yield the wrong number if the input does not
     fit into a 63 bit signed integer.

     NOTE: The conversion of [nat] is slow, even with [vm_compute]. It could be
     a legitimate strategy to go through the string presentation. *)
  Import Stdlib.Numbers.BinNums.
  Import BinInt.
  Import Stdlib.Numbers.Cyclic.Int63.Uint63.

  Definition t : Type := int.

  (* Elpi does not understand that uint63 can be interpreted as a signed
     integer. For this reason, [of_Z] needs to return a signedness bit. *)
  Definition of_Z (z : Z) : bool * t :=
    match z with
    | Z0 | Zpos _ => (true, Uint63.of_Z z)
    | Zneg p => (false, of_Z (Zpos p))
    end.

  Definition of_N (n : N) : t := Uint63.of_Z (Z.of_N n).
  Definition of_pos (p : positive) : t := of_pos p.
  Definition of_nat (n : nat) : t := of_nat n.
  Definition of_byte (b : Byte.byte) : t := of_N (Byte.to_N b).

  Definition to_pos (i : t) : positive :=
    match to_Z i with
    | Z0 | Zneg _ => 1
    | Zpos p => p
    end.

  Definition to_N (i : t) : N :=
    match to_Z i with
    | Zneg _ => N0
    | Zpos p => Npos p
    | Z0 => N0
    end.

  Definition to_byte (i : t) : Byte.byte :=
    match Byte.of_N (to_N i) with
    | Some b => b
    | None => Byte.x00
    end.

  Definition to_nat (i : t) : nat := Uint63.to_nat i.
End Numbers.
