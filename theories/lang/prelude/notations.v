(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

(** Alternative ASCII notations for stdpp. *)
From stdpp Require Import base.

Infix "==" := (≡) (at level 70, no associativity, only parsing) : stdpp_scope.

Infix "==@{ A }" := (≡@{A})
  (at level 70, only parsing, no associativity) : stdpp_scope.

Notation "(==)" := (≡) (only parsing) : stdpp_scope.
Notation "( X ==.)" := ( X ≡.) (only parsing) : stdpp_scope.
Notation "(.== X )" := (.≡ X ) (only parsing) : stdpp_scope.
Notation "(==@{ A } )" := (≡@{ A } ) (only parsing) : stdpp_scope.

(** For now, no ASCII notation for [≢]. *)
