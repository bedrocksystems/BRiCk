(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require bedrock.elpi.extra.extra.

(** Confirm that we made warnings from <<Elpi Typecheck>> fatal. *)

Elpi Program test lp:{{ }}.
Elpi Accumulate lp:{{
  undeclared_constant cats.
}}.
Fail Elpi Typecheck.


Elpi Program test2 lp:{{ }}.

Elpi Accumulate lp:{{
  type cats dogs.
  type undeclared_constant dogs -> prop.

  undeclared_constant cats.
}}.
Succeed Elpi Typecheck.
Elpi Accumulate lp:{{
  kind dogs type.	% Sadly not forced
}}.
Succeed Elpi Typecheck.
