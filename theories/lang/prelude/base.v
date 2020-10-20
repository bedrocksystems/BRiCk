(** "Prelude" for available-everywhere dependencies. *)
(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From stdpp Require Export prelude countable.
From iris.algebra Require Export base.

(** Workaround https://github.com/coq/coq/issues/4230. Taken from Software Foundations. *)
Remove Hints Bool.trans_eq_bool : core.

Global Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)
Global Set Default Proof Using "Type".
