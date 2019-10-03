(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From Cpp Require Import Auto.

From Demo Require Import A_hpp_spec.

Section with_Σ.
Context {Σ:gFunctors}.

Definition A_cpp_spec : mpred Σ :=
  module empSP A__foo_spec.

End with_Σ.
