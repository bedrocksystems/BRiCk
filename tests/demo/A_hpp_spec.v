(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Cpp.Auto.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import Cpp.Auto.
Require Demo.A_hpp.

Section with_Σ.
Context {Σ:gFunctors}.

Local Notation mpred := (mpred Σ) (only parsing).

Definition A__foo_spec : mpred := ltac:(
  specify (name "::A::foo") A_hpp.module
      uconstr:(fun x =>
         \with (y : Z)
         \pre [| x = Vint y |] ** [| has_type (y + 6) T_int |]
         \post [r] [| r = Vint (y + 6)%Z |])).

Definition A__bar_spec : mpred := ltac:(
  specify (name "::A::bar") A_hpp.module
      uconstr:(fun x =>
         \with (y : Z)
         \pre [| x = Vint y |] ** [| has_type (y + 7) T_int |]
         \post [r] [| r = Vint (y + 7)%Z |])).

Definition A_hpp_spec :=
  module A__foo_spec A__bar_spec.

End with_Σ.
