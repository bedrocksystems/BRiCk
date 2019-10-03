(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From Cpp Require Import
     Auto.

Require RetRef.test_cpp.

Section with_Σ.
Context {Σ:gFunctors}.

Local Notation mpred := (mpred Σ) (only parsing).

Definition get_ref_spec : mpred := ltac:(
  specify (name "::get_ref") test_cpp.module
      uconstr:(fun x =>
         \with (m : val)
         \pre  _at (_eq x) (tprim T_int m)
         \post [ r ] [| r = x |] ** _at (_eq x) (tprim T_int m))).

Definition test_cpp_spec := get_ref_spec.

End with_Σ.
