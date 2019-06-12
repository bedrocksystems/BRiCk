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

Definition get_ref_spec : function_spec' :=
  SFunction (Qmut T_int) (Qmut (Tpointer (Qmut T_int)) :: nil)
      (fun x =>
         \with (m : val)
         \pre  _at (_eq x) (tprim T_int m)
         \post [ r ] [| r = x |] ** _at (_eq x) (tprim T_int m)).

Definition test_cpp_spec (resolve : _) :=
  ti_cglob' (resolve:=resolve) "_Z7get_refPi" get_ref_spec.
