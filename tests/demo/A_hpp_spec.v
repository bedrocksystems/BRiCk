(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import Cpp.Auto.
Require Demo.A_hpp.

Definition A__foo := "_ZN1A3fooEi".
Definition A__foo_spec : function_spec :=
  SFunction (Qmut T_int) (Qmut T_int :: nil)
      (fun x =>
         \with (y : Z)
         \pre [| x = Vint y |] ** [| has_type (y + 6) T_int |]
         \post [r] [| r = Vint (y + 6)%Z |]).

Definition A__bar := "_ZN1A3barEi".
Definition A__bar_spec : function_spec :=
  SFunction (Qmut T_int) (Qmut T_int :: nil)
      (fun x =>
         \with (y : Z)
         \pre [| x = Vint y |] ** [| has_type (y + 7) T_int |]
         \post [r] [| r = Vint (y + 7)%Z |]).

Definition A_hpp_spec (resolve : _) :=
      (|> ti_cglob (resolve:=resolve) A__foo A__foo_spec) -*
          ti_cglob (resolve:=resolve) A__bar A__bar_spec.
