(*
 * Copyright (c) 2021-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.bi.

Module Type ERRORS.
  Section with_bi.
    Context {PROP : bi}.

    Parameter ERROR : forall {T : Type}, T -> PROP.
    Parameter UNSUPPORTED : forall {T : Type}, T -> PROP.

    Parameter ERROR_elim : forall {T} (t : T), ERROR t ⊢ False.
    Parameter UNSUPPORTED_elim : forall {T} (t : T), UNSUPPORTED t ⊢ False.
  End with_bi.
End ERRORS.

Module Errors : ERRORS.
  Section with_bi.
    Context {PROP : bi}.

    Definition ERROR : forall {T : Type}, T -> PROP :=
      fun _ _ => False%I.
    Definition UNSUPPORTED : forall {T : Type}, T -> PROP :=
      fun _ _ => False%I.

    Theorem ERROR_elim : forall {T} (t : T), ERROR t ⊢ False.
    Proof. reflexivity. Qed.
    Theorem UNSUPPORTED_elim : forall {T} (t : T), UNSUPPORTED t ⊢ False.
    Proof. reflexivity. Qed.

  End with_bi.
End Errors.

Export Errors.
