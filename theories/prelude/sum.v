(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base.

Module sum.
  Definition existsb {A B} (f : A -> bool) (g : B -> bool) (s : A + B) : bool :=
    match s with
    | inl a => f a
    | inr b => g b
    end.
End sum.
