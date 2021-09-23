(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From bedrock.prelude Require Import base wrap.
From bedrock.lang.cpp Require Import semantics.values.

Module Type val_wrapper.
  Include wrapper.
  Definition to_V : t -> val := Vn ∘ to_N.
End val_wrapper.
