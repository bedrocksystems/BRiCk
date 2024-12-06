(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base.
Require Import bedrock.prelude.wrap.
Require Import bedrock.lang.cpp.semantics.values.

Module Type val_wrapper.
  Include wrapper.
  Definition to_V : t -> val := Vn ∘ to_N.
End val_wrapper.
