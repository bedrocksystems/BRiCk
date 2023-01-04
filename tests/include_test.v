(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.semantics.

From bedrocktest Require include_hpp include_cpp.

Goal module_le include_hpp.module include_cpp.module.
Proof. vm_compute. done. Qed.
