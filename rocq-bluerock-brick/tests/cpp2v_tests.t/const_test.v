(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.parser.
Require Import bedrock.lang.cpp.logic.pred.
Require Import bedrock.lang.cpp.logic.path_pred.
Require Import bedrock.lang.cpp.logic.heap_pred.
Require Import bedrock.lang.cpp.logic.operator.
Require Import bedrock.lang.cpp.logic.destroy.
Require Import bedrock.lang.cpp.logic.initializers.
Require Import bedrock.lang.cpp.logic.wp.
Require Import bedrock.lang.cpp.logic.call.
Require Import bedrock.lang.cpp.logic.string.
Require Import bedrock.lang.cpp.logic.translation_unit.
Require Import bedrock.lang.cpp.logic.dispatch.
Require Import bedrock.lang.cpp.logic.layout.
Require Import bedrock.lang.cpp.logic.const.
Require Import test.const_cpp.

#[local] Open Scope bs_scope.

Section with_Σ.

  Context `{Σ : cpp_logic}  {σ : genv.genv}.

(*
  Definition CR := const_coreR (module := module) (Tnamed "_Z1C") 1.
  (* Eval hnf in CR. *)

  Definition DR := const_coreR (module := module) (Tnamed "_Z1D") 1.
  (* Eval hnf in DR. *)
*)
End with_Σ.





