(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.parser.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred
     operator
     destroy
     initializers
     wp call string
     translation_unit
     dispatch layout
     const.
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





