(*
 * Copyright (c) 2019-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.cpp.syntax Require Import type_notations expr_notations stmt_notations.

(* TODO (JH): Look into disabling (selective) scopes *)

Module Export CodeNotations.
  Export TypeNotations.
  Export ExprNotations.
  Export StmtNotations.
End CodeNotations.

(* NOTE: The following [Section] is only used for testing purposes; if you break one of these
   tests - or add a new notation - please update things accordingly.
 *)

Section TestCodeNotations.
End TestCodeNotations.
