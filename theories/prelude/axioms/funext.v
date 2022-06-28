(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(*
Re-export functional extensionality axiom; this is a well-understood consistent
extension of Coq.
*)

Require Export Coq.Logic.FunctionalExtensionality.
From bedrock.prelude Require Import base.

Ltac funext := apply: functional_extensionality.
