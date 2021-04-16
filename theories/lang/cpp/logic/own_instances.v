(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** NOTE FOR MAINTAINTERS: This is the central authority for controlling the
  right own instances to use.
  Currently, [mpred] is defined as [iProp], so iProp's instances for [own] are
  being exported, while monPred's instances are not.
  Once we move mpred to monPred, this file should stop exporting iProp's
  instances, and start exporting monPred's instances. *)

Require Export iris.si_logic.bi.
Require Export iris.base_logic.lib.own. (* << exporting [inG] and [gFunctors] *)
Require Export bedrock.lang.bi.own. (* << general [own]. *)

(** Own instances for iProp, currently exported **)
Require Export bedrock.lang.cpp.logic.iprop_own.

(** Own instances for monPred, currently not exported. **)
(* Require Export bedrock.lang.cpp.logic.monpred_own. *)
