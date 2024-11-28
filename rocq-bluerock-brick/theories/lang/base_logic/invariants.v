(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** NOTE FOR MAINTAINTERS: This is the central authority for controlling the
  right own and invariants to use.
  Originally, [mpred] was defined as [iProp], so iProp's instances for [own],
  [inv], and [cinv] were being exported, while monPred's instances were not.
  (The instances for [own] are picked by `bedrock.lang.base_logic.own_instances`.)
  Once we moved mpred to monPred, this file stopped exporting iProp's
  instances, and started exporting monPred's instances. *)

(* General construction *)
Require Export bedrock.lang.bi.own.
Require Export bedrock.lang.bi.invariants.
Require Export bedrock.lang.bi.na_invariants.
Require Export bedrock.lang.bi.cancelable_invariants.

(* [own] instances for iProp or monPred *)
Require Export bedrock.lang.base_logic.own_instances.

(* [inv] and [cinv] instances for iProp. Currently not exported. *)
(* Require Export bedrock.lang.base_logic.iprop_invariants. *)

(* [inv] and [cinv] instances for monPred. Currently exported. *)
(* Unlike iProp's instances, which are in cpp2v-core, monPred's instances are
  here in cpp2v, due to possible patent pending problems. Once such problems are
  resolved, they should be published in cpp2v-core, or better yet, upstreamed in
  Iris. This file, then, should also be moved to cpp2v-core. *)
Require Export bedrock.lang.bi.weakly_objective.
Require Export bedrock.lang.base_logic.monpred_invariants.
