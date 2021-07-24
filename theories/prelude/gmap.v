(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From stdpp Require Export gmap.
From bedrock.prelude Require Import base.

(* TODO Remove when we bump to a version with
https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/298. *)
#[global] Arguments gset_elem_of : simpl never.
#[global] Arguments gset_empty : simpl never.
#[global] Arguments gset_singleton : simpl never.
#[global] Arguments gset_union : simpl never.
#[global] Arguments gset_intersection : simpl never.
#[global] Arguments gset_difference : simpl never.
#[global] Arguments gset_elements : simpl never.
#[global] Arguments gset_eq_dec : simpl never.
#[global] Arguments gset_countable : simpl never.
#[global] Arguments gset_equiv_dec : simpl never.
#[global] Arguments gset_elem_of_dec : simpl never.
#[global] Arguments gset_disjoint_dec : simpl never.
#[global] Arguments gset_subseteq_dec : simpl never.
#[global] Arguments gset_dom : simpl never.
