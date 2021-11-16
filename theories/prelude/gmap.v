(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From stdpp Require Export gmap mapset.
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

(* To upstream to Iris: using [mapseq_eq] directly would unfold a TC opaque
definition and interfere with TC search. *)
Lemma gset_eq `{Countable A} (X1 X2 : gset A) : X1 = X2 ↔ ∀ x, x ∈ X1 ↔ x ∈ X2.
Proof. apply mapset_eq. Qed.

(** [set_map] specialized to [gset]; avoids awkward type annotations such as
[set_map (C := gset A) (D := gset B)].
No lemmas provided, and meant to be unfolded.
*)
Definition gset_map {A B} `{Countable A, Countable B} : (A → B) → gset A → gset B :=
  set_map.
