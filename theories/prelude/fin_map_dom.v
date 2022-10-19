(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From stdpp Require Import fin_map_dom.
From bedrock.prelude Require Import base fin_maps.
Section fin_map_dom.
  Context `{FinMapDom K M D}.
  Context {A : Type}.
  Implicit Type (m : M A).
  #[local] Set Default Proof Using "Type*".

  Lemma elem_of_map_to_list_dom m k v :
    (k, v) ∈ map_to_list m → k ∈ dom m.
  Proof. move=> /elem_of_map_to_list. apply elem_of_dom_2. Qed.
End fin_map_dom.
