(*
 * Copyright (C) BedRock Systems Inc. 2020
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
*)
Require Export iris.bi.lib.laterable.
Set Default Proof Using "Type".

(** Replace the TC instance [big_sepL_laterable] with a version that
    does not assume [Timeless emp] when the list is empty. *)

#[global] Remove Hints big_sepL_laterable : typeclass_instances.

Class ListNonEmpty {A} (l : list A) : Prop := list_non_empty : l ≠ nil.
#[global] Hint Mode ListNonEmpty - ! : typeclass_instances.
Instance cons_non_empty {A} (x : A) l : ListNonEmpty (x :: l).
Proof. done. Qed.

Section laterable.
  Context {PROP : bi}.
  Implicit Types P : PROP.
  Implicit Types Ps : list PROP.

  Global Instance big_sepL_laterable Ps :
    TCOr (ListNonEmpty Ps) (Timeless (PROP:=PROP) emp) →
    TCForall Laterable Ps →
    Laterable ([∗] Ps).
  Proof.
    destruct 1; last exact: big_sepL_laterable.
    induction 1 as [|P Ps]; first done.
    simpl. destruct Ps as [|Ps].
    - rewrite big_sepL_nil right_id. apply _.
    - apply _.
  Qed.
End laterable.
