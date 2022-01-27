(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From stdpp Require Import fin_maps strings.
From bedrock.prelude Require Import base bytestring.
Require Import Coq.FSets.FMapAVL.

Module IM := FMapAVL.Make OT_bs.

#[global] Instance IMR_lookup {V} : Lookup bs V (IM.Raw.t V) :=
  @IM.Raw.find _.

#[global] Instance IMR_empty {V} : Empty (IM.Raw.t V) :=
  @IM.Raw.empty _.

#[global] Instance IMR_insert {V} : Insert bs V (IM.Raw.t V) :=
  @IM.Raw.add _.

#[global] Instance IMR_map : FMap IM.Raw.t := @IM.Raw.map.

#[global] Instance IMR_merge : Merge IM.Raw.t := IM.Raw.map2.

#[global] Instance IMR_maptolist A : FinMapToList bs A (IM.Raw.t A) := IM.Raw.elements (elt := A).

#[global] Instance IMR_singleton {V} : SingletonM bs V (IM.Raw.t V) :=
  fun k v => <[ k := v ]> ∅.

#[global] Instance IMR_delete {V} : Delete bs (IM.Raw.t V) :=
  fun k m => IM.Raw.remove k m.

#[global] Instance IMR_omap : OMap IM.Raw.t := fun _ _ f =>
  IM.Raw.map_option (fun _ v => f v).


#[global] Instance IM_lookup {V} : Lookup bs V (IM.t V) :=
  @IM.find _.

#[global] Instance IM_empty {V} : Empty (IM.t V) :=
  @IM.empty _.

#[global] Instance IM_insert {V} : Insert bs V (IM.t V) :=
  @IM.add _.

#[global] Instance IM_map : FMap IM.t := @IM.map.

#[global] Instance IM_merge : Merge IM.t := IM.map2.

#[global] Instance IM_maptolist A : FinMapToList bs A (IM.t A) := IM.elements (elt := A).

#[global] Instance IM_singleton {V} : SingletonM bs V (IM.t V) :=
  fun k v => <[ k := v ]> ∅.

#[global] Instance IM_delete {V} : Delete bs (IM.t V) :=
  fun k m => IM.remove k m.

(* TODO: more efficient implementation, doing a single tree traversal (like in
stdpp), not one for lookup and one for insertion. *)
#[global] Instance IM_partial_alter {V} : PartialAlter bs V (IM.t V) :=
  fun f k m =>
  match f (m !! k) with
  | Some v => <[ k := v ]> m
  | None => delete k m
  end.

(* TODO:
- lifting of [IMR_omap].
- [FinMap bs IM.t].
(* Instance IM_omap : OMap IM.t. *)
(* Instance IM_fin_map : FinMap bs IM.t. *)
*)

Definition find_any {T} (b : bs -> T -> bool) (l : IM.t T) : bool :=
  IM.fold (λ (k : IM.key) (v : T) (acc : bool), if acc then true else b k v) l false.

Theorem find_any_ok : forall {T} b (l : IM.t T),
    if find_any b l then
      exists k v, IM.MapsTo k v l /\ b k v = true
    else
      forall k v, IM.MapsTo k v l -> b k v = false.
Proof.
  unfold find_any.
  intros. rewrite IM.fold_1.
  assert (if
   fold_left (λ (a : bool) (p : IM.key * T), if a then true else b p.1 p.2)
     (IM.elements (elt:=T) l) false
  then ∃ (k : IM.key) (v : T), SetoidList.InA (IM.eq_key_elt (elt:=T)) (k, v) (IM.elements l) ∧ b k v = true
  else ∀ (k : IM.key) (v : T), SetoidList.InA (IM.eq_key_elt (elt:=T)) (k, v) (IM.elements l) → b k v = false).
  { induction (IM.elements l); simpl; intros.
    { inversion H. }
    { destruct (b a.1 a.2) eqn:?.
      { enough (fold_left (λ (a0 : bool) (p : IM.key * T), if a0 then true else b p.1 p.2) l0 true = true) as ->.
        { do 2 eexists. split; eauto. left. split; reflexivity. }
        clear. induction l0; simpl; auto. }
      { destruct (fold_left (λ (a : bool) (p : IM.key * T), if a then true else b p.1 p.2) l0
            false).
        { destruct IHl0 as [ ? [ ? [ ? ? ] ] ].
          do 2 eexists; split; eauto. }
        { intros. inversion H; subst.
          { inversion H1; simpl in *; subst; auto. }
          { eauto. } } } } }
  { destruct (fold_left (λ (a : bool) (p : IM.key * T), if a then true else b p.1 p.2)
                        (IM.elements (elt:=T) l) false).
    { destruct H as [ k [ v [ ? ? ] ] ].
      do 2 eexists; split; eauto using IM.elements_2. }
    { intros. apply H. eauto using IM.elements_1. } }
Qed.

Fixpoint check_canon {e} (min max : option bs) (b : IM.Raw.tree e) : bool.
destruct b.
- apply true.
- refine (check_canon _ min (Some k) b1 &&
          check_canon _ (Some k) max b2 &&
          match min with
          | None => true
          | Some m => match bs_cmp m k with
                     | Lt => true
                     | _ => false
                     end
          end &&
          match max with
          | None => true
          | Some m => match bs_cmp k m with
                     | Lt => true
                     | _ => false
                     end
          end).
Defined.

#[local] Lemma check_canon_lem : forall e (b : IM.Raw.tree e) min max,
    check_canon min max b ->
    IM.Raw.bst b /\
    match min with
    | None => True
    | Some m => IM.Raw.gt_tree m b
    end /\
    match max with
    | None => True
    | Some m => IM.Raw.lt_tree m b
    end.
Proof.
  induction b; simpl; intros.
  { repeat constructor.
    - destruct min; repeat constructor.
      red. inversion 1.
    - destruct max; repeat constructor.
      red. inversion 1. }
  {  repeat match goal with
           | H : Is_true (_ && _) |- _ => eapply andb_prop_elim in H; destruct H
           end.
     specialize (IHb2 _ _ H2).
     specialize (IHb1 _ _ H).
     simpl in *.
     repeat match goal with
            | H : _ /\ _ |- _ => destruct H
            end.
     repeat constructor; eauto.
     { destruct min as [b|]; simpl in *; auto.
       red. inversion 1; subst.
       { destruct (bs_cmp b k); simpl in *; try congruence; contradiction. }
       { apply H7 in H11. auto. }
       { apply H4 in H11.
         destruct (bs_cmp b k) eqn:?; simpl in *; try contradiction.
         eapply IM.E.lt_trans; eauto. } }
     { destruct max as [b|]; simpl in *; auto.
       red. inversion 1; subst.
       { destruct (bs_cmp k b); simpl in *; try congruence; contradiction. }
       { apply H8 in H11.
         destruct (bs_cmp k b) eqn:?; simpl in *; try contradiction.
         eapply IM.E.lt_trans; eauto. }
       { apply H5; auto. } } }
Qed.

Theorem check_canon_ok : forall e (b : IM.Raw.tree e), check_canon None None b -> IM.Raw.bst b.
Proof.
  intros. apply check_canon_lem in H. tauto.
Qed.

Definition build {e} (b : IM.Raw.t e) (pf : Is_true (check_canon None None b)) :IM.t e :=
  {| IM.this := b; IM.is_bst := check_canon_ok _ _ pf |}.

(* this canonicalizes the proof *)
Definition map_canon {e} (b : IM.t e) : IM.t e :=
  match check_canon None None b.(IM.this) as X return (X -> IM.Raw.bst b.(IM.this)) -> _ with
  | true => fun x => {| IM.this := IM.this b; IM.is_bst := x I |}
  | false => fun _ => b
  end (@check_canon_ok _ b.(IM.this)).
