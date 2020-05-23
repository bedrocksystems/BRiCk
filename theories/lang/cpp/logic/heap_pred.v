(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.Morphisms.

From iris.bi Require Export monpred.
Require Import iris.proofmode.tactics.

From bedrock.lang.cpp Require Import
     semantics logic.pred logic.path_pred ast logic.wp.
Require Import bedrock.lang.cpp.logic.spec.

Set Default Proof Using "Type".

Lemma monPred_at_persistent_inv {V bi} (P : monPred V bi) :
  (∀ i, Persistent (P i)) → Persistent P.
Proof using . intros HP. constructor=> i. MonPred.unseal. apply HP. Qed.

Lemma monPred_at_timeless_inv {V sbi} (P : monPredSI V sbi) :
  (∀ i, Timeless (P i)) → Timeless P.
Proof using . intros HP. constructor=> i. MonPred.unseal. apply HP. Qed.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* representations are predicates over a location, they should be used to
   * assert properties of the heap
   *)
  Global Instance val_inhabited : Inhabited val.
  Proof using . constructor. apply (Vint 0). Qed.
  Global Instance ptr_inhabited : Inhabited ptr.
  Proof using . constructor. apply nullptr. Qed.

  Local Instance ptr_rel : SqSubsetEq ptr.
  Proof.
    unfold SqSubsetEq.
    unfold relation.
    apply eq.
  Defined.

  Local Instance ptr_rel_preorder : PreOrder (⊑@{ptr}).
  Proof using .
    unfold sqsubseteq. unfold ptr_rel.
    apply base.PreOrder_instance_0.
  Qed.

  Canonical Structure ptr_bi_index : biIndex :=
    BiIndex ptr ptr_inhabited ptr_rel ptr_rel_preorder.

  Definition Rep := monPred ptr_bi_index mpredI.
  Definition RepI := monPredI ptr_bi_index mpredI.
  Definition RepSI := monPredSI ptr_bi_index mpredSI.

  Lemma Rep_lequiv : forall (P Q : Rep),
      (forall p, P p -|- Q p) ->
      P -|- Q.
  Proof using . intros. split'; constructor; intro; rewrite H; reflexivity. Qed.

  Local Ltac solve_Rep_persistent X :=
    intros;
    rewrite X;
    constructor; apply monPred_at_persistent_inv;
    apply _.

  Local Ltac solve_Rep_timeless X :=
    intros;
    rewrite X;
    constructor; apply monPred_at_timeless_inv;
    apply _.

  Definition as_Rep (P : ptr -> mpred) : Rep := MonPred P _.

  Lemma Rep_equiv_ext_equiv : forall P Q : Rep,
      (forall x, P x -|- Q x) ->
      P -|- Q.
  Proof using .
    split; red; simpl; eapply H.
  Qed.

  Definition _offsetR_def (o : Offset) (r : Rep) : Rep :=
    as_Rep (fun base =>
              Exists to, _offset o base to ** r to).
  Definition _offsetR_aux : seal (@_offsetR_def). by eexists. Qed.
  Definition _offsetR := _offsetR_aux.(unseal).
  Definition _offsetR_eq : @_offsetR = _ := _offsetR_aux.(seal_eq).

  Global Instance _offsetR_persistent o r :
    Persistent r -> Persistent (_offsetR o r).
  Proof using . solve_Rep_persistent _offsetR_eq. Qed.
  Global Instance Proper__offsetR_entails
    : Proper (eq ==> lentails ==> lentails) _offsetR.
  Proof using .
    rewrite _offsetR_eq. unfold _offsetR_def.
    constructor. simpl. intros.
    subst. setoid_rewrite H0. reflexivity.
  Qed.

  Global Instance Proper__offsetR_equiv
    : Proper (eq ==> lequiv ==> lequiv) _offsetR.
  Proof using .
    rewrite _offsetR_eq.
    intros ?? H1 ?? H2.
    constructor. simpl.
    subst. intros. setoid_rewrite H2. reflexivity.
  Qed.

  Definition _at_def (base : Loc) (P : Rep) : mpred :=
    Exists a, base &~ a ** P a.
  Definition _at_aux : seal (@_at_def). by eexists. Qed.
  Definition _at := _at_aux.(unseal).
  Definition _at_eq : @_at = _ := _at_aux.(seal_eq).

  Global Instance _at_persistent : Persistent P -> Persistent (_at base P).
  Proof using . rewrite _at_eq. apply _. Qed.

  Global Instance _at_affine : Affine P -> Affine (_at base P).
  Proof using . rewrite _at_eq. apply _. Qed.

  Global Instance _at_timeless : Timeless P -> Timeless (_at base P).
  Proof using . rewrite _at_eq. apply _. Qed.

  Global Instance Proper__at_entails
    : Proper (lequiv ==> lentails ==> lentails) _at.
  Proof using .
    rewrite _at_eq. unfold _at_def. red. red. red.
    intros. simpl in *. setoid_rewrite H0. setoid_rewrite H.
    reflexivity.
  Qed.

  Global Instance Proper__at_lequiv
    : Proper (lequiv ==> lequiv ==> lequiv) _at.
  Proof using .
    intros x y H1 ?? H2.
    rewrite _at_eq /_at_def.
    setoid_rewrite H2. setoid_rewrite H1.
    reflexivity.
  Qed.

  Instance _at_ne: Proper (dist n ==> dist n) (_at a).
  Proof.
    red. red. intros.
    rewrite _at_eq /_at_def addr_of_eq /addr_of_def.
    apply: bi.exist_ne => p; apply: bi.sep_ne; [ solve_proper | ].
    apply H.
  Qed.

  Lemma _at_valid_loc : forall (l : Loc) R,
      _at l R -|- _at l R ** □ valid_loc l.
  Proof.
    split'.
    - rewrite _at_eq /_at_def valid_loc_eq /valid_loc_def addr_of_eq /addr_of_def /=.
      iIntros "X"; iDestruct "X" as (a) "[#L R]".
      iSplitL; iExists _; iFrame "#∗".
    - iIntros "X"; iDestruct "X" as "[A B]"; iFrame.
  Qed.

  (** Values
   * These `Rep` predicates wrap `ptsto` facts
   *)
  (* todo(gmm): make opaque *)
  Definition pureR (P : mpred) : Rep :=
    as_Rep (fun _ => P).

  Global Instance pureR_persistent (P : mpred) :
    Persistent P -> Persistent (pureR P).
  Proof using . intros. apply monPred_at_persistent_inv. apply  _. Qed.

  (* this is the primitive *)
  Definition primR_def {resolve:genv} (ty : type) q (v : val) : Rep :=
    as_Rep (fun addr => @tptsto _ _ resolve ty q addr v ** [| has_type v (drop_qualifiers ty) |]).
  Definition primR_aux : seal (@primR_def). by eexists. Qed.
  Definition primR := primR_aux.(unseal).
  Definition primR_eq : @primR = _ := primR_aux.(seal_eq).
  Arguments primR {resolve} ty q v : rename.

  Global Instance primR_timeless resolve ty q p : Timeless (primR (resolve:=resolve) ty q p).
  Proof using . solve_Rep_timeless primR_eq. Qed.

  Global Instance Proper_primR_entails
    : Proper (genv_leq ==> (=) ==> (=) ==> (=) ==> lentails) (@primR).
  Proof using .
    do 5 red; intros; subst.
    rewrite primR_eq /primR_def. constructor; simpl.
    intros. setoid_rewrite H. reflexivity.
  Qed.
  Global Instance Proper_primR_equiv
    : Proper (genv_eq ==> (=) ==> (=) ==> (=) ==> lequiv) (@primR).
  Proof using .
    do 5 red; intros; subst.
    rewrite primR_eq /primR_def. constructor; simpl.
    intros. setoid_rewrite H. reflexivity.
  Qed.

  Definition uninit_def {resolve:genv} (ty : type) q : Rep :=
    primR (resolve:=resolve) ty q Vundef.
  Definition uninit_aux : seal (@uninit_def). by eexists. Qed.
  Definition uninitR := uninit_aux.(unseal).
  Definition uninit_eq : @uninitR = _ := uninit_aux.(seal_eq).
  Arguments uninitR {resolve} ty q : rename.

  Global Instance uninit_timeless resolve ty q : Timeless (uninitR (resolve:=resolve) ty q).
  Proof using . solve_Rep_timeless uninit_eq. Qed.

  (* this means "anything, including uninitialized" *)
  Definition anyR_def {resolve} (ty : type) q : Rep :=
    as_Rep (fun addr => (Exists v, (primR (resolve:=resolve) ty q v) addr) \\//
                                                                        (uninitR (resolve:=resolve) ty q) addr).
  Definition anyR_aux : seal (@anyR_def). by eexists. Qed.
  Definition anyR := anyR_aux.(unseal).
  Definition anyR_eq : @anyR = _ := anyR_aux.(seal_eq).
  Arguments anyR {resolve} ty q : rename.

  Global Instance anyR_timeless resolve ty q : Timeless (anyR (resolve:=resolve) ty q).
  Proof using . solve_Rep_timeless anyR_eq. Qed.

  Definition tref_def (ty : type) (p : ptr) : Rep :=
    as_Rep (fun addr => [| addr = p |]).
  Definition tref_aux : seal (@tref_def). by eexists. Qed.
  Definition refR := tref_aux.(unseal).
  Definition tref_eq : @refR = _ := tref_aux.(seal_eq).

  Global Instance tref_timeless ty p : Timeless (refR ty p).
  Proof using . solve_Rep_timeless tref_eq. Qed.

  (* this is the core definition that everything will be based on.
     it is really an assertion about assembly
   *)
  Definition cptr_def (fs : function_spec) : Rep :=
    as_Rep (fun p =>
         Forall (ti : thread_info), □ (Forall vs Q,
         [| List.length vs = List.length fs.(fs_arguments) |] -*
         fs.(fs_spec) ti vs Q -* fspec ti (Vptr p) vs Q))%I.
  Definition cptr_aux : seal (@cptr_def). by eexists. Qed.
  Definition cptr := cptr_aux.(unseal).
  Definition cptr_eq : @cptr = _ := cptr_aux.(seal_eq).

  Global Instance cptr_persistent : Persistent (cptr s).
  Proof using .
    red. rewrite cptr_eq /cptr_def; intros.
    constructor; simpl; intros.
    rewrite monPred_at_persistently /=.
    rewrite bi.persistently_forall.
    apply bi.forall_mono'; red; intros.
    iIntros "#X"; iModIntro; iFrame "#".
  Qed.



  (********************* DERIVED CONCEPTS ****************************)

  Definition is_null_def : Rep :=
    as_Rep (fun addr => [| addr = nullptr |]).
  Definition is_null_aux : seal (@is_null_def). by eexists. Qed.
  Definition is_null := is_null_aux.(unseal).
  Definition is_null_eq : @is_null = _ := is_null_aux.(seal_eq).

  Global Instance is_null_persistent : Persistent (is_null).
  Proof using . solve_Rep_persistent is_null_eq. Qed.

  Definition is_nonnull_def : Rep :=
    as_Rep (fun addr => [| addr <> nullptr |]).
  Definition is_nonnull_aux : seal (@is_nonnull_def). by eexists. Qed.
  Definition is_nonnull := is_nonnull_aux.(unseal).
  Definition is_nonnull_eq : @is_nonnull = _ := is_nonnull_aux.(seal_eq).

  Global Instance is_nonnull_persistent : Persistent (is_nonnull).
  Proof using . solve_Rep_persistent is_nonnull_eq. Qed.

End with_cpp.

Global Opaque _at _offsetR primR.

Arguments anyR {_ Σ resolve} ty q : rename.
Arguments uninitR {_ Σ resolve} ty q : rename.
Arguments primR {_ Σ resolve} ty q v : rename.
Arguments refR {_ Σ} ty v : rename.


Instance Persistent_spec `{Σ:cpp_logic ti} {resolve:genv} nm s :
  Persistent (_at (Σ:=Σ) (_global (resolve:=resolve) nm) (cptr s)) := _.
