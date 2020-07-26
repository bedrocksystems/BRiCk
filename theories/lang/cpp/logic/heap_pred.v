(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Classes.Morphisms.

From iris.bi Require Export monpred.
Require Import iris.proofmode.tactics.
Require Import iris.bi.lib.fractional.

From bedrock Require Import ChargeUtil.
From bedrock.lang.cpp Require Import
     semantics logic.pred logic.path_pred ast logic.wp.
Require Import bedrock.lang.cpp.logic.spec.

Set Default Proof Using "Type".

Definition monPred_at_persistent_inv {V bi} (P : monPred V bi) :
  (∀ i, Persistent (P i)) → Persistent P := monPred_persistent _.

Lemma monPred_at_timeless_inv {V bi} (P : monPredI V bi) :
  (∀ i, Timeless (P i)) → Timeless P.
Proof.
  intros HP. constructor=>i.
  rewrite monPred_at_later monPred_at_except_0. apply HP.
Qed.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* representations are predicates over a location, they should be used to
   * assert properties of the heap
   *)
  Global Instance val_inhabited : Inhabited val.
  Proof. constructor. apply (Vint 0). Qed.
  Global Instance ptr_inhabited : Inhabited ptr.
  Proof. constructor. apply nullptr. Qed.

  Local Instance ptr_rel : SqSubsetEq ptr.
  Proof.
    unfold SqSubsetEq.
    unfold relation.
    apply eq.
  Defined.

  Local Instance ptr_rel_preorder : PreOrder (⊑@{ptr}).
  Proof.
    unfold sqsubseteq. unfold ptr_rel.
    apply base.PreOrder_instance_0.
  Qed.

  Canonical Structure ptr_bi_index : biIndex :=
    BiIndex ptr ptr_inhabited ptr_rel ptr_rel_preorder.

  Definition Rep := monPred ptr_bi_index mpredI.
  Definition RepI := monPredI ptr_bi_index mpredI.

  Lemma Rep_lequiv : forall (P Q : Rep),
      (forall p, P p -|- Q p) ->
      P -|- Q.
  Proof. intros. split'; constructor; intro; rewrite H; reflexivity. Qed.

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

  Lemma as_Rep_obs f P :
    (∀ p, f p |-- f p ** [| P |]) →
    as_Rep f |-- as_Rep f ** [| P |].
  Proof.
    intros Hf. constructor=>p /=. rewrite Hf{Hf}.
    by rewrite monPred_at_sep monPred_at_only_provable.
  Qed.

  Lemma Rep_equiv_ext_equiv : forall P Q : Rep,
      (forall x, P x -|- Q x) ->
      P -|- Q.
  Proof.
    split; red; simpl; eapply H.
  Qed.

  Local Instance as_Rep_fractional `{Hp : ∀ p, Fractional (λ q, P q p)} :
    Fractional (λ q, as_Rep (P q)).
  Proof.
    intros q1 q2. constructor=>p. by rewrite monPred_at_sep /= (Hp p).
  Qed.
  Global Instance as_Rep_as_fractional q
      `{Hp : ∀ p, AsFractional (P q p) (λ q, P q p) q} :
    AsFractional (as_Rep (P q)) (λ q, as_Rep (P q)) q.
  Proof. constructor. done. apply _. Qed.

  Definition _offsetR_def (o : Offset) (r : Rep) : Rep :=
    as_Rep (fun base =>
              Exists to, _offset o base to ** r to).
  Definition _offsetR_aux : seal (@_offsetR_def). by eexists. Qed.
  Definition _offsetR := _offsetR_aux.(unseal).
  Definition _offsetR_eq : @_offsetR = _ := _offsetR_aux.(seal_eq).

  Global Instance _offsetR_persistent o r :
    Persistent r -> Persistent (_offsetR o r).
  Proof. solve_Rep_persistent _offsetR_eq. Qed.
  Global Instance Proper__offsetR_entails
    : Proper (eq ==> lentails ==> lentails) _offsetR.
  Proof.
    rewrite _offsetR_eq. unfold _offsetR_def.
    constructor. simpl. intros.
    subst. setoid_rewrite H0. reflexivity.
  Qed.

  Global Instance Proper__offsetR_equiv
    : Proper (eq ==> lequiv ==> lequiv) _offsetR.
  Proof.
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
  Proof. rewrite _at_eq. apply _. Qed.

  Global Instance _at_affine : Affine P -> Affine (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.

  Global Instance _at_timeless : Timeless P -> Timeless (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.

  Global Instance Proper__at_entails
    : Proper (lequiv ==> lentails ==> lentails) _at.
  Proof.
    rewrite _at_eq. unfold _at_def. red. red. red.
    intros. simpl in *. setoid_rewrite H0. setoid_rewrite H.
    reflexivity.
  Qed.

  Global Instance Proper__at_lequiv
    : Proper (lequiv ==> lequiv ==> lequiv) _at.
  Proof.
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
      _at l R -|- _at l R ** valid_loc l.
  Proof.
    split'; last by iIntros "[$ _]".
    rewrite _at_eq /_at_def valid_loc_eq /valid_loc_def addr_of_eq /addr_of_def /=.
    iDestruct 1 as (a) "[#L R]". auto.
  Qed.

  Lemma _at_loc_rw : forall (l1 l2 : Loc) (R : Rep),
      Loc_impl l1 l2 ** _at l1 R |-- _at l2 R.
  Proof.
    intros. rewrite _at_eq /_at_def path_pred.addr_of_eq /addr_of_def.
    iIntros "[#H L]"; iDestruct "L" as (l) "[L R]".
    iExists _; iFrame "#∗".
    iApply "H". iAssumption.
  Qed.

  Lemma _at_loc_rwe : forall (l1 l2 : Loc) (R : Rep),
      Loc_equiv l1 l2 |-- (_at l1 R ∗-∗ _at l2 R).
  Proof.
    intros. iIntros "#A".
    iSplit.
    - iIntros "B". iApply _at_loc_rw. iFrame.
      unfold Loc_impl. iModIntro. iIntros (l) "H".
      iApply "A"; iAssumption.
    - iIntros "B". iApply _at_loc_rw. iFrame.
      unfold Loc_impl. iModIntro. iIntros (l) "H".
      iApply "A"; iAssumption.
  Qed.

  Lemma _at_loc_materialize : forall (l : Loc) (r : Rep),
      _at l r -|- Exists a, l &~ a ** r a.
  Proof.
    intros. by rewrite _at_eq /_at_def path_pred.addr_of_eq /addr_of_def.
  Qed.

  Lemma addr_of_valid_loc : forall l a,
      l &~ a |-- valid_loc l.
  Proof.
    intros. rewrite valid_loc_eq /valid_loc_def.
    iIntros "X"; iExists _; eauto.
  Qed.

  Lemma valid_loc_equiv : forall l, valid_loc l -|- Exists p, l &~ p.
  Proof.
    intros.
    rewrite valid_loc_eq /valid_loc_def. reflexivity.
  Qed.

  Lemma _at_emp : forall l, _at l emp -|- valid_loc l.
  Proof.
    intros. rewrite _at_loc_materialize.
    setoid_rewrite -> monPred_at_emp; eauto.
    split'; eauto with iFrame.
    - iIntros "X"; iDestruct "X" as (a) "[#A _]".
      iApply addr_of_valid_loc; eauto.
    - rewrite valid_loc_equiv.
      iIntros "X"; iDestruct "X" as (a) "#X"; iExists a; iFrame "#".
  Qed.

  Lemma _at_exists : forall (l : Loc) T (P : T -> Rep),
      _at l (Exists v : T, P v) -|- Exists v, _at l (P v).
  Proof.
    intros.
    rewrite _at_eq /_at_def.
    split'.
    - iIntros "H". iDestruct "H" as (a) "H".
      rewrite monPred_at_exist.
      iDestruct "H" as "[? H]"; iFrame "#∗".
      iDestruct "H" as (xx) "H".
      do 2 iExists _; iFrame "#∗".
    - iIntros "A"; iDestruct "A" as (v a) "[#L P]".
      iExists _; iFrame "#∗".
      rewrite monPred_at_exist. iExists _; iFrame.
  Qed.

  Lemma _at_only_provable : forall (l : Loc) (P : Prop),
      _at l [| P |] -|- [| P |] ** valid_loc l.
  Proof.
    intros. rewrite _at_loc_materialize valid_loc_equiv.
    setoid_rewrite monPred_at_only_provable.
    split'.
    { iIntros "X"; iDestruct "X" as (a) "[#L R]"; iFrame; iExists a; iFrame "#". }
    { iIntros "[L #R]"; iDestruct "R" as (p) "R"; iExists p; iFrame "#∗". }
  Qed.

  Lemma _at_pure : forall (l : Loc) (P : Prop),
      _at l (bi_pure P) -|- bi_pure P ** valid_loc l.
  Proof.
    intros. rewrite _at_loc_materialize valid_loc_equiv.
    setoid_rewrite monPred_at_pure.
    split'.
    { iIntros "X"; iDestruct "X" as (a) "[#L R]"; iFrame; iExists a; iFrame "#". }
    { iIntros "[L #R]"; iDestruct "R" as (p) "R"; iExists p; iFrame "#∗". }
  Qed.

  Lemma _at_sep (l : Loc) (P Q : Rep) :
      _at l (P ** Q) -|- _at l P ** _at l Q.
  Proof.
    rewrite !_at_loc_materialize.
    setoid_rewrite monPred_at_sep.
    split'.
    { iIntros "A"; iDestruct "A" as (p) "[#X [L R]]".
      iSplitL "L"; iExists _; iFrame "#∗". }
    { iIntros "[A B]"; iDestruct "A" as (p) "[#LA A]"; iDestruct "B" as (p') "[#LB B]".
      iExists _; iFrame "#∗".
      iDestruct (addr_of_precise with "[LA LB]") as %H;
        [ iSplit; [ iApply "LA" | iApply "LB" ] | ].
      subst; eauto. }
  Qed.

  Lemma _at_wand (l : Loc) (P Q : Rep) :
      _at l (P -* Q) |-- (_at l P -* _at l Q) ** valid_loc l.
  Proof.
    rewrite !_at_loc_materialize.
    iIntros "X"; iDestruct "X" as (a) "[#L X]".
    rewrite monPred_wand_force.
    iSplitR "L"; [ | iApply addr_of_valid_loc; iAssumption ].
    iIntros "Y".
    iDestruct "Y" as (aa) "[#L' P]".
    iExists _.
    iSplitR.
    2:{ iApply "X".
        rewrite path_pred.addr_of_eq /addr_of_def.
        iDestruct (_loc_unique with "[L L']") as "%".
        iSplitL; [ iApply "L" | iApply "L'" ].
        subst. iAssumption. }
    iAssumption.
  Qed.

  Lemma _at_offsetL_offsetR (l : Loc) (o : Offset) (r : Rep) :
      _at l (_offsetR o r) -|- _at (_offsetL o l) r.
  Proof.
    rewrite !_at_loc_materialize.
    rewrite _offsetR_eq _offsetL_eq path_pred.addr_of_eq
            /addr_of_def /_offsetR_def /_offsetL_def;
    split'; simpl.
    { iIntros "H"; iDestruct "H" as (a) "[#L X]"; iDestruct "X" as (to) "[O R]".
      iExists _. iFrame. iExists _. iFrame "#∗". }
    { iIntros "H"; iDestruct "H" as (a) "[X R]"; iDestruct "X" as (from) "[#O L]".
      iExists _; iFrame; iExists _; iFrame "#∗". }
  Qed.

  Global Instance _at_fractional (r : Qp → Rep) (l : Loc) `{!Fractional r} :
    Fractional (λ q, _at l (r q)).
  Proof.
    intros q1 q2.
    rewrite fractional _at_sep. reflexivity.
  Qed.
  Global Instance _at_as_fractional (r : Qp → Rep) q (l : Loc)
      `{!AsFractional (r q) r q} :
    AsFractional (_at l (r q)) (λ q, _at l (r q)) q.
  Proof. constructor. done. apply _. Qed.

  (** Lift observations on [Rep]'s in [RepI] to observations on [_at]
  in [mpredI].

  PDS: We could prove a variant using fancy update rather than
  entailment. *)
  Lemma _at_obs (l : Loc) (r : Rep) P :
    r |-- r ** [| P |] →
    _at l r |-- _at l r ** [| P |].
  Proof.
    move=>/monPred_in_entails Hobs. rewrite _at_eq/_at_def.
    iDestruct 1 as (p) "[Hl Hp]". iDestruct (Hobs with "Hp") as "Hp".
    rewrite monPred_at_sep monPred_at_only_provable.
    iDestruct "Hp" as "[Hp $]". auto.
  Qed.


  (** Values
   * These `Rep` predicates wrap `ptsto` facts
   *)
  (* todo(gmm): make opaque *)
  Definition pureR (P : mpred) : Rep :=
    as_Rep (fun _ => P).

  Global Instance pureR_persistent (P : mpred) :
    Persistent P -> Persistent (pureR P).
  Proof. intros. apply monPred_at_persistent_inv. apply  _. Qed.

  Global Instance pureR_objective P : Objective (pureR P).
  Proof. done. Qed.

  Lemma pureR_only_provable P : pureR [| P |] ⊣⊢ [| P |].
  Proof.
    split'.
    - rewrite (objective_objectively (pureR _)).
      rewrite monPred_objectively_unfold embed_forall.
      by rewrite (bi.forall_elim inhabitant) embed_only_provable.
    - constructor=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma pureR_obs P Q :
    P |-- P ** [| Q |] →
    pureR P |-- pureR P ** [| Q |].
  Proof. intros. exact: as_Rep_obs. Qed.

  Lemma pureR_pure P : pureR ⌜P⌝ ⊣⊢ ⌜P⌝.
  Proof.
    split'.
    - rewrite (objective_objectively (pureR _)).
      rewrite monPred_objectively_unfold embed_forall.
      by rewrite (bi.forall_elim inhabitant) embed_pure.
    - constructor=>p. by rewrite monPred_at_pure.
  Qed.
  Definition pureR_True : pureR True ⊣⊢ True := pureR_pure _.
  Definition pureR_False : pureR False ⊣⊢ False := pureR_pure _.

  Lemma _at_pureR : forall x (P : mpred),
      _at x (pureR P) -|- P ** valid_loc x.
  Proof.
    intros. rewrite _at_loc_materialize; simpl.
    split'; simpl.
    - iIntros "X"; iDestruct "X" as (a) "[#L P]"; iFrame.
      iApply addr_of_valid_loc; iApply "L".
    - rewrite valid_loc_equiv.
      iIntros "[P H]"; iDestruct "H" as (a) "#H"; iExists _; iFrame "#∗".
  Qed.


  (** [primR] *)
  Definition primR_def {resolve:genv} (ty : type) q (v : val) : Rep :=
    as_Rep (fun addr => @tptsto _ _ resolve ty q addr v ** [| has_type v (drop_qualifiers ty) |]).
  Definition primR_aux : seal (@primR_def). by eexists. Qed.
  Definition primR := primR_aux.(unseal).
  Definition primR_eq : @primR = _ := primR_aux.(seal_eq).
  Arguments primR {resolve} ty q v : rename.

  Global Instance primR_timeless resolve ty q p
    : Timeless (primR (resolve:=resolve) ty q p).
  Proof. solve_Rep_timeless primR_eq. Qed.

  Local Existing Instance tptsto_fractional.
  Global Instance primR_fractional ty v : Fractional (λ q, primR (resolve:=resolve) ty q v).
  Proof.
    intros q1 q2. rewrite primR_eq/primR_def.
    constructor; intros; rewrite !monPred_at_sep /=.
    rewrite tptsto_fractional.
    split'.
    - iIntros "[[A B] %]"; iFrame "∗%".
    - iIntros "[[A %] [B _]]"; iFrame "∗%".
  Qed.
  Global Instance primR_as_fractional ty q v :
    AsFractional (primR (resolve:=resolve) ty q v) (λ q, primR (resolve:=resolve) ty q v) q.
  Proof. constructor. done. apply _. Qed.


  Global Instance Proper_primR_entails
    : Proper (genv_leq ==> (=) ==> (=) ==> (=) ==> lentails) (@primR).
  Proof.
    do 5 red; intros; subst.
    rewrite primR_eq /primR_def. constructor; simpl.
    intros. setoid_rewrite H. reflexivity.
  Qed.
  Global Instance Proper_primR_equiv
    : Proper (genv_eq ==> (=) ==> (=) ==> (=) ==> lequiv) (@primR).
  Proof.
    do 5 red; intros; subst.
    rewrite primR_eq /primR_def. constructor; simpl.
    intros. setoid_rewrite H. reflexivity.
  Qed.

  (** Expose the typing side-condition in a [primR]. *)
  Lemma primR_has_type {σ} ty q v :
    primR (resolve:=σ) ty q v |--
    primR (resolve:=σ) ty q v ** [| has_type v (drop_qualifiers ty) |].
  Proof.
    rewrite primR_eq. constructor=>p /=.
    rewrite monPred_at_sep monPred_at_only_provable/=.
    by iIntros "[$ %]".
  Qed.

  (** [uninitR] *)
  Definition uninit_def {resolve:genv} (ty : type) q : Rep :=
    primR (resolve:=resolve) ty q Vundef.
  Definition uninit_aux : seal (@uninit_def). by eexists. Qed.
  Definition uninitR := uninit_aux.(unseal).
  Definition uninit_eq : @uninitR = _ := uninit_aux.(seal_eq).
  Arguments uninitR {resolve} ty q : rename.

  Global Instance uninitR_timeless resolve ty q
    : Timeless (uninitR (resolve:=resolve) ty q).
  Proof. solve_Rep_timeless uninit_eq. Qed.

  Global Instance Proper_uninitR_entails
    : Proper (genv_leq ==> (=) ==> (=) ==> (=) ==> lentails) (@uninitR).
  Proof using .
    do 5 red; intros; subst.
    rewrite uninit_eq /uninit_def.
    intros. setoid_rewrite H. reflexivity.
  Qed.
  Global Instance Proper_uninitR_equiv
    : Proper (genv_eq ==> (=) ==> (=) ==> (=) ==> lequiv) (@uninitR).
  Proof using .
    do 5 red; intros; subst.
    rewrite uninit_eq /uninit_def. split'; setoid_rewrite H; reflexivity.
  Qed.


  (** [anyR] this means "anything, including uninitialized" *)
  Definition anyR_def {resolve} (ty : type) q : Rep :=
    as_Rep (fun addr => (Exists v, (primR (resolve:=resolve) ty q v) addr) \\//
                                 (uninitR (resolve:=resolve) ty q) addr).
  Definition anyR_aux : seal (@anyR_def). by eexists. Qed.
  Definition anyR := anyR_aux.(unseal).
  Definition anyR_eq : @anyR = _ := anyR_aux.(seal_eq).
  Arguments anyR {resolve} ty q : rename.

  Global Instance anyR_timeless resolve ty q : Timeless (anyR (resolve:=resolve) ty q).
  Proof. solve_Rep_timeless anyR_eq. Qed.

  Definition tref_def (ty : type) (p : ptr) : Rep :=
    as_Rep (fun addr => [| addr = p |]).
  Definition tref_aux : seal (@tref_def). by eexists. Qed.
  Definition refR := tref_aux.(unseal).
  Definition tref_eq : @refR = _ := tref_aux.(seal_eq).

  Global Instance tref_timeless ty p : Timeless (refR ty p).
  Proof. solve_Rep_timeless tref_eq. Qed.

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
  Proof.
    red. rewrite cptr_eq /cptr_def; intros.
    constructor; simpl; intros.
    rewrite monPred_at_persistently /=.
    rewrite bi.persistently_forall.
    apply bi.forall_mono'; red; intros.
    iIntros "#X"; iModIntro; iFrame "#".
  Qed.

  (** object identity *)
  Definition _identity (σ : genv) (cls : globname) (mdc : option globname)
             (q : Qp) : Rep :=
    as_Rep (@identity _ _ σ cls mdc q).

  Definition _type_ptr (σ : genv) (ty : type) :=
    as_Rep (@type_ptr _ _ σ ty).
  Lemma Persistent_type_ptr : forall σ ty,
    Persistent (_type_ptr σ ty).
  Proof.
    move => σ ty; generalize (Persistent_type_ptr σ).
    rewrite /_type_ptr/as_Rep /Persistent /bi_persistently => H /=.
    apply: Build_monPred_entails => p /=.
    move: (H p ty) => ->.
    rewrite !monPred_at_persistently. auto.
  Qed.

  (********************* DERIVED CONCEPTS ****************************)

  Definition is_null_def : Rep :=
    as_Rep (fun addr => [| addr = nullptr |]).
  Definition is_null_aux : seal (@is_null_def). by eexists. Qed.
  Definition is_null := is_null_aux.(unseal).
  Definition is_null_eq : @is_null = _ := is_null_aux.(seal_eq).

  Global Instance is_null_persistent : Persistent (is_null).
  Proof. solve_Rep_persistent is_null_eq. Qed.

  Definition is_nonnull_def : Rep :=
    as_Rep (fun addr => [| addr <> nullptr |]).
  Definition is_nonnull_aux : seal (@is_nonnull_def). by eexists. Qed.
  Definition is_nonnull := is_nonnull_aux.(unseal).
  Definition is_nonnull_eq : @is_nonnull = _ := is_nonnull_aux.(seal_eq).

  Global Instance is_nonnull_persistent : Persistent (is_nonnull).
  Proof. solve_Rep_persistent is_nonnull_eq. Qed.

End with_cpp.

Global Opaque _at _offsetR primR.

Arguments anyR {_ Σ resolve} ty q : rename.
Arguments uninitR {_ Σ resolve} ty q : rename.
Arguments primR {_ Σ resolve} ty q v : rename.
Arguments refR {_ Σ} ty v : rename.


Instance Persistent_spec `{Σ:cpp_logic ti} {resolve:genv} nm s :
  Persistent (_at (Σ:=Σ) (_global (resolve:=resolve) nm) (cptr s)) := _.
