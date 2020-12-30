(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License. 
 * See the LICENSE-BedRock file in the repository root for details. 
 *)
From iris.bi Require Export monpred.
From iris.proofmode Require Import tactics monpred.
Require Import iris.bi.lib.fractional.
From iris_string_ident Require Import ltac2_string_ident.

Require Import bedrock.lang.prelude.base.

From bedrock.lang.cpp Require Import
     semantics logic.pred logic.path_pred ast logic.wp.
Require Import bedrock.lang.cpp.logic.spec.

(** representations are predicates over a location, they should be used to
  * assert properties of the heap
  *)
Canonical Structure ptr_bi_index : biIndex :=
  BiIndex ptr _ eq _.

(** The tactic [intros ->%ptr_rel_elim] is much faster than [intros
    ->] when introducing [p1 ⊑ p2] (when the latter works at all). *)
Lemma ptr_rel_elim (p1 p2 : ptr) : p1 ⊑ p2 → p1 = p2.
Proof. done. Qed.

Definition Rep `{Σ : cpp_logic} := monPred ptr_bi_index mpredI.
Canonical Structure RepI `{Σ : cpp_logic} := monPredI ptr_bi_index mpredI.
Canonical Structure RepO `{Σ : cpp_logic} := monPredO ptr_bi_index mpredI.

Bind Scope bi_scope with Rep.
Bind Scope bi_scope with RepI.
Bind Scope bi_scope with RepO.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  Lemma Rep_ext (P Q : Rep) :
      (forall p : ptr, P p -|- Q p) ->
      P -|- Q.
  Proof. by constructor. Qed.

  Definition as_Rep (P : ptr -> mpred) : Rep := MonPred P _.

  Global Instance as_Rep_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) as_Rep.
  Proof. intros R1 R2 HR. constructor=>p. apply HR. Qed.
  Global Instance as_Rep_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) as_Rep.
  Proof. intros R1 R2 HR. constructor=>p. apply HR. Qed.

  Global Instance as_Rep_mono :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) as_Rep.
  Proof. by constructor. Qed.
  Global Instance as_Rep_flip_mono :
    Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) as_Rep.
  Proof. by constructor. Qed.

  Global Instance as_Rep_persistent P :
    (∀ p, Persistent (P p)) → Persistent (as_Rep P).
  Proof.
    intros HP. constructor=>p. by rewrite monPred_at_persistently -HP.
  Qed.
  Global Instance as_Rep_affine P :
    (∀ p, Affine (P p)) → Affine (as_Rep P) := _.
  Global Instance as_Rep_timeless P :
    (∀ p, Timeless (P p)) → Timeless (as_Rep P).
  Proof.
    intros HP. constructor=>p.
    by rewrite monPred_at_later monPred_at_except_0 HP.
  Qed.
  Global Instance as_Rep_fractional P :
    (∀ p, Fractional (λ q, P q p)) → Fractional (λ q, as_Rep (P q)).
  Proof.
    intros HP q1 q2. constructor=>p. by rewrite monPred_at_sep /= HP.
  Qed.
  Global Instance as_Rep_as_fractional P q :
    (∀ p, AsFractional (P q p) (λ q, P q p) q) →
    AsFractional (as_Rep (P q)) (λ q, as_Rep (P q)) q.
  Proof. constructor. done. apply _. Qed.

  Lemma as_Rep_sep P Q : as_Rep (λ p, P p ** Q p) -|- as_Rep P ** as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_sep. Qed.

  Global Instance as_Rep_observe Q (P : ptr → mpred) :
    (∀ p, Observe [| Q |] (P p)) → Observe [| Q |] (as_Rep P).
  Proof.
    intros. apply monPred_observe=>p. by rewrite monPred_at_only_provable.
  Qed.
  Global Instance as_Rep_observe_2 Q (P1 P2 : ptr → mpred) :
    (∀ p, Observe2 [| Q |] (P1 p) (P2 p)) →
    Observe2 [| Q |] (as_Rep P1) (as_Rep P2).
  Proof.
    intros. apply monPred_observe_2=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma as_Rep_obs f P :
    (∀ p, f p |-- f p ** [| P |]) →
    as_Rep f |-- as_Rep f ** [| P |].
  Proof.
    intros. apply observe_elim, as_Rep_observe=>p. exact: observe_intro.
  Qed.

  Lemma Rep_wand_force (R1 R2 : Rep) p : (R1 -* R2) p -|- R1 p -* R2 p.
  Proof. split'. apply monPred_wand_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.
  Lemma Rep_impl_force (R1 R2 : Rep) p : (R1 -->> R2) p -|- R1 p -->> R2 p.
  Proof. split'. apply monPred_impl_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.

  Definition _offsetR_def (o : Offset) (r : Rep) : Rep :=
    as_Rep (fun base =>
              Exists to, _offset o base to ** r to).
  Definition _offsetR_aux : seal (@_offsetR_def). Proof. by eexists. Qed.
  Definition _offsetR := _offsetR_aux.(unseal).
  Definition _offsetR_eq : @_offsetR = _ := _offsetR_aux.(seal_eq).

  Global Instance _offsetR_ne o n : Proper (dist n ==> dist n) (_offsetR o).
  Proof. rewrite _offsetR_eq. solve_proper. Qed.
  Global Instance _offsetR_proper o : Proper ((≡) ==> (≡)) (_offsetR o).
  Proof. rewrite _offsetR_eq. solve_proper. Qed.
  Global Instance _offsetR_mono o : Proper ((⊢) ==> (⊢)) (_offsetR o).
  Proof. rewrite _offsetR_eq. solve_proper. Qed.
  Local Lemma _offsetR_mono_old : Proper (eq ==> (⊢) ==> (⊢)) _offsetR.
  Proof. solve_proper. Qed.
  Global Instance _offsetR_flip_mono o : Proper (flip (⊢) ==> flip (⊢)) (_offsetR o).
  Proof. rewrite _offsetR_eq. solve_proper. Qed.

  Global Instance _offsetR_persistent o (r : Rep) :
    Persistent r -> Persistent (_offsetR o r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  Global Instance _offsetR_affine o (r : Rep) :
    Affine r -> Affine (_offsetR o r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  Global Instance _offsetR_timeless o (r : Rep) :
    Timeless r → Timeless (_offsetR o r).
  Proof. rewrite _offsetR_eq. apply _. Qed.

  Lemma _offsetR_sep o r1 r2 :
    _offsetR o (r1 ** r2) -|- _offsetR o r1 ** _offsetR o r2.
  Proof.
    rewrite _offsetR_eq /_offsetR_def. rewrite -as_Rep_sep. f_equiv=>p.
    apply (anti_symm _).
    - iDestruct 1 as (to) "[#O [R1 R2]]".
      iSplitL "R1"; iExists to; by iFrame "O".
    - iDestruct 1 as "[R1 R2]".
      iDestruct "R1" as (to1) "[#O1 R1]". iDestruct "R2" as (to2) "[#O2 R2]".
      iDestruct (_off_functional _ _ to1 to2 with "[$]") as %->.
      iExists to2. iFrame "O1 R1 R2".
  Qed.

  Global Instance _offsetR_fractional o (r : Qp → Rep) :
    Fractional r → Fractional (λ q, _offsetR o (r q)).
  Proof. intros ? q1 q2. by rewrite fractional _offsetR_sep. Qed.
  Global Instance _offsetR_as_fractional o (r : Qp → Rep) q :
    Fractional r → AsFractional (_offsetR o (r q)) (λ q, _offsetR o (r q)) q.
  Proof. constructor. done. apply _. Qed.

  Global Instance _offsetR_observe Q o (R : Rep) :
    Observe [| Q |] R → Observe [| Q |] (_offsetR o R).
  Proof. intros. rewrite _offsetR_eq. apply _. Qed.
  Global Instance _offsetR_observe_2 Q o (R1 R2 : Rep) :
    Observe2 [| Q |] R1 R2 → Observe2 [| Q |] (_offsetR o R1) (_offsetR o R2).
  Proof.
    intros Hobs. apply observe_uncurry. rewrite -_offsetR_sep.
    apply _offsetR_observe, observe_curry, Hobs.
  Qed.

  Lemma _offsetR_obs o r P :
    r |-- r ** [| P |] →
    _offsetR o r |-- _offsetR o r ** [| P |].
  Proof.
    intros. apply observe_elim, _offsetR_observe. exact: observe_intro.
  Qed.

  Definition _at_def (base : Loc) (P : Rep) : mpred :=
    Exists a, base &~ a ** P a.
  Definition _at_aux : seal (@_at_def). Proof. by eexists. Qed.
  Definition _at := _at_aux.(unseal).
  Definition _at_eq : @_at = _ := _at_aux.(seal_eq).

  Global Instance _at_ne l : Proper (dist n ==> dist n) (_at l).
  Proof. rewrite _at_eq. solve_proper. Qed.
  Global Instance _at_proper : Proper ((≡) ==> (≡) ==> (≡)) _at.
  Proof. rewrite _at_eq. solve_proper. Qed.
  Global Instance _at_mono : Proper ((≡) ==> (⊢) ==> (⊢)) _at.
  Proof. rewrite _at_eq. solve_proper. Qed.
  Global Instance _at_flip_mono : Proper ((≡) ==> flip (⊢) ==> flip (⊢)) _at.
  Proof.
    rewrite _at_eq/_at_def=>l1 l2 HL r1 r2 HR/=. f_equiv=>a. by rewrite HL HR.
  Qed.

  Global Instance _at_persistent : Persistent P -> Persistent (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  Global Instance _at_affine : Affine P -> Affine (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  Global Instance _at_timeless : Timeless P -> Timeless (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.

  Lemma _at_valid_loc : forall (l : Loc) R,
      _at l R -|- _at l R ** valid_loc l.
  Proof.
    split'; last by iIntros "[$ _]".
    rewrite _at_eq /_at_def valid_loc_eq /valid_loc_def addr_of_eq /addr_of_def /=.
    iDestruct 1 as (a) "[#L R]". auto.
  Qed.
  Global Instance _at_valid_loc_observe l R : Observe (valid_loc l) (_at l R).
  Proof. apply: observe_intro. by rewrite -_at_valid_loc. Qed.

  Lemma _at_loc_rw : forall (l1 l2 : Loc) (R : Rep),
      Loc_impl l1 l2 ** _at l1 R |-- _at l2 R.
  Proof.
    intros. rewrite _at_eq /_at_def path_pred.addr_of_eq /addr_of_def.
    iIntros "[#H L]"; iDestruct "L" as (l) "[L R]".
    iExists _; iFrame "#∗".
    by iApply "H".
  Qed.

  Lemma _at_loc_rwe : forall (l1 l2 : Loc) (R : Rep),
      Loc_equiv l1 l2 |-- (_at l1 R ∗-∗ _at l2 R).
  Proof.
    intros. iIntros "#A".
    iSplit; iIntros "B";
      iApply _at_loc_rw; iFrame;
      iIntros "!>" (l) "H"; by iApply "A".
  Qed.

  Lemma _at_loc_materialize : forall (l : Loc) (r : Rep),
      _at l r -|- Exists a, l &~ a ** r a.
  Proof.
    intros. by rewrite _at_eq /_at_def.
  Qed.

  Lemma addr_of_valid_loc : forall l a,
      l &~ a |-- valid_loc l.
  Proof. intros. rewrite valid_loc_eq /valid_loc_def. eauto. Qed.

  Global Instance addr_of_observe_valid_loc l p :
    Observe (valid_loc l) (l &~ p).
  Proof. apply: observe_intro_persistent. apply addr_of_valid_loc. Qed.

  Lemma valid_loc_equiv : forall l, valid_loc l -|- Exists p, l &~ p.
  Proof. by rewrite valid_loc_eq. Qed.

  Lemma _at_emp : forall l, _at l emp -|- valid_loc l.
  Proof.
    intros. rewrite _at_loc_materialize valid_loc_equiv.
    setoid_rewrite monPred_at_emp.
    by setoid_rewrite bi.sep_emp.
  Qed.

  Lemma _at_exists : forall (l : Loc) T (P : T -> Rep),
      _at l (Exists v : T, P v) -|- Exists v, _at l (P v).
  Proof.
    intros. rewrite _at_eq /_at_def /=.
    setoid_rewrite monPred_at_exist. setoid_rewrite bi.sep_exist_l.
    by rewrite bi.exist_exist.
  Qed.

  Lemma _at_forall : forall (l : Loc) T (P : T -> Rep),
    _at l (Forall x, P x) |-- Forall x, _at l (P x).
  Proof.
    intros. rewrite _at_eq /_at_def /=.
    setoid_rewrite monPred_at_forall. setoid_rewrite bi.sep_forall_l.
    by rewrite bi.exist_forall.
  Qed.

  Lemma _at_only_provable : forall (l : Loc) (P : Prop),
      _at l [| P |] -|- [| P |] ** valid_loc l.
  Proof.
    intros. rewrite _at_loc_materialize valid_loc_equiv bi.sep_exist_l.
    setoid_rewrite monPred_at_only_provable.
    by setoid_rewrite bi.sep_comm at 1.
  Qed.

  Lemma _at_pure : forall (l : Loc) (P : Prop),
      _at l ([! P !]) -|- [! P !] ** valid_loc l.
  Proof.
    intros. rewrite _at_loc_materialize valid_loc_equiv bi.sep_exist_l.
    setoid_rewrite monPred_at_pure.
    by setoid_rewrite bi.sep_comm at 1.
  Qed.

  Lemma _at_and l (R1 R2 : Rep) : _at l (R1 //\\ R2) ⊣⊢ _at l R1 //\\ _at l R2.
  Proof.
    rewrite _at_eq/_at_def -bi.exist_and_agree.
    { f_equiv=> p. by rewrite monPred_at_and. }
    apply path_pred.addr_of_precise.
  Qed.

  Lemma _at_sep (l : Loc) (P Q : Rep) :
      _at l (P ** Q) -|- _at l P ** _at l Q.
  Proof.
    rewrite _at_eq/_at_def -bi.exist_sep_agree.
    { f_equiv=> p. by rewrite monPred_at_sep. }
    apply path_pred.addr_of_precise.
  Qed.

  Lemma _at_or (l : Loc) (P Q : Rep) : _at l (P \\// Q) -|- _at l P \\// _at l Q.
  Proof.
    rewrite _at_eq /_at_def /=.
    rewrite -bi.or_exist; f_equiv=> p.
    by rewrite monPred_at_or -bi.sep_or_l.
  Qed.

  Lemma _at_wand (l : Loc) (P Q : Rep) :
      _at l (P -* Q) |-- (_at l P -* _at l Q) ** valid_loc l.
  Proof.
    rewrite !_at_loc_materialize.
    iDestruct 1 as (a) "[#L X]".
    rewrite monPred_wand_force.
    iSplitR "L"; [ | by iApply addr_of_valid_loc ].
    iDestruct 1 as (aa) "[#L' P]".
    iExists _.
    iSplitR.
    2:{ iApply "X".
        rewrite path_pred.addr_of_eq.
        by iDestruct (_loc_unique _ _ aa with "[$L $L']") as %->. }
    iAssumption.
  Qed.

  Lemma _at_pers (l : Loc) R : _at l (<pers> R) |-- <pers> _at l R.
  Proof.
    rewrite !_at_loc_materialize.
    iIntros "z"; iDestruct "z" as (a) "[#b c]"; iExists a; iFrame.
    rewrite monPred_at_persistently.
      by iSplitL "b".
  Qed.

  Lemma _at_fupd (l : Loc) R E1 E2 : _at l (|={E1,E2}=> R) |-- |={E1,E2}=> _at l R.
  Proof.
    rewrite _at_eq/_at_def.
    setoid_rewrite monPred_at_fupd.
    iIntros "a".
    iDestruct "a" as (a) "[? >c]".
    iModIntro; iExists a; iFrame.
  Qed.

  Lemma _at_offsetL_offsetR (l : Loc) (o : Offset) (r : Rep) :
      _at l (_offsetR o r) -|- _at (_offsetL o l) r.
  Proof.
    rewrite !_at_loc_materialize.
    rewrite _offsetR_eq _offsetL_eq path_pred.addr_of_eq
            /addr_of_def /_offsetR_def /_offsetL_def;
    split'; simpl.
    { iDestruct 1 as (a) "[#L X]"; iDestruct "X" as (to) "[O R]". eauto. }
    { iDestruct 1 as (a) "[X R]"; iDestruct "X" as (from) "[#O L]". eauto. }
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

  Global Instance _at_observe_only_provable Q l (R : Rep) :
    Observe [| Q |] R → Observe [| Q |] (_at l R).
  Proof. rewrite _at_eq. apply _. Qed.
  Global Instance _at_observe_2_only_provable Q l (R1 R2 : Rep) :
    Observe2 [| Q |] R1 R2 → Observe2 [| Q |] (_at l R1) (_at l R2).
  Proof.
    intros Hobs. apply observe_uncurry. rewrite -_at_sep.
    apply _at_observe_only_provable, observe_curry, Hobs.
  Qed.

  Lemma _at_obs (l : Loc) (r : Rep) P :
    r |-- r ** [| P |] →
    _at l r |-- _at l r ** [| P |].
  Proof. intros. apply observe_elim, _at_observe_only_provable. exact: observe_intro. Qed.

  (** Values
   * These `Rep` predicates wrap `ptsto` facts
   *)
  (* todo(gmm): make opaque *)
  Definition pureR (P : mpred) : Rep :=
    as_Rep (fun _ => P).

  Global Instance pureR_ne : NonExpansive pureR.
  Proof. solve_proper. Qed.
  Global Instance pureR_proper : Proper ((≡) ==> (≡)) pureR.
  Proof. solve_proper. Qed.
  Global Instance pureR_mono : Proper ((⊢) ==> (⊢)) pureR.
  Proof. by constructor. Qed.
  Global Instance pureR_flip_momo : Proper (flip (⊢) ==> flip (⊢)) pureR.
  Proof. by constructor. Qed.

  Global Instance pureR_persistent (P : mpred) :
    Persistent P -> Persistent (pureR P).
  Proof. apply _. Qed.
  Global Instance pureR_affine (P : mpred) :
    Affine P -> Affine (pureR P).
  Proof. apply _. Qed.
  Global Instance pureR_timeless (P : mpred) :
    Timeless P → Timeless (pureR P).
  Proof. apply _. Qed.
  Global Instance pureR_fractional (P : Qp → mpred) :
    Fractional P → Fractional (λ q, pureR (P q)).
  Proof. apply _. Qed.
  Global Instance pureR_as_fractional P Φ q :
    AsFractional P Φ q →
    AsFractional (pureR P) (λ q, pureR (Φ q)) q.
  Proof. intros [??]. constructor. done. apply _. Qed.

  Global Instance pureR_objective P : Objective (pureR P).
  Proof. done. Qed.

  Lemma pureR_persistently P : pureR (<pers> P) -|- <pers> pureR P.
  Proof. constructor=>p /=. by rewrite monPred_at_persistently. Qed.

  Lemma pureR_only_provable P : pureR [| P |] ⊣⊢ [| P |].
  Proof.
    split'.
    - rewrite (objective_objectively (pureR _)).
      rewrite monPred_objectively_unfold embed_forall.
      by rewrite (bi.forall_elim inhabitant) embed_only_provable.
    - constructor=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma pureR_sep (P Q : mpred) : pureR (P ** Q) -|- pureR P ** pureR Q.
  Proof. exact: as_Rep_sep. Qed.

  Global Instance pureR_observe Q (P : mpred) :
    Observe [| Q |] P → Observe [| Q |] (pureR P).
  Proof. apply _. Qed.
  Global Instance pureR_observe_2 Q (P1 P2 : mpred) :
    Observe2 [| Q |] P1 P2 → Observe2 [| Q |] (pureR P1) (pureR P2).
  Proof. apply _. Qed.

  Lemma pureR_obs P Q :
    P |-- P ** [| Q |] →
    pureR P |-- pureR P ** [| Q |].
  Proof. intros. apply observe_elim, pureR_observe. exact: observe_intro. Qed.

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
    intros. rewrite _at_loc_materialize/= valid_loc_equiv bi.sep_exist_l.
    by setoid_rewrite bi.sep_comm at 1.
  Qed.

  (** As this isn't syntax-directed, we conservatively avoid
      registering it as an instance (which could slow down
      observations). It's handy under [Local Existing Instance
      _at_observe_pureR] to project a [pureR Q] conjunct out of
      representation predicates. *)
  Lemma _at_observe_pureR Q (l : Loc) (R : Rep) :
    Observe (pureR Q) R → Observe Q (_at l R).
  Proof.
    rewrite /Observe=>->. rewrite -pureR_persistently _at_pureR.
    exact: bi.sep_elim_l.
  Qed.

  (** [primR]: the argument pointer points to an initialized value [v] of C++ type [ty]. *)
  Definition primR_def {resolve:genv} (ty : type) (q : Qp) (v : val) : Rep :=
    as_Rep (fun addr => @tptsto _ _ resolve ty q addr v ** [| has_type v (drop_qualifiers ty) |]).
  Definition primR_aux : seal (@primR_def). Proof. by eexists. Qed.
  Definition primR := primR_aux.(unseal).
  Definition primR_eq : @primR = _ := primR_aux.(seal_eq).
  Arguments primR {resolve} ty q v : rename.

  Global Instance primR_proper :
    Proper (genv_eq ==> (=) ==> (=) ==> (=) ==> lequiv) (@primR).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite primR_eq/primR_def. by setoid_rewrite Hσ.
  Qed.
  Global Instance primR_mono :
    Proper (genv_leq ==> (=) ==> (=) ==> (=) ==> (⊢)) (@primR).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite primR_eq/primR_def. by setoid_rewrite Hσ.
  Qed.

  Global Instance primR_affine resolve ty q p
    : Affine (primR (resolve:=resolve) ty q p).
  Proof. rewrite primR_eq. apply _. Qed.
  Global Instance primR_timeless resolve ty q p
    : Timeless (primR (resolve:=resolve) ty q p).
  Proof. rewrite primR_eq. apply _. Qed.

  Global Instance primR_fractional resolve ty v :
    Fractional (λ q, primR (resolve:=resolve) ty q v).
  Proof. rewrite primR_eq. apply _. Qed.
  Global Instance primR_as_fractional resolve ty q v :
    AsFractional (primR (resolve:=resolve) ty q v) (λ q, primR (resolve:=resolve) ty q v) q.
  Proof. constructor. done. apply _. Qed.

  Global Instance primR_observe_frac_valid resolve ty (q : Qp) v :
    Observe [| q ≤ 1 |]%Qc (primR (resolve:=resolve) ty q v).
  Proof. rewrite primR_eq. apply _. Qed.

  Global Instance primR_observe_agree resolve ty q1 q2 v1 v2 :
    Observe2 [| v1 = v2 |]
      (primR (resolve:=resolve) ty q1 v1)
      (primR (resolve:=resolve) ty q2 v2).
  Proof. rewrite primR_eq. apply _. Qed.

  Global Instance primR_observe_has_type resolve ty q v :
    Observe [| has_type v (drop_qualifiers ty) |] (primR (resolve:=resolve) ty q v).
  Proof. rewrite primR_eq. apply _. Qed.

  Lemma primR_has_type {σ} ty q v :
    primR (resolve:=σ) ty q v |--
    primR (resolve:=σ) ty q v ** [| has_type v (drop_qualifiers ty) |].
  Proof. apply: observe_elim. Qed.

  (**
  [uninitR]: the argument pointer points to an uninitialized value [Vundef] of C++ type [ty].
  Unlike [primR], does not imply [has_type]. *)
  Definition uninitR_def {resolve:genv} (ty : type) (q : Qp) : Rep :=
    as_Rep (fun addr => @tptsto _ _ resolve ty q addr Vundef).
  Definition uninitR_aux : seal (@uninitR_def). Proof. by eexists. Qed.
  Definition uninitR := uninitR_aux.(unseal).
  Definition uninitR_eq : @uninitR = _ := uninitR_aux.(seal_eq).
  Arguments uninitR {resolve} ty q : rename.

  Global Instance uninitR_proper
    : Proper (genv_eq ==> (=) ==> (=) ==> (=) ==> lequiv) (@uninitR).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite uninitR_eq/uninitR_def. by setoid_rewrite Hσ.
  Qed.
  Global Instance uninitR_mono
    : Proper (genv_leq ==> (=) ==> (=) ==> (=) ==> lentails) (@uninitR).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite uninitR_eq/uninitR_def. by setoid_rewrite Hσ.
  Qed.

  Global Instance uninitR_affine resolve ty q
    : Affine (uninitR (resolve:=resolve) ty q).
  Proof. rewrite uninitR_eq. apply _. Qed.
  Global Instance uninitR_timeless resolve ty q
    : Timeless (uninitR (resolve:=resolve) ty q).
  Proof. rewrite uninitR_eq. apply _. Qed.

  Global Instance uninitR_fractional resolve ty :
    Fractional (uninitR (resolve:=resolve) ty).
  Proof. rewrite uninitR_eq. apply _. Qed.
  Global Instance unintR_as_fractional resolve ty q :
    AsFractional (uninitR (resolve:=resolve) ty q) (uninitR (resolve:=resolve) ty) q.
  Proof. constructor. done. apply _. Qed.

  Global Instance uninitR_observe_frac_valid resolve ty (q : Qp) :
    Observe [| q ≤ 1 |]%Qc (uninitR (resolve:=resolve) ty q).
  Proof. rewrite uninitR_eq. apply _. Qed.

  (** This seems odd, but it's relevant to proof that [anyR] is fractional. *)
  Lemma primR_uninitR {resolve} ty q1 q2 v :
    primR (resolve:=resolve) ty q1 v |--
    uninitR (resolve:=resolve) ty q2 -*
    primR (resolve:=resolve) ty (q1 + q2) Vundef.
  Proof.
    rewrite primR_eq/primR_def uninitR_eq/uninitR_def. constructor=>p /=.
    rewrite monPred_at_wand. iIntros "[T1 %]" (? <-%ptr_rel_elim) "/= T2".
    iDestruct (observe_2 [|v = Vundef|] with "T1 T2") as %->. iFrame "T1 T2 %".
  Qed.

  (** [anyR] The argument pointers points to a value of C++ type [ty] that might be
  uninitialized. *)
  Definition anyR_def {resolve} (ty : type) (q : Qp) : Rep :=
    as_Rep (fun addr => (Exists v, (primR (resolve:=resolve) ty q v) addr) \\//
                                 (uninitR (resolve:=resolve) ty q) addr).
  Definition anyR_aux : seal (@anyR_def). Proof. by eexists. Qed.
  Definition anyR := anyR_aux.(unseal).
  Definition anyR_eq : @anyR = _ := anyR_aux.(seal_eq).
  Arguments anyR {resolve} ty q : rename.

  Global Instance anyR_affine resolve ty q : Affine (anyR (resolve:=resolve) ty q).
  Proof. rewrite anyR_eq. apply _. Qed.
  Global Instance anyR_timeless resolve ty q : Timeless (anyR (resolve:=resolve) ty q).
  Proof. rewrite anyR_eq. apply _. Qed.
  Global Instance anyR_fractional resolve ty :
    Fractional (anyR (resolve:=resolve) ty).
  Proof.
    rewrite anyR_eq /anyR_def. intros q1 q2.
    rewrite -as_Rep_sep. f_equiv=>p. split'.
    { iDestruct 1 as "[V|U]".
      - iDestruct "V" as (v) "[V1 V2]".
        iSplitL "V1"; iLeft; iExists v; [iFrame "V1"|iFrame "V2"].
      - iDestruct "U" as "[U1 U2]".
        iSplitL "U1"; iRight; [iFrame "U1"|iFrame "U2"]. }
    iDestruct 1 as "[[V1|U1] [V2|U2]]".
    - iDestruct "V1" as (v1) "V1". iDestruct "V2" as (v2) "V2".
      iDestruct (observe_2 [| v1 = v2 |] with "V1 V2") as %->.
      iLeft. iExists v2. rewrite primR_fractional monPred_at_sep. iFrame "V1 V2".
    - iDestruct "V1" as (v) "V1".
      iDestruct (primR_uninitR with "V1 U2") as "V".
      iLeft. iExists _. iFrame "V".
    - iDestruct "V2" as (v) "V2".
      iDestruct (primR_uninitR with "V2 U1") as "V".
      iLeft. iExists _. rewrite comm_L. iFrame "V".
    - iRight. rewrite uninitR_fractional monPred_at_sep. iFrame "U1 U2".
  Qed.
  Global Instance anyR_as_fractional resolve ty q :
    AsFractional (anyR (resolve:=resolve) ty q) (anyR (resolve:=resolve) ty) q.
  Proof. exact: Build_AsFractional. Qed.

  Global Instance anyR_observe_frac_valid resolve ty (q : Qp) :
    Observe [| q ≤ 1 |]%Qc (anyR (resolve:=resolve) ty q).
  Proof. rewrite anyR_eq. apply _. Qed.

  Definition refR_def (ty : type) (p : ptr) : Rep :=
    as_Rep (fun addr => [| addr = p |]).
  Definition refR_aux : seal (@refR_def). Proof. by eexists. Qed.
  Definition refR := refR_aux.(unseal).
  Definition refR_eq : @refR = _ := refR_aux.(seal_eq).

  Global Instance refR_persistent ty p : Persistent (refR ty p).
  Proof. rewrite refR_eq. apply _. Qed.
  Global Instance refR_affine ty p : Affine (refR ty p).
  Proof. rewrite refR_eq. apply _. Qed.
  Global Instance refR_timeless ty p : Timeless (refR ty p).
  Proof. rewrite refR_eq. apply _. Qed.

  (* this is the core definition that everything will be based on.
     it is really an assertion about assembly
   *)
  Definition cptr_def {resolve : genv} (fs : function_spec) : Rep :=
    as_Rep (fun p =>
         Forall (ti : thread_info), □ (Forall vs Q,
         [| List.length vs = List.length fs.(fs_arguments) |] -*
         fs.(fs_spec) ti vs Q -*
         fspec resolve.(genv_tu).(globals) (type_of_spec fs) ti (Vptr p) vs Q)).
  Definition cptr_aux : seal (@cptr_def). Proof. by eexists. Qed.
  Definition cptr := cptr_aux.(unseal).
  Definition cptr_eq : @cptr = _ := cptr_aux.(seal_eq).

  #[global] Instance cptr_persistent {resolve} : Persistent (cptr resolve s).
  Proof. rewrite cptr_eq. apply _. Qed.

  (* TODO: Proper wrt [genv_leq]. *)
  #[global] Instance cptr_mono {resolve} : Proper (flip fs_entails ==> (⊢)) (@cptr resolve).
  Proof.
    intros ??; rewrite /flip /fs_entails /fs_impl cptr_eq/cptr_def; intros Heq.
    constructor => p /=.
    f_equiv=>ti; f_equiv; f_equiv => vs; f_equiv => Q.
    iIntros "Hcptr -> Hy".
    iDestruct Heq as "(%Hspec & #Hyx)"; rewrite Hspec.
    iApply ("Hcptr" with "[%] (Hyx Hy)").
    exact: length_type_of_spec.
  Qed.

  #[global] Instance cptr_flip_mono {resolve} : Proper (fs_entails ==> flip (⊢)) (@cptr resolve).
  Proof. by intros ?? <-. Qed.

  #[global] Instance cptr_proper {resolve} : Proper ((≡) ==> (⊣⊢)) (@cptr resolve).
  Proof.
    intros ? ? [H1 H2]%function_spec_equiv_split; iSplit; iIntros.
    - by rewrite -H2.
    - by rewrite -H1.
  Qed.
End with_cpp.
Global Instance: Params (@cptr) 3 := {}.

Instance: Params (@as_Rep) 2 := {}.
Instance: Params (@_offsetR) 3 := {}.
Instance: Params (@pureR) 2 := {}.

Global Opaque _at _offsetR primR.

Typeclasses Opaque pureR.
Typeclasses Opaque as_Rep.

Arguments anyR {_ Σ resolve} ty q : rename.
Arguments uninitR {_ Σ resolve} ty q : rename.
Arguments primR {_ Σ resolve} ty q v : rename.
Arguments refR {_ Σ} ty v : rename.
Arguments cptr {_ Σ resolve} _ : rename.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  (** object identity *)
  Definition _identity (σ : genv) (cls : globname) (mdc : option globname)
             (q : Qp) : Rep :=
    as_Rep (@identity _ _ σ cls mdc q).
  (** cpp2v-core#194: [Fractional], [AsFractional], [Timeless]? *)
  (** cpp2v-core#194: The fraction is valid? Agreement? *)

  Definition _type_ptr (σ : genv) (ty : type) :=
    as_Rep (@type_ptr _ _ σ ty).
  Global Instance _type_ptr_persistent σ ty : Persistent (_type_ptr σ ty).
  Proof. apply _. Qed.

  Definition type_ptrR_def σ (t : type) : Rep := as_Rep (@type_ptr _ _ σ t).
  Definition type_ptrR_aux : seal (@type_ptrR_def). Proof. by eexists. Qed.
  Definition type_ptrR := type_ptrR_aux.(unseal).

  (********************* DERIVED CONCEPTS ****************************)

  Definition validR_def : Rep := as_Rep valid_ptr.
  Definition validR_aux : seal (@validR_def). Proof. by eexists. Qed.
  Definition validR := validR_aux.(unseal).

  Definition is_null_def : Rep :=
    as_Rep (fun addr => [| addr = nullptr |]).
  Definition is_null_aux : seal (@is_null_def). Proof. by eexists. Qed.
  Definition is_null := is_null_aux.(unseal).
  Definition is_null_eq : @is_null = _ := is_null_aux.(seal_eq).

  Global Instance is_null_persistent : Persistent is_null.
  Proof. rewrite is_null_eq. apply _. Qed.
  Global Instance is_null_affine : Affine is_null.
  Proof. rewrite is_null_eq. apply _. Qed.
  Global Instance is_null_timeless : Timeless is_null.
  Proof. rewrite is_null_eq. apply _. Qed.
  Global Instance is_null_fractional : Fractional (λ _, is_null).
  Proof. apply _. Qed.
  Global Instance is_null_as_fractional q : AsFractional is_null (λ _, is_null) q.
  Proof. exact: Build_AsFractional. Qed.

  Definition is_nonnull_def : Rep :=
    as_Rep (fun addr => [| addr <> nullptr |]).
  Definition is_nonnull_aux : seal (@is_nonnull_def). Proof. by eexists. Qed.
  Definition is_nonnull := is_nonnull_aux.(unseal).
  Definition is_nonnull_eq : @is_nonnull = _ := is_nonnull_aux.(seal_eq).

  Global Instance is_nonnull_persistent : Persistent is_nonnull.
  Proof. rewrite is_nonnull_eq. apply _. Qed.
  Global Instance is_nonnull_affine : Affine is_nonnull.
  Proof. rewrite is_nonnull_eq. apply _. Qed.
  Global Instance is_nonnull_timeless : Timeless is_nonnull.
  Proof. rewrite is_nonnull_eq. apply _. Qed.

  Global Instance primR_nonnull {σ} ty q v :
    Observe is_nonnull (primR (resolve:=σ) ty q v).
  Proof.
    rewrite is_nonnull_eq primR_eq. apply monPred_observe=>p /=. apply _.
  Qed.
  Global Instance uninitR_nonnull {σ} ty q :
    Observe is_nonnull (uninitR (resolve:=σ) ty q).
  Proof.
    rewrite is_nonnull_eq uninitR_eq. apply monPred_observe=>p /=. apply _.
  Qed.

  Lemma null_nonnull (R : Rep) : is_null |-- is_nonnull -* R.
  Proof.
    rewrite is_null_eq /is_null_def is_nonnull_eq /is_nonnull_def.
    constructor=>p /=. rewrite monPred_at_wand/=.
    by iIntros "->" (? <-%ptr_rel_elim) "%".
  Qed.

  (** [blockR sz] is mean to be a contiguous chunk of [sz] bytes *)
  Definition blockR {σ} (sz : _) : Rep :=
    _offsetR (_sub (resolve:=σ) T_uint8 (Z.of_N sz)) (emp) **
    (* ^ Encodes valid_loc (this .[ T_uint8 ! sz]). This is
    necessary to get [l |-> blockR n -|- l |-> blockR n ** l .[ T_uint8 ! m] |-> blockR 0]. *)
    [∗list] i ∈ seq 0 (N.to_nat sz),
      _offsetR (_sub (resolve:=σ) T_uint8 (Z.of_nat i)) (anyR (resolve:=σ) T_uint8 1).

End with_cpp.

Typeclasses Opaque _identity.
Typeclasses Opaque _type_ptr.
Typeclasses Opaque type_ptrR.
Arguments type_ptrR {_ Σ σ} _%bs.

Instance Persistent_spec `{Σ:cpp_logic ti} {resolve:genv} nm s :
  Persistent (_at (Σ:=Σ) (_global (resolve:=resolve) nm) (cptr (resolve:=resolve) s)) := _.
