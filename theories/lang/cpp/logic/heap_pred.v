(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
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

Implicit Types (σ resolve : genv).

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** See also [Rep_equiv_at] and [Rep_entails_at]. *)
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

  (* NOTE this is not exposed as a hint *)
  Lemma as_Rep_observe P Q (o : forall p, Observe (P p) (Q p)) : Observe (as_Rep P) (as_Rep Q).
  Proof. apply monPred_observe =>p; apply o. Qed.
  Lemma as_Rep_observe_2 P Q R (o : forall p, Observe2 (P p) (Q p) (R p)) :
    Observe2 (as_Rep P) (as_Rep Q) (as_Rep R).
  Proof. apply monPred_observe_2=>p. apply o. Qed.

  #[global] Instance as_Rep_only_provable_observe Q (P : ptr → mpred) :
    (∀ p, Observe [| Q |] (P p)) → Observe [| Q |] (as_Rep P).
  Proof.
    intros. apply monPred_observe=>p. by rewrite monPred_at_only_provable.
  Qed.
  #[global] Instance as_Rep_only_provable_observe_2 Q (P1 P2 : ptr → mpred) :
    (∀ p, Observe2 [| Q |] (P1 p) (P2 p)) →
    Observe2 [| Q |] (as_Rep P1) (as_Rep P2).
  Proof.
    intros. apply monPred_observe_2=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma as_Rep_obs f P :
    (∀ p, f p |-- f p ** [| P |]) →
    as_Rep f |-- as_Rep f ** [| P |].
  Proof.
    intros. apply observe_elim, as_Rep_only_provable_observe =>p. exact: observe_intro.
  Qed.

  Lemma Rep_wand_force (R1 R2 : Rep) p : (R1 -* R2) p -|- R1 p -* R2 p.
  Proof. split'. apply monPred_wand_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.
  Lemma Rep_impl_force (R1 R2 : Rep) p : (R1 -->> R2) p -|- R1 p -->> R2 p.
  Proof. split'. apply monPred_impl_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.
  Lemma Rep_at_wand_iff (P Q : Rep) p :
    (P ∗-∗ Q) p ⊣⊢ (P p ∗-∗ Q p).
  Proof. by rewrite /bi_wand_iff monPred_at_and !Rep_wand_force. Qed.

  Definition _offsetR_def (o : offset) (r : Rep) : Rep :=
    as_Rep (fun base => r.(monPred_at) (_offset_ptr base o)).
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

  Lemma _offsetR_emp o : _offsetR o emp ⊣⊢ emp.
  Proof.
    rewrite _offsetR_eq /_offsetR_def.
    constructor=> p /=. by rewrite !monPred_at_emp.
  Qed.
  Lemma _offsetR_sep o r1 r2 :
    _offsetR o (r1 ** r2) -|- _offsetR o r1 ** _offsetR o r2.
  Proof.
    rewrite _offsetR_eq /_offsetR_def -as_Rep_sep.
    constructor=> p /=. by rewrite monPred_at_sep.
  Qed.
  Lemma _offsetR_pure (o : offset) (P : Prop) :
    _offsetR o (bi_pure P) -|- bi_pure P.
  Proof.
    rewrite _offsetR_eq/_offsetR_def /=.
    by constructor=> p/=; rewrite !monPred_at_pure.
  Qed.

  Lemma _offsetR_only_provable (o : offset) (P : Prop) :
    _offsetR o [| P |] -|- [| P |].
  Proof.
    rewrite _offsetR_eq/_offsetR_def /=.
    by constructor=> p/=; rewrite !monPred_at_only_provable.
  Qed.

  Lemma _offsetR_and (o : offset) P Q :
    _offsetR o (P //\\ Q) -|- _offsetR o P //\\ _offsetR o Q.
  Proof.
    rewrite _offsetR_eq/_offsetR_def /=.
    by constructor=> p/=; rewrite !monPred_at_and.
  Qed.

  Lemma _offsetR_or (o : offset) P Q :
    _offsetR o (P \\// Q) -|- _offsetR o P \\// _offsetR o Q.
  Proof.
    rewrite _offsetR_eq/_offsetR_def /=.
    by constructor=> p/=; rewrite !monPred_at_or.
  Qed.

  Lemma _offsetR_pers o R : _offsetR o (<pers> R) -|- <pers> _offsetR o R.
  Proof.
    rewrite !_offsetR_eq /_offsetR_def /=.
    constructor=> p/=. by rewrite !monPred_at_persistently.
  Qed.

  Lemma _offsetR_wand o (P Q : Rep) :
      _offsetR o (P -* Q) |-- (_offsetR o P -* _offsetR o Q).
  Proof.
    rewrite !_offsetR_eq /_offsetR_def /=.
    constructor=> p/=. by rewrite !Rep_wand_force.
  Qed.

  Lemma _offsetR_big_sepL (o : offset) {T} (Rs : list T) : forall F,
    _offsetR o ([∗list] i ↦ x ∈ Rs , F i x) -|- [∗list] i ↦ x ∈ Rs , _offsetR o (F i x).
  Proof.
    induction Rs; simpl; intros.
    - by rewrite _offsetR_emp.
    - by rewrite _offsetR_sep IHRs.
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
  (* Pulled in from plogic. *)
  Lemma _offsetR_id (R : Rep) :
    _offsetR o_id R -|- R.
  Proof.
    rewrite _offsetR_eq /_offsetR_def.
    constructor=>/= p.
    by rewrite offset_ptr_id.
  Qed.

  Lemma _offsetR_dot (o1 o2 : offset) (R : Rep) :
    _offsetR o1 (_offsetR o2 R) -|- _offsetR (o_dot o1 o2) R.
  Proof.
    constructor =>p/=.
    by rewrite _offsetR_eq/_offsetR_def/= offset_ptr_dot.
  Qed.

  (** [_at base R] states that [R base] holds.

      NOTE This is "weakly at"
   *)
  Definition _at_def (base : ptr) (R : Rep) : mpred :=
    R.(monPred_at) base.
  Definition _at_aux : seal (@_at_def). Proof. by eexists. Qed.
  Definition _at := _at_aux.(unseal).
  Definition _at_eq : @_at = _ := _at_aux.(seal_eq).

  Global Instance _at_ne l : Proper (dist n ==> dist n) (_at l).
  Proof. rewrite _at_eq. solve_proper. Qed.
  Global Instance _at_proper : Proper ((≡) ==> (≡)) (_at p).
  Proof. rewrite _at_eq. solve_proper. Qed.
  Global Instance _at_mono : Proper ((⊢) ==> (⊢)) (_at p).
  Proof. rewrite _at_eq. solve_proper. Qed.
  Global Instance _at_flip_mono : Proper (flip (⊢) ==> flip (⊢)) (_at p).
  Proof. rewrite _at_eq/_at_def=> ? r1 r2 HR/=. by rewrite HR. Qed.

  Global Instance _at_persistent : Persistent P -> Persistent (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  Global Instance _at_affine : Affine P -> Affine (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  Global Instance _at_timeless : Timeless P -> Timeless (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.

  Lemma Rep_equiv_at (P Q : Rep)
    (HPQ : forall p : ptr, _at p P -|- _at p Q) :
    P -|- Q.
  Proof. constructor => p. move: HPQ => /(_ p). by rewrite _at_eq. Qed.

  Lemma Rep_entails_at (P Q : Rep)
    (HPQ : forall p : ptr, _at p P |-- _at p Q) :
    P |-- Q.
  Proof. constructor => p. move: HPQ => /(_ p). by rewrite _at_eq. Qed.

  #[deprecated(since="2020-12-08",note="more cumbersome than necessary")]
  Lemma _at_loc_materialize (l : ptr) (r : Rep) :
      _at l r -|- Exists a, l &~ a ** r a.
  Proof.
    rewrite _at_eq/_at_def path_pred.addr_of_eq /addr_of_def.
    iSplit.
    - iIntros "A"; iExists l; iFrame "#∗"; eauto.
    - iIntros "A"; iDestruct "A" as (ll) "X".
      iDestruct "X" as "[-> $]".
  Qed.

  Lemma _at_as_Rep (l : ptr) (Q : ptr → mpred) : _at l (as_Rep Q) ⊣⊢ Q l.
  Proof. by rewrite _at_eq/_at_def. Qed.

  (* Prefer [_at_as_Rep] *)
  Lemma _at_loc p R : _at p R -|- R p.
  Proof. by rewrite _at_eq/_at_def. Qed.

  Lemma _at_emp l : _at l emp -|- emp.
  Proof. by rewrite _at_loc monPred_at_emp. Qed.

  Lemma _at_exists l {T} (P : T -> Rep) :
      _at l (Exists v : T, P v) -|- Exists v, _at l (P v).
  Proof. by rewrite _at_loc monPred_at_exist; setoid_rewrite _at_loc. Qed.

  Lemma _at_forall (l : ptr) T (P : T -> Rep) :
    _at l (Forall x, P x) |-- Forall x, _at l (P x).
  Proof. by rewrite _at_loc monPred_at_forall; setoid_rewrite _at_loc. Qed.

  Lemma _at_only_provable l P :
      _at l [| P |] -|- [| P |].
  Proof. by rewrite _at_loc monPred_at_only_provable. Qed.

  Lemma _at_pure (l : ptr) (P : Prop) :
      _at l [! P !] -|- [! P !].
  Proof. by rewrite _at_loc monPred_at_pure. Qed.

  Lemma _at_sep (l : ptr) (P Q : Rep) :
      _at l (P ** Q) -|- _at l P ** _at l Q.
  Proof. by rewrite !_at_loc monPred_at_sep. Qed.

  Lemma _at_and (l : ptr) (P Q : Rep) :
      _at l (P //\\ Q) -|- _at l P //\\ _at l Q.
  Proof. by rewrite !_at_loc monPred_at_and. Qed.

  Lemma _at_or (l : ptr) (P Q : Rep) :
      _at l (P \\// Q) -|- _at l P \\// _at l Q.
  Proof. by rewrite !_at_loc monPred_at_or. Qed.

  Lemma _at_wand (l : ptr) (P Q : Rep) :
      _at l (P -* Q) |-- (_at l P -* _at l Q).
  Proof. by rewrite !_at_loc monPred_wand_force. Qed.

  Lemma _at_pers (l : ptr) R : _at l (<pers> R) -|- <pers> _at l R.
  Proof. by rewrite !_at_loc monPred_at_persistently. Qed.

  Lemma _at_fupd (l : ptr) R E1 E2 : _at l (|={E1,E2}=> R) -|- |={E1,E2}=> _at l R.
  Proof. by rewrite !_at_loc monPred_at_fupd. Qed.

  Lemma _at_intuitionistically l (R : Rep) : _at l (□ R) ⊣⊢ □ (_at l R).
  Proof. by rewrite _at_eq/_at_def monPred_at_intuitionistically. Qed.

  Lemma _at_offsetL_offsetR (l : ptr) (o : offset) (r : Rep) :
      _at l (_offsetR o r) -|- _at (_offsetL o l) r.
  Proof. by rewrite !_at_loc /flip _offsetR_eq/_offsetR_def /=. Qed.

  Global Instance _at_fractional (r : Qp → Rep) (l : ptr) `{!Fractional r} :
    Fractional (λ q, _at l (r q)).
  Proof.
    intros q1 q2; by rewrite fractional _at_sep.
  Qed.
  Global Instance _at_as_fractional (r : Qp → Rep) q (l : ptr)
      `{!AsFractional (r q) r q} :
    AsFractional (_at l (r q)) (λ q, _at l (r q)) q.
  Proof. constructor. done. apply _. Qed.

  (* TODO: consider making this a global instance, but test performance impact. *)
  Local Instance _at_observe {p} {Q R : Rep} :
    Observe Q R ->
    Observe (_at p Q) (_at p R).
  Proof. move->. by rewrite /Observe _at_pers. Qed.

  Local Instance _at_observe_2 {p} {Q R1 R2 : Rep} :
    Observe2 Q R1 R2 ->
    Observe2 (_at p Q) (_at p R1) (_at p R2).
  Proof. move->. by rewrite /Observe2 _at_wand _at_pers. Qed.

  Global Instance _at_observe_only_provable Q l (R : Rep) :
    Observe [| Q |] R → Observe [| Q |] (_at l R).
  Proof. rewrite -_at_only_provable. apply _. Qed.
  Global Instance _at_observe_2_only_provable Q l (R1 R2 : Rep) :
    Observe2 [| Q |] R1 R2 → Observe2 [| Q |] (_at l R1) (_at l R2).
  Proof. rewrite -_at_only_provable. apply _. Qed.

  Lemma _at_obs (l : ptr) (r : Rep) P :
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

  Lemma _at_pureR x (P : mpred) :
      _at x (pureR P) -|- P.
  Proof. by rewrite !_at_loc /pureR. Qed.

  (** As this isn't syntax-directed, we conservatively avoid
      registering it as an instance (which could slow down
      observations). It's handy under [Local Existing Instance
      _at_observe_pureR] to project a [pureR Q] conjunct out of
      representation predicates. *)
  Lemma _at_observe_pureR Q (l : ptr) (R : Rep) :
    Observe (pureR Q) R → Observe Q (_at l R).
  Proof.
    rewrite /Observe=>->. rewrite -pureR_persistently _at_pureR. done.
  Qed.

  (** [primR ty q v]: the argument pointer points to an initialized value [v] of C++ type [ty].
   *
   * NOTE [ty] *must* be a primitive type.
   *)
  Definition primR_def {resolve:genv} (ty : type) (q : Qp) (v : val) : Rep :=
    as_Rep (fun addr => tptsto ty q addr v ** [| has_type v (drop_qualifiers ty) |]).
  (** TODO what is the current status of [has_type] and [Vundef]? Does it have all types? No types?
   *)
  Definition primR_aux : seal (@primR_def). Proof. by eexists. Qed.
  Definition primR := primR_aux.(unseal).
  Definition primR_eq : @primR = _ := primR_aux.(seal_eq).
  Global Arguments primR {resolve} ty q v : rename.

  Global Instance primR_proper :
    Proper (genv_eq ==> (=) ==> (=) ==> (=) ==> (⊣⊢)) (@primR).
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
    : Affine (primR ty q p).
  Proof. rewrite primR_eq. apply _. Qed.
  Global Instance primR_timeless resolve ty q p
    : Timeless (primR ty q p).
  Proof. rewrite primR_eq. apply _. Qed.

  Global Instance primR_fractional resolve ty v :
    Fractional (λ q, primR ty q v).
  Proof. rewrite primR_eq. apply _. Qed.
  Global Instance primR_as_fractional resolve ty q v :
    AsFractional (primR ty q v) (λ q, primR ty q v) q.
  Proof. constructor. done. apply _. Qed.

  Global Instance primR_observe_frac_valid resolve ty (q : Qp) v :
    Observe [| q ≤ 1 |]%Qc (primR ty q v).
  Proof. rewrite primR_eq. apply _. Qed.

  Global Instance primR_observe_agree resolve ty q1 q2 v1 v2 :
    Observe2 [| v1 = v2 |]
      (primR ty q1 v1)
      (primR ty q2 v2).
  Proof. rewrite primR_eq. apply _. Qed.

  Global Instance primR_observe_has_type resolve ty q v :
    Observe [| has_type v (drop_qualifiers ty) |] (primR ty q v).
  Proof. rewrite primR_eq. apply _. Qed.

  Lemma primR_has_type {σ} ty q v :
    primR (resolve:=σ) ty q v |--
    primR (resolve:=σ) ty q v ** [| has_type v (drop_qualifiers ty) |].
  Proof. apply: observe_elim. Qed.

  (**
     [uninitR ty q]: the argument pointer points to an uninitialized value [Vundef] of C++ type [ty].
     Unlike [primR], does not imply [has_type].

     NOTE the [ty] argument *must* be a primitive type.

     TODO is it possible to generalize this to support aggregate types? structures seem easy enough
          but unions seem more difficult, possibly we can achieve that through the use of disjunction?
   *)
  Definition uninitR_def {resolve:genv} (ty : type) (q : Qp) : Rep :=
    as_Rep (fun addr => @tptsto _ _ resolve ty q addr Vundef).
  Definition uninitR_aux : seal (@uninitR_def). Proof. by eexists. Qed.
  Definition uninitR := uninitR_aux.(unseal).
  Definition uninitR_eq : @uninitR = _ := uninitR_aux.(seal_eq).
  Global Arguments uninitR {resolve} ty q : rename.

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
    : Affine (uninitR ty q).
  Proof. rewrite uninitR_eq. apply _. Qed.
  Global Instance uninitR_timeless resolve ty q
    : Timeless (uninitR ty q).
  Proof. rewrite uninitR_eq. apply _. Qed.

  Global Instance uninitR_fractional resolve ty :
    Fractional (uninitR ty).
  Proof. rewrite uninitR_eq. apply _. Qed.
  Global Instance unintR_as_fractional resolve ty q :
    AsFractional (uninitR ty q) (uninitR ty) q.
  Proof. constructor. done. apply _. Qed.

  Global Instance uninitR_observe_frac_valid resolve ty (q : Qp) :
    Observe [| q ≤ 1 |]%Qc (uninitR ty q).
  Proof. rewrite uninitR_eq. apply _. Qed.

  (** This seems odd, but it's relevant to proof that [anyR] is fractional. *)
  Lemma primR_uninitR {resolve} ty q1 q2 v :
    primR ty q1 v |--
    uninitR ty q2 -*
    primR ty (q1 + q2) Vundef.
  Proof.
    rewrite primR_eq/primR_def uninitR_eq/uninitR_def. constructor=>p /=.
    rewrite monPred_at_wand. iIntros "[T1 %]" (? <-%ptr_rel_elim) "/= T2".
    iDestruct (observe_2 [|v = Vundef|] with "T1 T2") as %->. iFrame "T1 T2 %".
  Qed.

  (** [anyR] The argument pointers points to a value of C++ type [ty] that might be
      uninitialized.

      TODO generalize this to support aggregate types
   *)
  Definition anyR_def {resolve} (ty : type) (q : Qp) : Rep :=
    (Exists v, primR ty q v) \\// uninitR ty q.
  Definition anyR_aux : seal (@anyR_def). Proof. by eexists. Qed.
  Definition anyR := anyR_aux.(unseal).
  Definition anyR_eq : @anyR = _ := anyR_aux.(seal_eq).
  Global Arguments anyR {resolve} ty q : rename.

  Global Instance anyR_affine resolve ty q : Affine (anyR ty q).
  Proof. rewrite anyR_eq. apply _. Qed.
  Global Instance anyR_timeless resolve ty q : Timeless (anyR ty q).
  Proof. rewrite anyR_eq. apply _. Qed.
  Global Instance anyR_fractional resolve ty :
    Fractional (anyR ty).
  Proof.
    rewrite anyR_eq /anyR_def. intros q1 q2.
    apply Rep_equiv_at => p. rewrite !_at_sep !_at_or !_at_exists.
    split'.
    { iDestruct 1 as "[V|U]".
      - rewrite -!bi.or_intro_l.
        iDestruct "V" as (v) "V".
        rewrite _at_eq/_at_def.
        iDestruct "V" as "[V1 V2]".
        iSplitL "V1"; iExists v; [iFrame "V1"|iFrame "V2"].
      - iDestruct "U" as "[U1 U2]".
        iSplitL "U1"; iRight; [iFrame "U1"|iFrame "U2"]. }
    iDestruct 1 as "[[V1|U1] [V2|U2]]".
    - iDestruct "V1" as (v1) "V1". iDestruct "V2" as (v2) "V2".
      iDestruct (observe_2 [| v1 = v2 |] with "V1 V2") as %->.
      iLeft. iExists v2. rewrite primR_fractional _at_sep. iFrame "V1 V2".
    - iDestruct "V1" as (v) "V1".
      rewrite _at_eq/_at_def.
      iDestruct (primR_uninitR with "V1 U2") as "V".
      iLeft. iExists _. iFrame "V".
    - iDestruct "V2" as (v) "V2".
      rewrite _at_eq/_at_def.
      iDestruct (primR_uninitR with "V2 U1") as "V".
      iLeft. iExists _. rewrite comm_L. iFrame "V".
    - iRight. rewrite uninitR_fractional _at_sep. iFrame "U1 U2".
  Qed.
  Global Instance anyR_as_fractional resolve ty q :
    AsFractional (anyR ty q) (anyR ty) q.
  Proof. exact: Build_AsFractional. Qed.

  Global Instance anyR_observe_frac_valid resolve ty (q : Qp) :
    Observe [| q ≤ 1 |]%Qc (anyR ty q).
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
Global Instance: Params (@_at) 3 := {}.
Global Instance: Params (@cptr) 3 := {}.

Instance: Params (@as_Rep) 2 := {}.
Instance: Params (@_offsetR) 3 := {}.
Instance: Params (@pureR) 2 := {}.

Typeclasses Opaque _at _offsetR primR.
Global Opaque _at _offsetR primR.

Typeclasses Opaque pureR.
Typeclasses Opaque as_Rep.

Arguments refR {_ Σ} ty v : rename.
Arguments cptr {_ Σ resolve} _ : rename.

Notation cptrR := cptr (only parsing).

Section with_cpp.
  Context `{Σ : cpp_logic}.
  (** object identity *)
  Definition identityR (σ : genv) (cls : globname) (mdc : option globname)
             (q : Qp) : Rep :=
    as_Rep (@identity _ _ σ cls mdc q).
  (** cpp2v-core#194: [Fractional], [AsFractional], [Timeless]? *)
  (** cpp2v-core#194: The fraction is valid? Agreement? *)

  (********************* DERIVED CONCEPTS ****************************)

  Definition validR_def : Rep := as_Rep valid_ptr.
  Definition validR_aux : seal (@validR_def). Proof. by eexists. Qed.
  Definition validR := validR_aux.(unseal).
  Definition validR_eq : @validR = _ := validR_aux.(seal_eq).
  #[global] Instance validR_persistent : Persistent validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_timeless : Timeless validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_affine : Affine validR.
  Proof. rewrite validR_eq; refine _. Qed.

  Lemma _at_validR (p : ptr) : _at p validR -|- valid_ptr p.
  Proof. by rewrite validR_eq/validR_def _at_eq/_at_def. Qed.

  Definition svalidR_def : Rep := as_Rep strict_valid_ptr.
  Definition svalidR_aux : seal (@svalidR_def). Proof. by eexists. Qed.
  Definition svalidR := svalidR_aux.(unseal).
  Definition svalidR_eq : @svalidR = _ := svalidR_aux.(seal_eq).
  #[global] Instance svalidR_persistent : Persistent svalidR.
  Proof. rewrite svalidR_eq; refine _. Qed.
  #[global] Instance svalidR_timeless : Timeless svalidR.
  Proof. rewrite svalidR_eq; refine _. Qed.
  #[global] Instance svalidR_affine : Affine svalidR.
  Proof. rewrite svalidR_eq; refine _. Qed.

  Lemma _at_svalidR (p : ptr) : _at p svalidR -|- strict_valid_ptr p.
  Proof. by rewrite svalidR_eq/svalidR_def _at_eq/_at_def. Qed.

  Definition type_ptrR_def σ (t : type) : Rep := as_Rep (@type_ptr _ _ σ t).
  Definition type_ptrR_aux : seal (@type_ptrR_def). Proof. by eexists. Qed.
  Definition type_ptrR := type_ptrR_aux.(unseal).
  Definition type_ptrR_eq : @type_ptrR = _ := type_ptrR_aux.(seal_eq).
  #[global] Instance type_ptrR_persistent σ t : Persistent (type_ptrR σ t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.
  #[global] Instance type_ptrR_timeless σ t : Timeless (type_ptrR σ t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.
  #[global] Instance type_ptrR_affine : Affine (type_ptrR σ t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.

  Lemma _at_type_ptrR σ (p : ptr) ty : _at p (type_ptrR σ ty) -|- type_ptr ty p.
  Proof. by rewrite type_ptrR_eq/type_ptrR_def _at_eq/_at_def. Qed.



  Lemma svalidR_validR : svalidR |-- validR.
  Proof.
    rewrite validR_eq/validR_def svalidR_eq/svalidR_def.
    constructor =>p /=. by apply strict_valid_relaxed.
  Qed.
  Lemma type_ptrR_svalidR σ ty : type_ptrR σ ty |-- svalidR.
  Proof.
    rewrite type_ptrR_eq/type_ptrR_def svalidR_eq/svalidR_def.
    constructor =>p /=. by apply type_ptr_strict_valid.
  Qed.
  Lemma type_ptrR_validR σ ty : type_ptrR σ ty |-- validR.
  Proof. by rewrite type_ptrR_svalidR svalidR_validR. Qed.

  #[global] Instance svalidR_validR_observe : Observe validR svalidR.
  Proof. rewrite svalidR_validR. red; iIntros "#$". Qed.
  #[global] Instance type_ptrR_svalidR_observe σ t : Observe svalidR (type_ptrR σ t).
  Proof. rewrite type_ptrR_svalidR; red; iIntros "#$". Qed.

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

  Definition alignedR_def (al : N) : Rep := as_Rep (aligned_ptr al).
  Definition alignedR_aux : seal (@alignedR_def). Proof. by eexists. Qed.
  Definition alignedR := alignedR_aux.(unseal).
  Definition alignedR_eq : @alignedR = _ := alignedR_aux.(seal_eq).
  #[global] Instance alignedR_persistent : Persistent (alignedR al).
  Proof. rewrite alignedR_eq. apply _. Qed.
  #[global] Instance alignedR_affine : Affine (alignedR al).
  Proof. rewrite alignedR_eq. apply _. Qed.
  #[global] Instance alignedR_timeless : Timeless (alignedR al).
  Proof. rewrite alignedR_eq. apply _. Qed.

  Lemma null_nonnull (R : Rep) : is_null |-- is_nonnull -* R.
  Proof.
    rewrite is_null_eq /is_null_def is_nonnull_eq /is_nonnull_def.
    constructor=>p /=. rewrite monPred_at_wand/=.
    by iIntros "->" (? <-%ptr_rel_elim) "%".
  Qed.

  (** [blockR sz] represents a contiguous chunk of [sz] bytes *)
  Definition blockR {σ} (sz : _) : Rep :=
    _offsetR (o_sub σ T_uint8 (Z.of_N sz)) validR **
    (* ^ Encodes valid_ptr (this .[ T_uint8 ! sz]). This is
    necessary to get [l |-> blockR n -|- l |-> blockR n ** l .[ T_uint8 ! m] |-> blockR 0]. *)
    [∗list] i ∈ seq 0 (N.to_nat sz),
      _offsetR (o_sub σ T_uint8 (Z.of_nat i)) (anyR (resolve:=σ) T_uint8 1).

  (* [tblockR ty] is a [blockR] that is the size of [ty].
   * it is a convenient short-hand since it happens frequently, but there is nothing
   * special about it.
   *)
  Definition tblockR {σ} (ty : type) : Rep :=
    match size_of σ ty , align_of ty with
    | Some sz , Some al => blockR (σ:=σ) sz ** alignedR al
    | _ , _  => False
    end.


  (** Observing [type_ptr] *)
  #[global]
  Instance primR_type_ptr_observe σ ty q v : Observe (type_ptrR σ ty) (primR ty q v).
  Proof.
    red. rewrite primR_eq/primR_def.
    apply Rep_entails_at => p. rewrite _at_as_Rep _at_pers _at_type_ptrR.
    iIntros "[A _]".
    iDestruct (observe (type_ptr ty p) with "A") as "$".
    apply tptsto_type_ptr.
  Qed.
  #[global]
  Instance uninitR_type_ptr_observe σ ty q : Observe (type_ptrR σ ty) (uninitR ty q).
  Proof.
    red. rewrite uninitR_eq/uninitR_def.
    apply Rep_entails_at => p. rewrite _at_as_Rep _at_pers _at_type_ptrR.
    iIntros "[A _]".
    iDestruct (observe (type_ptr ty p) with "A") as "$".
    apply tptsto_type_ptr.
  Qed.

  #[global]
  Instance anyR_type_ptr_observe σ ty q : Observe (type_ptrR σ ty) (anyR ty q).
  Proof.
    red. rewrite anyR_eq/anyR_def.
    iDestruct 1 as "[a|a]"; first iDestruct "a" as (?) "a"; iStopProof.
    all: apply: observe.
  Qed.

  (** Observing [valid_ptr] *)
  #[global]
  Instance primR_valid_observe {σ : genv} {ty q v} : Observe validR (primR ty q v).
  Proof. rewrite -svalidR_validR -type_ptrR_svalidR; refine _. Qed.
  #[global]
  Instance anyR_valid_observe {σ : genv} {ty q} : Observe validR (anyR ty q).
  Proof. rewrite -svalidR_validR -type_ptrR_svalidR; refine _. Qed.
  #[global]
  Instance uninitR_valid_observe {σ : genv} {ty q} : Observe validR (uninitR ty q).
  Proof. rewrite -svalidR_validR -type_ptrR_svalidR; refine _. Qed.

  #[global]
  Instance observe_type_ptr_pointsto σ (p : ptr) ty (R : Rep) :
    Observe (type_ptrR σ ty) R -> Observe (type_ptr ty p) (_at p R).
  Proof. rewrite -_at_type_ptrR. apply _at_observe. Qed.
End with_cpp.

Typeclasses Opaque identityR.
Typeclasses Opaque type_ptrR validR svalidR alignedR.
Arguments type_ptrR {_ Σ σ} _%bs.
Arguments identityR {_ Σ σ} _%bs _%bs _%Qp.

Instance Persistent_spec `{Σ:cpp_logic ti} {resolve:genv} nm s :
  Persistent (_at (Σ:=Σ) (_global nm) (cptrR s)) := _.
