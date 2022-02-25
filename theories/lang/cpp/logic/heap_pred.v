(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.bi Require Export monpred.
From iris.proofmode Require Import proofmode monpred.
Require Import iris.bi.lib.fractional.

Require Import bedrock.prelude.base.

From bedrock.lang.cpp Require Import
     semantics ast logic.pred logic.path_pred logic.rep.
Export bedrock.lang.cpp.logic.rep.

Implicit Types (σ resolve : genv) (p : ptr) (o : offset).

Section defs.
  Context `{Σ : cpp_logic}.

  (** object identity *)
  Definition identityR (σ : genv) (cls : globname) (mdc : option globname)
             (q : Qp) : Rep :=
    as_Rep (@identity _ _ σ cls mdc q).
  (** cpp2v-core#194: [Fractional], [AsFractional], [Timeless]? *)
  (** cpp2v-core#194: The fraction is valid? Agreement? *)

  Definition validR_def : Rep := as_Rep valid_ptr.
  Definition validR_aux : seal (@validR_def). Proof. by eexists. Qed.
  Definition validR := validR_aux.(unseal).
  Definition validR_eq : @validR = _ := validR_aux.(seal_eq).

  Definition svalidR_def : Rep := as_Rep strict_valid_ptr.
  Definition svalidR_aux : seal (@svalidR_def). Proof. by eexists. Qed.
  Definition svalidR := svalidR_aux.(unseal).
  Definition svalidR_eq : @svalidR = _ := svalidR_aux.(seal_eq).

  Definition type_ptrR_def σ (t : type) : Rep := as_Rep (@type_ptr _ _ σ t).
  Definition type_ptrR_aux : seal (@type_ptrR_def). Proof. by eexists. Qed.
  Definition type_ptrR := type_ptrR_aux.(unseal).
  Definition type_ptrR_eq : @type_ptrR = _ := type_ptrR_aux.(seal_eq).

End defs.

Arguments type_ptrR {_ Σ σ} _%bs.
Arguments identityR {_ Σ σ} _%bs _%bs _%Qp.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** [primR ty q v]: the argument pointer points to an initialized value [v] of C++ type [ty].
   *
   * NOTE [ty] *must* be a primitive type.
   *)
  Definition primR_def {resolve:genv} (ty : type) (q : Qp) (v : val) : Rep :=
    as_Rep (fun addr => tptsto ty q addr v **
                      [| not(exists raw, v = Vraw raw) |] **
                      [| has_type v (drop_qualifiers ty) |]).
  (** TODO what is the current status of [has_type] and [Vundef]? Does it have all types? No types?
   *)
  Definition primR_aux : seal (@primR_def). Proof. by eexists. Qed.
  Definition primR := primR_aux.(unseal).
  Definition primR_eq : @primR = _ := primR_aux.(seal_eq).
  #[global] Arguments primR {resolve} ty q v : rename.

  #[global] Instance primR_proper :
    Proper (genv_eq ==> (=) ==> (=) ==> (=) ==> (⊣⊢)) (@primR).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite primR_eq/primR_def. by setoid_rewrite Hσ.
  Qed.
  #[global] Instance primR_mono :
    Proper (genv_leq ==> (=) ==> (=) ==> (=) ==> (⊢)) (@primR).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite primR_eq/primR_def. by setoid_rewrite Hσ.
  Qed.

  #[global] Instance primR_timeless resolve ty q v
    : Timeless (primR ty q v).
  Proof. rewrite primR_eq. apply _. Qed.

  #[global] Instance primR_fractional resolve ty v :
    Fractional (λ q, primR ty q v).
  Proof. rewrite primR_eq. apply _. Qed.
  #[global] Instance primR_as_fractional resolve ty q v :
    AsFractional (primR ty q v) (λ q, primR ty q v) q.
  Proof. constructor. done. apply _. Qed.

  #[global] Instance primR_observe_frac_valid resolve ty (q : Qp) v :
    Observe [| q ≤ 1 |]%Qp (primR ty q v).
  Proof. rewrite primR_eq. apply _. Qed.

  #[global] Instance primR_observe_agree resolve ty q1 q2 v1 v2 :
    Observe2 [| v1 = v2 |]
      (primR ty q1 v1)
      (primR ty q2 v2).
  Proof.
    rewrite primR_eq/primR_def;
      apply: as_Rep_only_provable_observe_2=> p;
      apply: observe_2_intro_only_provable.
    iIntros "(Htptsto1 & %Hnotraw1 & %Hhas_type1)
             (Htptsto2 & %Hnotraw2 & %Hhas_type2)".
    iDestruct (observe_2_elim_pure with "Htptsto1 Htptsto2") as %Hvs.
    assert (v1 = v2)
      by (induction Hvs; subst; auto; exfalso;
          [apply Hnotraw1 | apply Hnotraw2];
          eauto).
    by iPureIntro.
  Qed.

  #[global] Instance primR_observe_has_type resolve ty q v :
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
  #[global] Arguments uninitR {resolve} ty q : rename.

  #[global] Instance uninitR_proper
    : Proper (genv_eq ==> (=) ==> (=) ==> (≡)) (@uninitR).
  Proof.
    intros σ1 σ2 Hσ ??-> ??->     .
    rewrite uninitR_eq/uninitR_def. by setoid_rewrite Hσ.
  Qed.
  #[global] Instance uninitR_mono
    : Proper (genv_leq ==> (=) ==> (=) ==> (⊢)) (@uninitR).
  Proof.
    intros σ1 σ2 Hσ ??-> ??->     .
    rewrite uninitR_eq/uninitR_def. by setoid_rewrite Hσ.
  Qed.

  #[global] Instance uninitR_timeless resolve ty q
    : Timeless (uninitR ty q).
  Proof. rewrite uninitR_eq. apply _. Qed.

  #[global] Instance uninitR_fractional resolve ty :
    Fractional (uninitR ty).
  Proof. rewrite uninitR_eq. apply _. Qed.
  #[global] Instance unintR_as_fractional resolve ty q :
    AsFractional (uninitR ty q) (uninitR ty) q.
  Proof. constructor. done. apply _. Qed.

  #[global] Instance uninitR_observe_frac_valid resolve ty (q : Qp) :
    Observe [| q ≤ 1 |]%Qp (uninitR ty q).
  Proof. rewrite uninitR_eq. apply _. Qed.

  Lemma test:
    forall σ ty v v',
      v' = Vundef ->
      val_related σ ty v v' ->
      v = Vundef.
  Proof.
    intros * Hv' Hval_related; induction Hval_related;
      try (by inversion Hv'); auto.
  Qed.

  (** This seems odd, but it's relevant to proof that [anyR] is fractional. *)
  Lemma primR_uninitR {resolve} ty q1 q2 v :
    primR ty q1 v |--
    uninitR ty q2 -*
    primR ty (q1 + q2) Vundef.
  Proof.
    rewrite primR_eq/primR_def uninitR_eq/uninitR_def. constructor=>p /=.
    rewrite monPred_at_wand. iIntros "[T1 [%Hnotraw %Hty]]" (? <-%ptr_rel_elim) "/= T2".
    iDestruct (observe_2 [| val_related resolve ty v Vundef |] with "T1 T2") as "%Hrelated".
    assert (v = Vundef)
      by (remember Vundef as v'; induction Hrelated;
          try (by inversion Heqv'); auto); subst.
    iCombine "T1 T2" as "T"; by iFrame "∗%".
  Qed.

  (** [anyR] The argument pointers points to a value of C++ type [ty] that might be
      uninitialized. *)
  Parameter anyR : ∀ {resolve} (ty : type) (q : Qp), Rep.
  #[global] Arguments anyR {resolve} ty q : rename.
  Axiom anyR_timeless : ∀ resolve ty q, Timeless (anyR ty q).
  Axiom anyR_fractional : ∀ resolve ty, Fractional (anyR ty).
  Axiom anyR_observe_frac_valid : ∀ resolve ty (q : Qp),
    Observe [| q ≤ 1 |]%Qp (anyR ty q).
  Axiom primR_anyR : ∀ resolve t q v, primR t q v |-- anyR t q.
  Axiom uninitR_anyR : ∀ resolve t q, uninitR t q |-- anyR t q.
  Axiom anyR_type_ptr_observe : ∀ σ ty q, Observe (type_ptrR ty) (anyR ty q).

  #[global] Existing Instances anyR_timeless anyR_fractional anyR_observe_frac_valid anyR_type_ptr_observe.
  #[global] Instance anyR_as_fractional resolve ty q :
    AsFractional (anyR ty q) (anyR ty) q.
  Proof. exact: Build_AsFractional. Qed.
End with_cpp.

#[global] Typeclasses Opaque primR.
#[global] Opaque primR.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (********************* DERIVED CONCEPTS ****************************)
  #[global] Instance validR_persistent : Persistent validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_timeless : Timeless validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_affine : Affine validR.
  Proof. rewrite validR_eq; refine _. Qed.

  Lemma monPred_at_validR p : validR p -|- valid_ptr p.
  Proof. by rewrite validR_eq. Qed.
  Lemma _at_validR (p : ptr) : _at p validR -|- valid_ptr p.
  Proof. by rewrite validR_eq _at_eq. Qed.

  #[global] Instance svalidR_persistent : Persistent svalidR.
  Proof. rewrite svalidR_eq; refine _. Qed.
  #[global] Instance svalidR_timeless : Timeless svalidR.
  Proof. rewrite svalidR_eq; refine _. Qed.
  #[global] Instance svalidR_affine : Affine svalidR.
  Proof. rewrite svalidR_eq; refine _. Qed.

  Lemma monPred_at_svalidR p : svalidR p -|- strict_valid_ptr p.
  Proof. by rewrite svalidR_eq. Qed.
  Lemma _at_svalidR (p : ptr) : _at p svalidR -|- strict_valid_ptr p.
  Proof. by rewrite svalidR_eq _at_eq. Qed.

  #[global] Instance type_ptrR_persistent σ t : Persistent (type_ptrR t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.
  #[global] Instance type_ptrR_timeless σ t : Timeless (type_ptrR t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.
  #[global] Instance type_ptrR_affine σ t : Affine (type_ptrR t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.

  Lemma monPred_at_type_ptrR ty σ p : type_ptrR ty p -|- type_ptr ty p.
  Proof. by rewrite type_ptrR_eq. Qed.
  Lemma _at_type_ptrR σ (p : ptr) ty : _at p (type_ptrR ty) -|- type_ptr ty p.
  Proof. by rewrite type_ptrR_eq _at_eq. Qed.



  Lemma svalidR_validR : svalidR |-- validR.
  Proof.
    rewrite validR_eq/validR_def svalidR_eq/svalidR_def.
    constructor =>p /=. by apply strict_valid_valid.
  Qed.
  Lemma type_ptrR_svalidR σ ty : type_ptrR ty |-- svalidR.
  Proof.
    rewrite type_ptrR_eq/type_ptrR_def svalidR_eq/svalidR_def.
    constructor =>p /=. by apply type_ptr_strict_valid.
  Qed.
  Lemma type_ptrR_validR σ ty : type_ptrR ty |-- validR.
  Proof. by rewrite type_ptrR_svalidR svalidR_validR. Qed.

  #[global] Instance svalidR_validR_observe : Observe validR svalidR.
  Proof. rewrite svalidR_validR. red; iIntros "#$". Qed.
  #[global] Instance type_ptrR_svalidR_observe σ t : Observe svalidR (type_ptrR t).
  Proof. rewrite type_ptrR_svalidR; red; iIntros "#$". Qed.

  Definition is_null_def : Rep :=
    as_Rep (fun addr => [| addr = nullptr |]).
  Definition is_null_aux : seal (@is_null_def). Proof. by eexists. Qed.
  Definition is_null := is_null_aux.(unseal).
  Definition is_null_eq : @is_null = _ := is_null_aux.(seal_eq).

  #[global] Instance is_null_persistent : Persistent is_null.
  Proof. rewrite is_null_eq. apply _. Qed.
  #[global] Instance is_null_affine : Affine is_null.
  Proof. rewrite is_null_eq. apply _. Qed.
  #[global] Instance is_null_timeless : Timeless is_null.
  Proof. rewrite is_null_eq. apply _. Qed.
  #[global] Instance is_null_fractional : Fractional (λ _, is_null).
  Proof. apply _. Qed.
  #[global] Instance is_null_as_fractional q : AsFractional is_null (λ _, is_null) q.
  Proof. exact: Build_AsFractional. Qed.

  Definition is_nonnull_def : Rep :=
    as_Rep (fun addr => [| addr <> nullptr |]).
  Definition is_nonnull_aux : seal (@is_nonnull_def). Proof. by eexists. Qed.
  Definition is_nonnull := is_nonnull_aux.(unseal).
  Definition is_nonnull_eq : @is_nonnull = _ := is_nonnull_aux.(seal_eq).

  #[global] Instance is_nonnull_persistent : Persistent is_nonnull.
  Proof. rewrite is_nonnull_eq. apply _. Qed.
  #[global] Instance is_nonnull_affine : Affine is_nonnull.
  Proof. rewrite is_nonnull_eq. apply _. Qed.
  #[global] Instance is_nonnull_timeless : Timeless is_nonnull.
  Proof. rewrite is_nonnull_eq. apply _. Qed.

  Definition alignedR_def (al : N) : Rep := as_Rep (λ p, [| aligned_ptr al p |]).
  Definition alignedR_aux : seal (@alignedR_def). Proof. by eexists. Qed.
  Definition alignedR := alignedR_aux.(unseal).
  Definition alignedR_eq : @alignedR = _ := alignedR_aux.(seal_eq).
  #[global] Instance alignedR_persistent {al} : Persistent (alignedR al).
  Proof. rewrite alignedR_eq. apply _. Qed.
  #[global] Instance alignedR_affine {al} : Affine (alignedR al).
  Proof. rewrite alignedR_eq. apply _. Qed.
  #[global] Instance alignedR_timeless {al} : Timeless (alignedR al).
  Proof. rewrite alignedR_eq. apply _. Qed.

  #[global] Instance alignedR_divide_mono :
    Proper (flip N.divide ==> bi_entails) alignedR.
  Proof.
    intros m n ?.
    rewrite alignedR_eq /alignedR_def. constructor=>p/=. iIntros "!%".
    exact: aligned_ptr_divide_weaken.
  Qed.

  #[global] Instance alignedR_divide_flip_mono :
    Proper (N.divide ==> flip bi_entails) alignedR.
  Proof. solve_proper. Qed.

  Lemma alignedR_divide_weaken m n :
    (n | m)%N ->
    alignedR m ⊢ alignedR n.
  Proof. by move->. Qed.

  Lemma null_nonnull (R : Rep) : is_null |-- is_nonnull -* R.
  Proof.
    rewrite is_null_eq /is_null_def is_nonnull_eq /is_nonnull_def.
    constructor=>p /=. rewrite monPred_at_wand/=.
    by iIntros "->" (? <-%ptr_rel_elim) "%".
  Qed.

  (** [blockR sz q] represents [q] ownership of a contiguous chunk of
      [sz] bytes without any C++ structure on top of it. *)
  Definition blockR_def {σ} sz (q : Qp) : Rep :=
    _offsetR (o_sub σ T_uint8 (Z.of_N sz)) validR **
    (* ^ Encodes valid_ptr (this .[ T_uint8 ! sz]). This is
    necessary to get [l |-> blockR n -|- l |-> blockR n ** l .[ T_uint8 ! m] |-> blockR 0]. *)
    [∗list] i ∈ seq 0 (N.to_nat sz),
      _offsetR (o_sub σ T_uint8 (Z.of_nat i)) (anyR (resolve:=σ) T_uint8 q).
  Definition blockR_aux : seal (@blockR_def). Proof. by eexists. Qed.
  Definition blockR := blockR_aux.(unseal).
  Definition blockR_eq : @blockR = _ := blockR_aux.(seal_eq).
  #[global] Arguments blockR {_} _%N _%Qp.

  #[global] Instance blockR_timeless {resolve : genv} sz q :
    Timeless (blockR sz q).
  Proof. rewrite blockR_eq. apply _. Qed.
  #[global] Instance blockR_fractional resolve sz :
    Fractional (blockR sz).
  Proof.
    by rewrite blockR_eq /blockR_def; apply _.
  Qed.
  #[global] Instance blockR_as_fractional resolve sz q :
    AsFractional (blockR sz q) (blockR sz) q.
  Proof. exact: Build_AsFractional. Qed.

  #[global] Instance blockR_observe_frac_valid resolve sz (q : Qp) :
    TCLt (0 ?= sz)%N ->
    Observe [| q ≤ 1 |]%Qp (blockR sz q).
  Proof.
    rewrite TCLt_N blockR_eq/blockR_def. intros.
    destruct (N.to_nat sz) eqn:?; [ lia | ] => /=.
    refine _.
  Qed.

  (* [tblockR ty] is a [blockR] that is the size of [ty] and properly aligned.
   * it is a convenient short-hand since it happens frequently, but there is nothing
   * special about it.
   *)
  Definition tblockR {σ} (ty : type) (q : Qp) : Rep :=
    match size_of σ ty , align_of ty with
    | Some sz , Some al => blockR (σ:=σ) sz q ** alignedR al
    | _ , _  => False
    end.

  #[global] Instance tblockR_timeless {σ} ty q :
    Timeless (tblockR ty q).
  Proof. rewrite/tblockR. case_match; apply _. Qed.
  #[global] Instance tblockR_fractional {σ} ty :
    Fractional (tblockR ty).
  Proof.
    rewrite/tblockR. do 2!(case_match; last by apply _).
    apply _.
  Qed.
  #[global] Instance tblockR_as_fractional {σ} ty q :
    AsFractional (tblockR ty q) (tblockR ty) q.
  Proof. exact: Build_AsFractional. Qed.
  #[global] Instance tblockR_observe_frac_valid {σ} ty q n :
    SizeOf ty n -> TCLt (0 ?= n)%N ->
    Observe [| q ≤ 1 |]%Qp (tblockR ty q).
  Proof.
    rewrite/tblockR=>-> ?. case_match; by apply _.
  Qed.

  (** Observing [type_ptr] *)
  #[global]
  Instance primR_type_ptr_observe σ ty q v : Observe (type_ptrR ty) (primR ty q v).
  Proof.
    red. rewrite primR_eq/primR_def.
    apply Rep_entails_at => p. rewrite _at_as_Rep _at_pers _at_type_ptrR.
    apply: observe.
  Qed.
  #[global]
  Instance uninitR_type_ptr_observe σ ty q : Observe (type_ptrR ty) (uninitR ty q).
  Proof.
    red. rewrite uninitR_eq/uninitR_def.
    apply Rep_entails_at => p. rewrite _at_as_Rep _at_pers _at_type_ptrR.
    apply: observe.
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
    Observe (type_ptrR ty) R -> Observe (type_ptr ty p) (_at p R).
  Proof. rewrite -_at_type_ptrR. apply _at_observe. Qed.

  #[global] Instance type_ptrR_size_observe σ ty :
    Observe [| is_Some (size_of σ ty) |] (type_ptrR ty).
  Proof.
    apply monPred_observe_only_provable => p.
    rewrite monPred_at_type_ptrR. apply _.
  Qed.

  Lemma off_validR o
    (Hv : ∀ p, valid_ptr (p .., o) |-- valid_ptr p) :
    _offsetR o validR |-- validR.
  Proof.
    apply Rep_entails_at => p. by rewrite _at_offsetR !_at_validR.
  Qed.

  Lemma _field_validR σ f : _offsetR (_field f) validR |-- validR.
  Proof. apply off_validR => p. apply _valid_ptr_field. Qed.

  Lemma _base_validR σ derived base :
    _offsetR (_base derived base) validR |-- validR.
  Proof. apply off_validR => p. apply _valid_ptr_base. Qed.

  Lemma _derived_validR σ base derived :
    _offsetR (_derived base derived) validR |-- validR.
  Proof. apply off_validR => p. apply _valid_ptr_derived. Qed.

  (** Observation of [is_nonnull] *)
  #[global]
  Instance primR_nonnull_observe {σ} {ty q v} :
    Observe is_nonnull (primR ty q v).
  Proof.
    rewrite is_nonnull_eq primR_eq. apply monPred_observe=>p /=. apply _.
  Qed.
  #[global]
  Instance uninitR_nonnull_observe {σ} {ty q} :
    Observe is_nonnull (uninitR ty q).
  Proof.
    rewrite is_nonnull_eq uninitR_eq. apply monPred_observe=>p /=. apply _.
  Qed.
  Axiom anyR_nonnull_observe : ∀ {σ} {ty q}, Observe is_nonnull (anyR ty q).
  #[global] Existing Instance anyR_nonnull_observe.

  #[global] Instance blockR_nonnull {σ : genv} n q :
    TCLt (0 ?= n)%N -> Observe is_nonnull (blockR n q).
  Proof.
    rewrite TCLt_N blockR_eq/blockR_def.
    destruct (N.to_nat n) eqn:Hn; [ lia | ] => {Hn} /=.
    rewrite o_sub_0 ?_offsetR_id; [ | by eauto].
    apply _.
  Qed.
  #[global] Instance blockR_valid_ptr {σ} sz q : Observe validR (blockR sz q).
  Proof.
    rewrite blockR_eq/blockR_def.
    destruct sz.
    { iIntros "[#A _]".
      rewrite o_sub_0; last by econstructor.
      rewrite _offsetR_id. eauto. }
    { iIntros "[_ X]".
      simpl. destruct (Pos.to_nat p) eqn:?; first lia.
      simpl. iDestruct "X" as "[X _]".
      rewrite o_sub_0; last by econstructor. rewrite _offsetR_id.
      iApply (observe with "X"). }
  Qed.

  #[global] Instance tblockR_nonnull {σ} n ty q :
    SizeOf ty n -> TCLt (0 ?= n)%N ->
    Observe is_nonnull (tblockR ty q).
  Proof.
    intros Heq ?. rewrite/tblockR {}Heq.
    case_match; by apply _.
  Qed.

  #[global] Instance tblockR_valid_ptr {σ} ty q : Observe validR (tblockR ty q).
  Proof.
    rewrite /tblockR. case_match; refine _.
    case_match; refine _.
  Qed.

End with_cpp.

#[global] Typeclasses Opaque identityR.
#[global] Typeclasses Opaque type_ptrR validR svalidR alignedR.
