(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From iris.proofmode Require Import proofmode.
From bedrock.lang.bi Require Import fractional.

From bedrock.lang.cpp Require Import
  bi.cfractional
  semantics ast logic.pred logic.path_pred.

Export bedrock.lang.cpp.logic.pred.
(* ^^ Should this be exported? this file is supposed to provide wrappers
   so that clients do not work directly with [pred.v] *)
Export bedrock.lang.cpp.algebra.cfrac.

#[local] Set Printing Coercions.

Implicit Types (σ resolve : genv) (p : ptr) (o : offset).

Section defs.
  Context `{Σ : cpp_logic}.

  (** object identity *)
  Definition identityR {σ : genv} (cls : globname) (mdc : list globname)
             (q : cQp.t) : Rep :=
    as_Rep (identity cls mdc q).

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

Arguments type_ptrR {_ Σ σ} _.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** [varargsR ts_ps] is the ownership of a group of variadic arguments.
      The [type] is the type of the argument and the [ptr] is the location
      of the argument. *)
  Parameter varargsR : list (type * ptr) -> Rep.

  (** [primR ty q v]: the argument pointer points to an initialized value [v] of C++ type [ty].
   *
   * NOTE [ty] *must* be a primitive type.
   *)
  Definition primR_def {resolve:genv} (ty : type) (q : cQp.t) (v : val) : Rep :=
    as_Rep (fun p : ptr => tptsto ty q p v **
             [| not(exists raw, v = Vraw raw) |] **
             [| has_type v (drop_qualifiers ty) |]).
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


  #[global] Instance primR_cfractional resolve ty :
    CFractional1 (primR ty).
  Proof. rewrite primR_eq. apply _. Qed.
  #[global] Instance primR_as_cfractional resolve ty :
    AsCFractional1 (primR ty).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance primR_observe_cfrac_valid resolve ty :
    CFracValid1 (primR ty).
  Proof. rewrite primR_eq. solve_cfrac_valid. Qed.

  Section TEST.
    Context {σ : genv} (p : ptr).

    Goal
        p |-> primR Tint (cQp.m (1/2)) 0
        |-- p |-> primR Tint (cQp.m (1/2)) 0 -* p |-> primR Tint (cQp.m 1) 0.
    Proof.
      iIntros "H1 H2".
      iCombine "H1 H2" as "$".
    Abort.

    Goal
        p |-> primR Tint (cQp.c 1) 0 |-- p |-> primR Tint (cQp.c (1/2)) 0 ** p |-> primR Tint (cQp.c (1/2)) 0.
    Proof.
      iIntros "H".
      iDestruct "H" as "[H1 H2]".
    Abort.

    Goal p |-> primR Tint (cQp.c 1) 1 |-- True.
    Proof.
      iIntros "H".
      iDestruct (observe [| 1 ≤ 1 |]%Qp with "H") as %? (* ; [] << FAILS *).
    Abort.
  End TEST.

  #[global] Instance primR_observe_agree resolve ty q1 q2 v1 v2 :
    Observe2 [| v1 = v2 |]
      (primR ty q1 v1)
      (primR ty q2 v2).
  Proof.
    rewrite primR_eq/primR_def; apply: as_Rep_only_provable_observe_2=> p.
    iIntros "(Htptsto1 & %Hnotraw1 & %Hhas_type1)
             (Htptsto2 & %Hnotraw2 & %Hhas_type2)".
    iApply (observe_2 with "Htptsto1 Htptsto2").
    iApply observe_2_derive_only_provable => Hvs.
    induction Hvs; subst; auto; exfalso;
        [apply Hnotraw1 | apply Hnotraw2];
        eauto.
  Qed.

  (* Typical [f] are [Vint], [Vn] etc; this gives agreement for [u64R] etc. *)
  #[global] Instance primR_observe_agree_constr resolve ty q1 q2 {A} f `{!Inj eq eq f} (v1 v2 : A) :
    Observe2 [| v1 = v2 |]
      (primR ty q1 (f v1))
      (primR ty q2 (f v2)).
  Proof. apply (observe2_inj f), _. Qed.

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
  Definition uninitR_def {resolve:genv} (ty : type) (q : cQp.t) : Rep :=
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

  #[global] Instance uninitR_cfractional resolve ty :
    CFractional (uninitR ty).
  Proof. rewrite uninitR_eq. apply _. Qed.
  #[global] Instance unintR_as_fractional resolve ty :
    AsCFractional0 (uninitR ty).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance uninitR_observe_frac_valid resolve ty :
    CFracValid0 (uninitR ty).
  Proof. rewrite uninitR_eq. solve_cfrac_valid. Qed.

  Lemma test:
    forall σ ty v v',
      v' = Vundef ->
      val_related σ ty v v' ->
      v = Vundef.
  Proof.
    intros * Hv' Hval_related; induction Hval_related;
      try (by inversion Hv'); auto.
  Succeed Qed. Abort.

  (** This seems odd, but it's relevant to the (former) proof that [anyR] is
  fractional; currently unused. *)
  Lemma primR_uninitR {resolve} ty q1 q2 v :
    primR ty q1 v |--
    uninitR ty q2 -*
    primR ty (q1 ⋅ q2) Vundef.
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
  Parameter anyR : ∀ {resolve} (ty : type) (q : cQp.t), Rep.
  #[global] Arguments anyR {resolve} ty q : rename.
  #[global] Declare Instance anyR_timeless : ∀ resolve ty q, Timeless (anyR ty q).
  #[global] Declare Instance anyR_cfractional : ∀ resolve ty, CFractional (anyR ty).
  #[global] Declare Instance anyR_observe_frac_valid resolve ty : CFracValid0 (anyR ty).

  Axiom primR_anyR : ∀ resolve t q v, primR t q v |-- anyR t q.
  Axiom uninitR_anyR : ∀ resolve t q, uninitR t q |-- anyR t q.
  Axiom tptsto_raw_anyR : forall resolve p q r, tptsto Tu8 q p (Vraw r) |-- p |-> anyR Tu8 q.
  #[global] Declare Instance anyR_type_ptr_observe σ ty q : Observe (type_ptrR ty) (anyR ty q).

  #[global] Instance anyR_as_fractional resolve ty : AsCFractional0 (anyR ty).
  Proof. solve_as_cfrac. Qed.

  Axiom _at_anyR_ptr_congP_transport : forall {σ} p p' ty q,
    ptr_congP σ p p' ** type_ptr ty p' |-- p |-> anyR ty q -* p' |-> anyR ty q.
End with_cpp.

#[global] Typeclasses Opaque primR.
#[global] Opaque primR.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (********************* DERIVED CONCEPTS ****************************)
  #[global] Instance validR_persistent : Persistent validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_timeless : Timeless validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_affine : Affine validR.
  Proof. rewrite validR_eq; refine _. Qed.

  Import heap_notations.INTERNAL.

  Lemma monPred_at_validR p : validR p -|- valid_ptr p.
  Proof. by rewrite validR_eq. Qed.
  Lemma _at_validR (p : ptr) : _at p validR -|- valid_ptr p.
  Proof. by rewrite validR_eq _at_eq /_at_def. Qed.

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

  #[global] Instance type_ptrR_persistent t : Persistent (type_ptrR t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.
  #[global] Instance type_ptrR_timeless t : Timeless (type_ptrR t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.
  #[global] Instance type_ptrR_affine t : Affine (type_ptrR t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.

  Lemma monPred_at_type_ptrR ty p : type_ptrR ty p -|- type_ptr ty p.
  Proof. by rewrite type_ptrR_eq. Qed.
  Lemma _at_type_ptrR (p : ptr) ty : _at p (type_ptrR ty) -|- type_ptr ty p.
  Proof. by rewrite type_ptrR_eq _at_eq. Qed.



  Lemma svalidR_validR : svalidR |-- validR.
  Proof.
    rewrite validR_eq/validR_def svalidR_eq/svalidR_def.
    constructor =>p /=. by apply strict_valid_valid.
  Qed.
  Lemma type_ptrR_svalidR ty : type_ptrR ty |-- svalidR.
  Proof.
    rewrite type_ptrR_eq/type_ptrR_def svalidR_eq/svalidR_def.
    constructor =>p /=. by apply type_ptr_strict_valid.
  Qed.
  Lemma type_ptrR_validR ty : type_ptrR ty |-- validR.
  Proof. by rewrite type_ptrR_svalidR svalidR_validR. Qed.

  #[global] Instance svalidR_validR_observe : Observe validR svalidR.
  Proof. rewrite svalidR_validR. red; iIntros "#$". Qed.
  #[global] Instance type_ptrR_svalidR_observe t : Observe svalidR (type_ptrR t).
  Proof. rewrite type_ptrR_svalidR; red; iIntros "#$". Qed.

  Definition nullR_def : Rep :=
    as_Rep (fun addr => [| addr = nullptr |]).
  Definition nullR_aux : seal (@nullR_def). Proof. by eexists. Qed.
  Definition nullR := nullR_aux.(unseal).
  Definition nullR_eq : @nullR = _ := nullR_aux.(seal_eq).

  #[global] Hint Opaque nullR : typeclass_instances.

  #[global] Instance nullR_persistent : Persistent nullR.
  Proof. rewrite nullR_eq. apply _. Qed.
  #[global] Instance nullR_affine : Affine nullR.
  Proof. rewrite nullR_eq. apply _. Qed.
  #[global] Instance nullR_timeless : Timeless nullR.
  Proof. rewrite nullR_eq. apply _. Qed.
  #[global] Instance nullR_fractional : Fractional (λ _, nullR).
  Proof. apply _. Qed.
  #[global] Instance nullR_as_fractional q : AsFractional nullR (λ _, nullR) q.
  Proof. exact: Build_AsFractional. Qed.
  #[global] Instance nullR_cfractional : CFractional (λ _, nullR).
  Proof. apply _. Qed.
  #[global] Instance nullR_as_cfractional q : AsCFractional nullR (λ _, nullR) q.
  Proof. solve_as_cfrac. Qed.

  Definition nonnullR_def : Rep :=
    as_Rep (fun addr => [| addr <> nullptr |]).
  Definition nonnullR_aux : seal (@nonnullR_def). Proof. by eexists. Qed.
  Definition nonnullR := nonnullR_aux.(unseal).
  Definition nonnullR_eq : @nonnullR = _ := nonnullR_aux.(seal_eq).

  #[global] Hint Opaque nonnullR : typeclass_instances.

  #[global] Instance nonnullR_persistent : Persistent nonnullR.
  Proof. rewrite nonnullR_eq. apply _. Qed.
  #[global] Instance nonnullR_affine : Affine nonnullR.
  Proof. rewrite nonnullR_eq. apply _. Qed.
  #[global] Instance nonnullR_timeless : Timeless nonnullR.
  Proof. rewrite nonnullR_eq. apply _. Qed.

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

  Lemma null_nonnull (R : Rep) : nullR |-- nonnullR -* R.
  Proof.
    rewrite nullR_eq /nullR_def nonnullR_eq /nonnullR_def.
    constructor=>p /=. rewrite monPred_at_wand/=.
    by iIntros "->" (? <-%ptr_rel_elim) "%".
  Qed.

  Lemma null_validR : nullR |-- validR.
  Proof.
    rewrite nullR_eq /nullR_def validR_eq /validR_def.
    constructor => p /=. iIntros "->". iApply valid_ptr_nullptr.
  Qed.


  (** [blockR sz q] represents [q] ownership of a contiguous chunk of
      [sz] bytes without any C++ structure on top of it. *)
  Definition blockR_def {σ} sz (q : cQp.t) : Rep :=
    _offsetR (o_sub σ Tu8 (Z.of_N sz)) validR **
    (* ^ Encodes valid_ptr (this .[ Tu8 ! sz]). This is
    necessary to get [l |-> blockR n -|- l |-> blockR n ** l .[ Tu8 ! m] |-> blockR 0]. *)
    [∗list] i ∈ seq 0 (N.to_nat sz),
      _offsetR (o_sub σ Tu8 (Z.of_nat i)) (anyR (resolve:=σ) Tu8 q).
  Definition blockR_aux : seal (@blockR_def). Proof. by eexists. Qed.
  Definition blockR := blockR_aux.(unseal).
  Definition blockR_eq : @blockR = _ := blockR_aux.(seal_eq).
  #[global] Arguments blockR {_} _%N _%Qp.

  #[global] Instance blockR_timeless {resolve : genv} sz q :
    Timeless (blockR sz q).
  Proof. rewrite blockR_eq /blockR_def. unfold_at. apply _. Qed.
  #[global] Instance blockR_cfractional resolve sz :
    CFractional (blockR sz).
  Proof. rewrite blockR_eq. apply _. Qed.
  #[global] Instance blockR_as_cfractional {resolve : genv} sz :
    AsCFractional0 (blockR sz).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance blockR_observe_frac_valid {resolve : genv} sz :
    TCLt (0 ?= sz)%N ->
    CFracValid0 (blockR sz).
  Proof.
    rewrite TCLt_N blockR_eq/blockR_def. intros.
    destruct (N.to_nat sz) eqn:?; [ lia | ] => /=.
    solve_cfrac_valid.
  Qed.

  (* [tblockR ty] is a [blockR] that is the size of [ty] and properly aligned.
   * it is a convenient short-hand since it happens frequently, but there is nothing
   * special about it.
   *)
  Definition tblockR {σ} (ty : type) (q : cQp.t) : Rep :=
    match size_of σ ty , align_of ty with
    | Some sz , Some al => blockR (σ:=σ) sz q ** alignedR al
    | _ , _  => False
    end.

  #[global] Instance tblockR_timeless ty q :
    Timeless (tblockR ty q).
  Proof. rewrite/tblockR. case_match; apply _. Qed.
  #[global] Instance tblockR_cfractional ty :
    CFractional (tblockR ty).
  Proof.
    rewrite/tblockR. do 2!(case_match; last by apply _).
    apply _.
  Qed.
  #[global] Instance tblockR_as_cfractional ty : AsCFractional0 (tblockR ty).
  Proof. solve_as_cfrac. Qed.
  #[global] Instance tblockR_observe_frac_valid ty n :
    SizeOf ty n -> TCLt (0 ?= n)%N ->
    CFracValid0 (tblockR ty).
  Proof.
    rewrite/tblockR=>-> ?. case_match; solve_cfrac_valid.
  Qed.

  #[global] Instance identityR_timeless cls mdc q : Timeless (identityR cls mdc q) := _.
  #[global] Instance identityR_cfractional cls mdc : CFractional (identityR cls mdc) := _.
  #[global] Instance identityR_as_frac cls mdc :
    AsCFractional0 (identityR cls mdc).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance identityR_strict_valid cls mdc q : Observe svalidR (identityR cls mdc q).
  Proof.
    red. eapply Rep_entails_at. intros.
    rewrite _at_as_Rep _at_pers svalidR_eq _at_as_Rep.
    apply identity_strict_valid.
  Qed.
  #[global] Instance identity_not_null p cls path q : Observe [| p <> nullptr |] (p |-> identityR cls path q).
  Proof.
    red.
    iIntros "X".
    destruct (decide (p = nullptr)); eauto.
    iDestruct (observe (p |-> svalidR) with "X") as "#SV".
    subst; rewrite _at_svalidR not_strictly_valid_ptr_nullptr.
    iDestruct "SV" as "[]".
  Qed.

  (** Observing [type_ptr] *)
  #[global]
  Instance primR_type_ptr_observe ty q v : Observe (type_ptrR ty) (primR ty q v).
  Proof.
    red. rewrite primR_eq/primR_def.
    apply Rep_entails_at => p. rewrite _at_as_Rep _at_pers _at_type_ptrR.
    apply: observe.
  Qed.
  #[global]
  Instance uninitR_type_ptr_observe ty q : Observe (type_ptrR ty) (uninitR ty q).
  Proof.
    red. rewrite uninitR_eq/uninitR_def.
    apply Rep_entails_at => p. rewrite _at_as_Rep _at_pers _at_type_ptrR.
    apply: observe.
  Qed.

  (** Observing [valid_ptr] *)
  #[global]
  Instance primR_valid_observe {ty q v} : Observe validR (primR ty q v).
  Proof. rewrite -svalidR_validR -type_ptrR_svalidR; refine _. Qed.
  #[global]
  Instance anyR_valid_observe {ty q} : Observe validR (anyR ty q).
  Proof. rewrite -svalidR_validR -type_ptrR_svalidR; refine _. Qed.
  #[global]
  Instance uninitR_valid_observe {ty q} : Observe validR (uninitR ty q).
  Proof. rewrite -svalidR_validR -type_ptrR_svalidR; refine _. Qed.

  #[global]
  Instance observe_type_ptr_pointsto (p : ptr) ty (R : Rep) :
    Observe (type_ptrR ty) R -> Observe (type_ptr ty p) (_at p R).
  Proof. rewrite -_at_type_ptrR. apply _at_observe. Qed.

  #[global] Instance type_ptrR_size_observe ty :
    Observe [| is_Some (size_of σ ty) |] (type_ptrR ty).
  Proof.
    apply monPred_observe_only_provable => p.
    rewrite monPred_at_type_ptrR. apply _.
  Qed.

  #[global]
  Instance null_valid_observe : Observe validR nullR.
  Proof. rewrite -null_validR. refine _. Qed.

  Lemma off_validR o
    (Hv : ∀ p, valid_ptr (p ,, o) |-- valid_ptr p) :
    _offsetR o validR |-- validR.
  Proof.
    apply Rep_entails_at => p. by rewrite _at_offsetR !_at_validR.
  Qed.

  Lemma _field_validR f : _offsetR (_field f) validR |-- validR.
  Proof. apply off_validR => p. apply _valid_ptr_field. Qed.

  (** Observation of [nonnullR] *)
  #[global]
  Instance primR_nonnull_observe {ty q v} :
    Observe nonnullR (primR ty q v).
  Proof.
    rewrite nonnullR_eq primR_eq. apply monPred_observe=>p /=. apply _.
  Qed.
  #[global]
  Instance uninitR_nonnull_observe {ty q} :
    Observe nonnullR (uninitR ty q).
  Proof.
    rewrite nonnullR_eq uninitR_eq. apply monPred_observe=>p /=. apply _.
  Qed.
  Axiom anyR_nonnull_observe : ∀ {ty q}, Observe nonnullR (anyR ty q).
  #[global] Existing Instance anyR_nonnull_observe.

  #[global] Instance blockR_nonnull n q :
    TCLt (0 ?= n)%N -> Observe nonnullR (blockR n q).
  Proof.
    rewrite TCLt_N blockR_eq/blockR_def.
    destruct (N.to_nat n) eqn:Hn; [ lia | ] => {Hn} /=.
    rewrite o_sub_0 ?_offsetR_id; [ | by eauto].
    apply _.
  Qed.
  #[global] Instance blockR_valid_ptr sz q : Observe validR (blockR sz q).
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

  #[global] Instance tblockR_nonnull n ty q :
    SizeOf ty n -> TCLt (0 ?= n)%N ->
    Observe nonnullR (tblockR ty q).
  Proof.
    intros Heq ?. rewrite/tblockR {}Heq.
    case_match; by apply _.
  Qed.

  #[global] Instance tblockR_valid_ptr ty q : Observe validR (tblockR ty q).
  Proof.
    rewrite /tblockR. case_match; refine _.
    case_match; refine _.
  Qed.

  #[global] Instance type_ptrR_observe_nonnull ty :
    Observe nonnullR (type_ptrR ty).
  Proof.
    apply monPred_observe=>p /=.
    rewrite monPred_at_type_ptrR nonnullR_eq /=. refine _.
  Qed.
End with_cpp.

#[global] Typeclasses Opaque identityR.
#[global] Typeclasses Opaque type_ptrR validR svalidR alignedR.

#[deprecated(note="since 2022-04-07; use `nonnullR` instead")]
Notation is_nonnull := nonnullR (only parsing).
#[deprecated(note="since 2022-04-07; use `nonnullR_eq` instead")]
Notation is_nonnull_eq := nonnullR_eq (only parsing).
#[deprecated(note="since 2022-04-07; use `nonnullR_def` instead")]
Notation is_nonnull_def := nonnullR_def (only parsing).

#[deprecated(note="since 2022-04-07; use `nullR` instead")]
Notation is_null := nullR (only parsing).
#[deprecated(note="since 2022-04-07; use `nullR_eq` instead")]
Notation is_null_eq := nullR_eq (only parsing).
#[deprecated(note="since 2022-04-07; use `nullR_def` instead")]
Notation is_null_def := nullR_def (only parsing).
