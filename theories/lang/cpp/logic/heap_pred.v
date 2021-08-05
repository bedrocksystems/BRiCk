(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From iris.bi Require Export monpred.
From iris.proofmode Require Import tactics monpred.
Require Import iris.bi.lib.fractional.
From iris_string_ident Require Import ltac2_string_ident.

Require Import bedrock.prelude.base.

From bedrock.lang.cpp Require Import
     semantics ast logic.pred logic.path_pred logic.rep logic.wp.
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

  Definition refR_def (ty : type) (p : ptr) : Rep :=
    as_Rep (fun addr => [| addr = p |]).
  Definition refR_aux : seal (@refR_def). Proof. by eexists. Qed.
  Definition refR := refR_aux.(unseal).
  Definition refR_eq : @refR = _ := refR_aux.(seal_eq).

  (* this is the core definition that the program logic will be based on.
     it is really an assertion about assembly.
   *)
  Definition cptrR_def {resolve : genv} (fs : function_spec) : Rep :=
    as_Rep (fun p =>
         valid_ptr p **
         Forall (ti : thread_info), □ (Forall vs Q,
         [| List.length vs = List.length fs.(fs_arguments) |] -*
         fs.(fs_spec) ti vs Q -*
         fspec resolve.(genv_tu).(globals) (type_of_spec fs) (Vptr p) vs Q)). (** TODO *)
  Definition cptrR_aux : seal (@cptrR_def). Proof. by eexists. Qed.
  Definition cptrR := cptrR_aux.(unseal).
  Definition cptrR_eq : @cptrR = _ := cptrR_aux.(seal_eq).
End defs.

Global Instance: Params (@cptrR) 3 := {}.

Arguments refR {_ Σ} ty v : rename.
Arguments cptrR {_ Σ resolve} _ : rename.

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

  Global Instance primR_timeless resolve ty q v
    : Timeless (primR ty q v).
  Proof. rewrite primR_eq. apply _. Qed.

  Global Instance primR_fractional resolve ty v :
    Fractional (λ q, primR ty q v).
  Proof. rewrite primR_eq. apply _. Qed.
  Global Instance primR_as_fractional resolve ty q v :
    AsFractional (primR ty q v) (λ q, primR ty q v) q.
  Proof. constructor. done. apply _. Qed.

  Global Instance primR_observe_frac_valid resolve ty (q : Qp) v :
    Observe [| q ≤ 1 |]%Qp (primR ty q v).
  Proof. rewrite primR_eq. apply _. Qed.

  Global Instance primR_observe_agree resolve ty q1 q2 v1 v2 :
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
      uninitialized.

      TODO generalize this to support aggregate types
   *)
  Definition anyR_def {resolve} (ty : type) (q : Qp) : Rep :=
    (Exists v, primR ty q v) \\// uninitR ty q.
  Definition anyR_aux : seal (@anyR_def). Proof. by eexists. Qed.
  Definition anyR := anyR_aux.(unseal).
  Definition anyR_eq : @anyR = _ := anyR_aux.(seal_eq).
  Global Arguments anyR {resolve} ty q : rename.

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
    Observe [| q ≤ 1 |]%Qp (anyR ty q).
  Proof. rewrite anyR_eq. apply _. Qed.

  Global Instance refR_persistent ty p : Persistent (refR ty p).
  Proof. rewrite refR_eq. apply _. Qed.
  Global Instance refR_affine ty p : Affine (refR ty p).
  Proof. rewrite refR_eq. apply _. Qed.
  Global Instance refR_timeless ty p : Timeless (refR ty p).
  Proof. rewrite refR_eq. apply _. Qed.

  #[global] Instance cptrR_persistent {resolve s} : Persistent (cptrR s).
  Proof. rewrite cptrR_eq. apply _. Qed.
  #[global] Instance cptrR_affine {resolve s} : Affine (cptrR s).
  Proof. rewrite cptrR_eq. apply _. Qed.

  (* NOTE this should become an instance. *)
  Lemma cptrR_valid_observe {resolve:genv} (p : ptr) f : Observe (valid_ptr p) (_at p (cptrR f)).
  Proof.
    apply observe_intro_persistent; refine _.
    rewrite cptrR_eq/cptrR_def _at_as_Rep.
    iIntros "[$ _]".
  Qed.

  Lemma cptrR_fs_impl {resolve} f g :
    pureR (fs_impl f g) |-- cptrR f -* cptrR g.
  Proof.
    rewrite cptrR_eq/cptrR_def /pureR /as_Rep.
    constructor => p; rewrite Rep_wand_force; iIntros "#(%ty & fs_impl)" => /=.
    iIntros "(val & #rest)"; iFrame. iIntros (ti vs Q len).
    rewrite ty. iSpecialize ("rest" $! ti). iModIntro. iIntros "fs_g".
    iApply "rest"; first by apply length_type_of_spec in ty; rewrite -ty len.
    by iApply "fs_impl".
  Qed.

(* TODO: Proper wrt [genv_leq]. *)
  #[global] Instance cptrR_ne {resolve} : NonExpansive cptrR.
  Proof.
    intros n P Q HPQ. rewrite cptrR_eq. rewrite/cptrR_def.
    rewrite (length_fs_arguments_ne _ _ _ HPQ) (type_of_spec_ne _ _ _ HPQ).
    apply as_Rep_ne=>p. (do 2!f_equiv)=>ti. (do 2!f_equiv)=>vs. f_equiv=>K.
    do 2!f_equiv. by apply fs_spec_ne.
  Qed.
  #[global] Instance cptrR_proper {resolve} : Proper (equiv ==> equiv) cptrR.
  Proof. exact: ne_proper. Qed.

  #[global] Instance cptrR_mono {resolve} : Proper (fs_entails ==> (⊢)) cptrR.
  Proof.
    intros ??; rewrite /fs_entails/flip => impl. iApply cptrR_fs_impl.
    by rewrite -impl pureR_emp.
  Qed.

  #[global] Instance cptrR_flip_mono {resolve} : Proper (flip fs_entails ==> flip (⊢)) cptrR.
  Proof. by intros ?? <-. Qed.

End with_cpp.

Typeclasses Opaque primR.
Global Opaque primR.

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
  Global Instance anyR_nonnull {σ} ty q :
    Observe is_nonnull (anyR (resolve:=σ) ty q).
  Proof. rewrite anyR_eq. apply _. Qed.

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

  Global Instance alignedR_divide_mono :
    Proper (flip N.divide ==> bi_entails) alignedR.
  Proof.
    intros m n ?.
    rewrite alignedR_eq /alignedR_def. constructor=>p/=. iIntros "!%".
    exact: aligned_ptr_divide_weaken.
  Qed.

  Global Instance alignedR_divide_flip_mono :
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

  #[global] Instance blockR_observe_frac_valid resolve sz (q : Qp) : (0 < sz)%N ->
    Observe [| q ≤ 1 |]%Qp (blockR sz q).
  Proof.
    rewrite blockR_eq/blockR_def.
    intros.
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

  #[global]
  Instance anyR_type_ptr_observe σ ty q : Observe (type_ptrR ty) (anyR ty q).
  Proof.
    red. rewrite anyR_eq/anyR_def.
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
  Instance primR_nonnull_observe {σ : genv} {ty q v} :
    Observe is_nonnull (primR ty q v).
  Proof.
    apply monPred_observe => p.
    rewrite primR_eq/primR_def is_nonnull_eq/is_nonnull_def/=. refine _.
  Qed.
  #[global]
  Instance uninitR_nonnull_observe {σ : genv} {ty q} :
    Observe is_nonnull (uninitR ty q).
  Proof.
    apply monPred_observe => p.
    rewrite uninitR_eq/uninitR_def is_nonnull_eq/is_nonnull_def/=.
    refine _.
  Qed.
  #[global]
  Instance anyR_nonnull_observe {σ : genv} {ty q} :
    Observe is_nonnull (anyR ty q).
  Proof.
    apply monPred_observe => p. rewrite anyR_eq/anyR_def.
    red. iIntros "[X | X]".
    - iDestruct "X" as (?) "X". iDestruct (observe is_nonnull with "X") as "#$".
    - iDestruct (observe is_nonnull with "X") as "#$".
  Qed.
  #[global]
  Instance blockR_nonnull {σ : genv} (p : ptr) n q:
    (0 < n)%N -> Observe is_nonnull (blockR n q).
  Proof.
    iIntros (?) "Hb".
    rewrite blockR_eq/blockR_def. (** TODO upstream *)
    iDestruct "Hb" as "[_ Hb]".
    destruct (N.to_nat n) eqn:?; [ lia | ] => /=.
    iDestruct "Hb" as "[Hany _]".
    rewrite o_sub_0; [ | by eauto].
    rewrite _offsetR_id.
    iDestruct (observe is_nonnull with "Hany") as "#$".
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

  #[global] Instance tblockR_valid_ptr {σ} ty q : Observe validR (tblockR ty q).
  Proof.
    rewrite /tblockR. case_match; refine _.
    case_match; refine _.
  Qed.

End with_cpp.

Typeclasses Opaque identityR.
Typeclasses Opaque type_ptrR validR svalidR alignedR.

Instance Persistent_spec `{Σ:cpp_logic ti} {resolve:genv} nm s :
  Persistent (_at (Σ:=Σ) (_global nm) (cptrR s)) := _.
