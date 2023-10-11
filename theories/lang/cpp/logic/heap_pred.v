(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi.apps Require Export locker.

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

  (** ** Object derivations
      The path from the object to its complete object.
   *)
  Definition derivationR {σ : genv} (cls : globname) (mdc : list globname)
             (q : cQp.t) : Rep :=
    as_Rep (mdc_path cls mdc q).

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

mlock Definition alignedR `{Σ : cpp_logic} (al : N) : Rep :=
  as_Rep (λ p, [| aligned_ptr al p |]).
#[global] Arguments alignedR {_ Σ} _.

(* [Rep] version of (to be deprecated) [aligned_ptr_ty] *)
mlock Definition aligned_ofR `{Σ : cpp_logic} {σ} (ty : type) : Rep :=
  ∃ align : N, [| align_of ty = Some align |] ** alignedR align.
#[global] Arguments aligned_ofR {_ Σ σ} _.

mlock Definition nonnullR `{Σ : cpp_logic} : Rep :=
  as_Rep (fun addr => [| addr <> nullptr |]).
#[global] Arguments nonnullR {_ _} : assert.	(* mlock bug *)

Section nonnullR.
  Context `{Σ : cpp_logic, σ : genv}.

  #[global] Instance nonnullR_persistent : Persistent nonnullR.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance nonnullR_affine : Affine nonnullR.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance nonnullR_timeless : Timeless nonnullR.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance type_ptrR_observe_nonnull ty :
    Observe nonnullR (type_ptrR ty).
  Proof.
    rewrite nonnullR.unlock type_ptrR_eq /type_ptrR_def.
    exact: as_Rep_observe.
  Qed.
End nonnullR.

(**
[tptstoR ty q v] is [q] ownership of a memory location of type [ty]
storing the value [v].

Whereas [tptstoR] is precise w.r.t. the value (i.e., given two
fractions, one learns the values are equal), [tptstoR_fuzzyR ty q v]
lets one view the contents of the memory as either [v] or a related
value [v'] (see [val_related] and [tptsto_fuzzyR_val_related]).
*)
mlock Definition tptstoR `{Σ : cpp_logic} {σ : genv} (ty : type) (q : cQp.t) (v : val) : Rep :=
  as_Rep (fun p => tptsto ty q p v).
#[global] Arguments tptstoR {_ _ _} _ _ _ : assert.	(* mlock bug *)

mlock Definition tptsto_fuzzyR `{Σ : cpp_logic, σ : genv} (ty : type) (q : cQp.t) (v : val) : Rep :=
  Exists v', [| val_related ty v v' |] ** tptstoR ty q v'.
#[global] Arguments tptsto_fuzzyR {_ _ _} _ _ _ : assert.	(* mlock bug *)

Section tptstoR.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** [tptstoR] *)

  Lemma _at_tptstoR (p : ptr) ty q v : p |-> tptstoR ty q v -|- tptsto ty q p v.
  Proof. by rewrite tptstoR.unlock _at_as_Rep. Qed.

  #[global] Instance: Params (@tptstoR) 2 := {}.

  #[global] Instance tptstoR_proper :
    Proper (genv_eq ==> eq ==> eq ==> eq ==> (⊣⊢)) (@tptstoR _ _).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite tptstoR.unlock. by setoid_rewrite Hσ.
  Qed.
  #[global] Instance tptstoR_mono :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> (⊢)) (@tptstoR _ _).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite tptstoR.unlock. by setoid_rewrite Hσ.
  Qed.

  #[global] Instance tptstoR_timeless ty q v :
    Timeless (tptstoR ty q v).
  Proof. rewrite tptstoR.unlock. apply _. Qed.

  #[global] Instance tptstoR_cfractional ty :
    CFractional1 (tptstoR ty).
  Proof. rewrite tptstoR.unlock. apply _. Qed.
  #[global] Instance tptstoR_as_cfractional ty :
    AsCFractional1 (tptstoR ty).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance tptstoR_observe_cfrac_valid ty :
    CFracValid1 (tptstoR ty).
  Proof. rewrite tptstoR.unlock. solve_cfrac_valid. Qed.

  #[global] Instance tptstoR_observe_agree ty q1 q2 v1 v2 :
    Observe2 [| v1 = v2 |] (tptstoR ty q1 v1) (tptstoR ty q2 v2).
  Proof.
    rewrite tptstoR.unlock; apply: as_Rep_only_provable_observe_2=> p.
  Qed.

  #[global] Instance _at_tptstoR_welltyped p ty q v :
    Observe (has_type_or_undef v ty) (p |-> tptstoR ty q v).
  Proof. rewrite _at_tptstoR. refine _. Qed.
  #[global] Instance tptstoR_welltyped ty q v :
    Observe (pureR (has_type_or_undef v ty)) (tptstoR ty q v).
  Proof.
    apply observe_at=>p. rewrite _at_pureR. apply _.
  Qed.

  #[global] Instance _at_tptstoR_reference_to p ty q v :
    Observe (reference_to ty p) (p |-> tptstoR ty q v) | 100.
  Proof. rewrite _at_tptstoR. refine _. Qed.

  #[global] Instance tptstoR_type_ptrR ty q v :
    Observe (type_ptrR ty) (tptstoR ty q v).
  Proof.
    rewrite tptstoR.unlock type_ptrR_eq/type_ptrR_def.
    apply as_Rep_observe. intros; apply tptsto_type_ptr.
  Qed.

  #[global] Instance tptstoR_nonnull ty q v : Observe nonnullR (tptstoR ty q v).
  Proof. trans (type_ptrR ty); apply _. Qed.

  (**
  The various [tptsto] accessors in this file support low-level
  mechanisms like constant casts (see [primR_wp_const_val]) and
  transporting resources along [ptr_congP] and [offset_congP] (see,
  e.g., [rawR_ptr_congP_transport]).
  *)
  Lemma tptstoR_tptsto_acc (p : ptr) ty q v :
    p |-> tptstoR ty q v |--
      tptsto ty q p v **
      (Forall p' q' v', tptsto ty q' p' v' -* p' |-> tptstoR ty q' v').
  Proof.
    setoid_rewrite _at_tptstoR. iIntros "$". auto.
  Qed.

  (** [tptsto_fuzzyR] *)

  Lemma _at_tptsto_fuzzyR (p : ptr) ty q v :
    p |-> tptsto_fuzzyR ty q v -|-
      Exists v', [| val_related ty v v' |] ** p |-> tptstoR ty q v'.
  Proof.
    rewrite tptsto_fuzzyR.unlock. rewrite _at_exists. f_equiv=>v'.
    by rewrite _at_sep _at_only_provable.
  Qed.

  #[global] Instance: Params (@tptsto_fuzzyR) 2 := {}.
  #[global] Instance tptsto_fuzzyR_mono :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> bi_entails) (@tptsto_fuzzyR _ _).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite tptsto_fuzzyR.unlock. by setoid_rewrite Hσ.
  Qed.
  #[global] Instance tptsto_fuzzyR_flip_mono :
    Proper (flip genv_leq ==> eq ==> eq ==> eq ==> flip bi_entails) (@tptsto_fuzzyR _ _).
  Proof. repeat intro. by apply tptsto_fuzzyR_mono. Qed.
  #[global] Instance tptsto_fuzzyR_proper :
    Proper (genv_eq ==> eq ==> eq ==> eq ==> equiv) (@tptsto_fuzzyR _ _).
  Proof.
    intros σ1 σ2 [??] ??? ??? ???. split'; by apply tptsto_fuzzyR_mono.
  Qed.

  #[global] Instance tptsto_fuzzyR_timeless : Timeless3 tptsto_fuzzyR.
  Proof. rewrite tptsto_fuzzyR.unlock. apply _. Qed.

  #[global] Instance tptsto_fuzzyR_cfractional ty : CFractional1 (tptsto_fuzzyR ty).
  Proof. rewrite tptsto_fuzzyR.unlock. apply _. Qed.
  #[global] Instance tptsto_fuzzyR_cfrac_valid ty : CFracValid1 (tptsto_fuzzyR ty).
  Proof. rewrite tptsto_fuzzyR.unlock. solve_cfrac_valid. Qed.

  #[global] Instance tptsto_fuzzyR_welltyped ty q v :
    Observe (pureR (has_type_or_undef v ty)) (tptsto_fuzzyR ty q v).
  Proof.
    rewrite tptsto_fuzzyR.unlock. iIntros "(% & % & R)".
    iDestruct (tptstoR_welltyped with "R") as "#?".
    by rewrite has_type_or_undef_val_related.
  Qed.
  #[global] Instance _at_tptsto_fuzzyR_welltyped p ty q v :
    Observe (has_type_or_undef v ty) (p |-> tptsto_fuzzyR ty q v).
  Proof. apply _at_observe_pureR, _. Qed.

  #[global] Instance _at_tptsto_fuzzyR_reference_to p ty q v :
    Observe (reference_to ty p) (p |-> tptsto_fuzzyR ty q v) | 100.
  Proof. rewrite _at_tptsto_fuzzyR. refine _. Qed.

  #[global] Instance tptsto_fuzzyR_type_ptrR ty q v :
    Observe (type_ptrR ty) (tptsto_fuzzyR ty q v).
  Proof. rewrite tptsto_fuzzyR.unlock. apply _. Qed.

  #[global] Instance tptsto_fuzzyR_nonnull ty q v :
    Observe nonnullR (tptsto_fuzzyR ty q v).
  Proof. rewrite tptsto_fuzzyR.unlock. apply _. Qed.

  #[global] Instance tptstoR_tptsto_fuzzyR_agree ty q1 q2 v1 v2 :
    Observe2 [| val_related ty v1 v2 |] (tptstoR ty q1 v1) (tptsto_fuzzyR ty q2 v2).
  Proof.
    rewrite tptsto_fuzzyR.unlock. iIntros "R1 (% & % & R2)".
    iDestruct (observe_2 [| _ = _ |] with "R1 R2") as %?. simplify_eq. auto.
  Qed.
  #[global] Instance tptsto_fuzzyR_agree ty q1 q2 v1 v2 :
    Observe2 [| val_related ty v1 v2 |] (tptsto_fuzzyR ty q1 v1) (tptsto_fuzzyR ty q2 v2).
  Proof.
    rewrite tptsto_fuzzyR.unlock. iIntros "(% & % & R1) (% & % & R2)".
    iDestruct (observe_2 [| _ = _ |] with "R1 R2") as %?. simplify_eq.
    iIntros "!> !%". by etrans.
  Qed.

  Lemma tptsto_fuzzyR_intro ty q v : tptstoR ty q v |-- tptsto_fuzzyR ty q v.
  Proof.
    rewrite tptsto_fuzzyR.unlock -(bi.exist_intro v). by iIntros "$".
  Qed.

  Lemma tptsto_fuzzyR_elim_r ty q1 q2 v1 v2 :
    tptstoR ty q1 v1 ** tptsto_fuzzyR ty q2 v2 |-- tptstoR ty (q1 + q2) v1.
  Proof.
    rewrite tptsto_fuzzyR.unlock. iIntros "(R1 & (% & % & R2))".
    iDestruct (observe_2 [| _ = _ |] with "R1 R2") as %?. simplify_eq.
    iCombine "R1 R2" as "$".
  Qed.
  Lemma tptsto_fuzzyR_elim_l ty q1 q2 v1 v2 :
    tptsto_fuzzyR ty q1 v1 ** tptstoR ty q2 v2 |-- tptstoR ty (q1 + q2) v2.
  Proof. by rewrite comm tptsto_fuzzyR_elim_r comm_L. Qed.

  Lemma tptsto_fuzzyR_val_related ty q v1 v2 :
    val_related ty v1 v2 ->
    tptsto_fuzzyR ty q v1 -|- tptsto_fuzzyR ty q v2.
  Proof.
    intros. rewrite tptsto_fuzzyR.unlock. f_equiv=>v'. do 2!f_equiv. split; by etrans.
  Qed.

  Lemma tptsto_fuzzyR_tptsto_acc (p : ptr) ty q v :
    p |-> tptsto_fuzzyR ty q v |--
      Exists v', [| val_related ty v v' |] ** tptsto ty q p v' **
      (Forall p' q' v', [| val_related ty v v' |] -* tptsto ty q' p' v' -* p' |-> tptsto_fuzzyR ty q' v).
  Proof.
    setoid_rewrite _at_tptsto_fuzzyR. iIntros "(%v' & %Hval & R)".
    iDestruct (tptstoR_tptsto_acc with "R") as "(R & HR)".
    iExists v'. iFrame (Hval) "R". iIntros (??? Hval') "R". iExists _. iFrame (Hval').
    iApply ("HR" with "R").
  Qed.
End tptstoR.

(**
[primR ty q v]: the argument pointer points to an initialized value
[v] of C++ type [ty].

NOTE [ty] *must* be a primitive type.
*)
mlock Definition primR `{Σ : cpp_logic, resolve : genv} (ty : type) (q : cQp.t) (v : val) : Rep :=
  [| ~~ is_raw v |] **
  (**
  NOTE: Clients use [primR (erase_qualifiers ty)] but we do not bake
  [erase_qualifiers] in to simplify our automation.

  TODO: In light of [has_type_drop_qualifiers], there's no need for
  [drop_qualifiers].
  *)
  pureR (has_type v (drop_qualifiers ty)) **
  tptsto_fuzzyR ty q v.
#[global] Arguments primR {_ _ _} _ _ _ : assert.	(* mlock bug *)

mlock Definition reference_toR `{Σ : cpp_logic, resolve : genv} (ty : type) : Rep :=
  as_Rep (reference_to ty).
#[global] Arguments reference_toR {_ _ _} _ : assert.	(* mlock bug *)

#[global] Instance reference_toR_knoweldge `{Σ : cpp_logic, resolve : genv}
  : Knowledge1 reference_toR.
Proof. rewrite reference_toR.unlock; intros. split; refine _. Qed.
#[global] Instance reference_toR_timeless `{Σ : cpp_logic, resolve : genv}
  : Timeless1 reference_toR.
Proof. rewrite reference_toR.unlock; intros. refine _. Qed.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** [varargsR ts_ps] is the ownership of a group of variadic arguments.
      The [type] is the type of the argument and the [ptr] is the location
      of the argument. *)
  Parameter varargsR : forall {σ : genv}, list (type * ptr) -> Rep.

  Lemma _at_reference_toR {σ : genv} ty (p : ptr) :
    p |-> reference_toR ty -|- reference_to ty p.
  Proof. by rewrite reference_toR.unlock _at_as_Rep. Qed.

  Lemma _at_primR {σ} (p : ptr) ty q v :
    p |-> primR ty q v -|-
      [| ~~ is_raw v |] **
      has_type v (drop_qualifiers ty) **
      p |-> tptsto_fuzzyR ty q v.
  Proof.
    by rewrite primR.unlock !_at_sep _at_only_provable _at_pureR.
  Qed.

  #[global] Instance: Params (@primR) 2 := {}.
  #[global] Instance primR_proper :
    Proper (genv_eq ==> (=) ==> (=) ==> (=) ==> (⊣⊢)) (@primR _ _).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite primR.unlock. by setoid_rewrite Hσ.
  Qed.
  #[global] Instance primR_mono :
    Proper (genv_leq ==> (=) ==> (=) ==> (=) ==> (⊢)) (@primR _ _).
  Proof.
    intros σ1 σ2 Hσ ??-> ??-> ??->.
    rewrite primR.unlock. by setoid_rewrite Hσ.
  Qed.

  #[global] Instance primR_timeless resolve ty q v
    : Timeless (primR ty q v).
  Proof. rewrite primR.unlock. apply _. Qed.

  #[global] Instance primR_cfractional resolve ty :
    CFractional1 (primR ty).
  Proof. rewrite primR.unlock. apply _. Qed.
  #[global] Instance primR_as_cfractional resolve ty :
    AsCFractional1 (primR ty).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance primR_observe_cfrac_valid resolve ty :
    CFracValid1 (primR ty).
  Proof. rewrite primR.unlock. solve_cfrac_valid. Qed.

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

  #[global] Instance primR_observe_agree {σ} ty q1 q2 v1 v2 :
    Observe2 [| v1 = v2 |] (primR ty q1 v1) (primR ty q2 v2).
  Proof.
    rewrite primR.unlock. iIntros "(% & _ & R1) (% & _ & R2)".
    iDestruct (observe_2 [| val_related _ _ _ |] with "R1 R2") as %?.
    eauto using val_related_not_raw.
  Qed.

  (* Typical [f] are [Vint], [Vn] etc; this gives agreement for [u64R] etc. *)
  #[global] Instance primR_observe_agree_constr resolve ty q1 q2 {A} f `{!Inj eq eq f} (v1 v2 : A) :
    Observe2 [| v1 = v2 |]
      (primR ty q1 (f v1))
      (primR ty q2 (f v2)).
  Proof. apply (observe2_inj f), _. Qed.

  #[global] Instance primR_observe_has_type resolve ty q v :
    Observe (pureR (has_type v ty)) (primR ty q v).
  Proof. rewrite primR.unlock has_type_drop_qualifiers. apply _. Qed.

  #[global] Instance _at_primR_observe_has_type resolve ty q v (p : ptr) :
    Observe (has_type v ty) (p |-> primR ty q v).
  Proof. apply: _at_observe_pureR. Qed.

  #[global] Instance primR_observe_has_type_prop resolve ty q v :
    Observe [| has_type_prop v ty |] (primR ty q v).
  Proof.
    apply observe_at=>p. rewrite _at_only_provable -has_type_has_type_prop.
    apply _.
  Qed.

  Lemma primR_has_type_prop {σ} ty q v :
    primR (resolve:=σ) ty q v |--
    primR (resolve:=σ) ty q v ** [| has_type_prop v ty |].
  Proof. apply: observe_elim. Qed.

  Lemma primR_tptsto_acc {σ} p ty q v :
    p |-> primR ty q v |--
      Exists v', [| val_related ty v v' |] ** tptsto ty q p v' **
      (Forall p' q' v', [| val_related ty v v' |] -* tptsto ty q' p' v' -* p' |-> primR ty q' v).
  Proof.
    setoid_rewrite _at_primR. iIntros "(%Hraw & #T & R)".
    iDestruct (tptsto_fuzzyR_tptsto_acc with "R") as "(%v' & %Hval & R & HR)".
    iExists v'. iFrame (Hval Hraw) "R T". iFrame "HR".
  Qed.

  #[global] Instance _at_primR_reference_to {σ} p ty q v :
    Observe (reference_to ty p) (p |-> primR ty q v) | 100.
  Proof. rewrite _at_primR. refine _. Qed.

  (**
     [uninitR ty q]: the argument pointer points to an uninitialized value [Vundef] of C++ type [ty].
     Unlike [primR], does not imply [has_type_prop].

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

  Lemma uninitR_tptstoR {σ} ty q : uninitR ty q -|- tptstoR ty q Vundef.
  Proof. by rewrite uninitR_eq /uninitR_def tptstoR.unlock. Qed.

  Lemma test:
    forall σ ty v v',
      v' = Vundef ->
      val_related ty v v' ->
      v = Vundef.
  Proof.
    intros * Hv' Hval_related.
    induction Hval_related;
      try (by inversion Hv'); auto.
  Succeed Qed. Abort.

  (** This seems odd, but it's relevant to the (former) proof that [anyR] is
  fractional; currently unused. *)
  Lemma primR_uninitR {resolve} ty q1 q2 v :
    primR ty q1 v |--
    uninitR ty q2 -*
    primR ty (q1 + q2) Vundef.
  Proof.
    rewrite primR.unlock uninitR_tptstoR. iIntros "(_ & #T & R1) R2".
    iDestruct (observe_2 [| val_related _ _ _ |] with "R2 R1") as %->%val_related_Vundef.
    iFrame "T". iDestruct (tptsto_fuzzyR_elim_l with "[$R1 $R2]") as "R".
    by iDestruct (tptsto_fuzzyR_intro with "R") as "$".
  Qed.

  (** [anyR] The argument pointers points to a value of C++ type [ty] that might be
      uninitialized.

      NOTE: this can be defined by recursion on [ty] assuming well-founded translation
            unit.
   *)
  Parameter anyR : ∀ {resolve} (ty : type) (q : cQp.t), Rep.
  #[global] Arguments anyR {resolve} ty q : rename.
  #[global] Declare Instance anyR_timeless : ∀ resolve ty q, Timeless (anyR ty q).
  #[global] Declare Instance anyR_cfractional : ∀ resolve ty, CFractional (anyR ty).
  #[global] Declare Instance anyR_observe_frac_valid resolve ty : CFracValid0 (anyR ty).

  (**
  For value types and reference types, [anyR] coincides with
  [tptstoR].
  *)
  Axiom anyR_tptstoR_val : ∀ {σ} t q, is_value_type t -> anyR t q -|- Exists v, tptstoR t q v.
  Axiom anyR_tptstoR_ref : ∀ {σ} t q, anyR (Tref t) q -|- Exists v, tptstoR (Tref t) q v.

  Lemma anyR_tptstoR_val_2 {σ} t q v : is_value_type t -> tptstoR t q v |-- anyR t q.
  Proof. intros. by rewrite anyR_tptstoR_val// -(bi.exist_intro v). Qed.
  Lemma anyR_tptstoR_ref_2 {σ} t q v : tptstoR (Tref t) q v |-- anyR (Tref t) q.
  Proof. intros. by rewrite anyR_tptstoR_ref -(bi.exist_intro v). Qed.

  Lemma anyR_tptsto_fuzzyR_val_2 {σ} t q v :
    is_value_type t -> tptsto_fuzzyR t q v |-- anyR t q.
  Proof.
    intros. rewrite tptsto_fuzzyR.unlock. iIntros "(% & % & R)".
    by rewrite anyR_tptstoR_val_2.
  Qed.

  (**
  TODO: With some minor cleanup we ought to be able to derive
  [primR_anyR], [uninitR_anyR] from [anyR_tptstoR_val],
  [anyR_tptstoR_ref].
  *)
  Axiom primR_anyR : ∀ {σ}  t q v, primR t q v |-- anyR t q.
  Axiom uninitR_anyR : ∀ {σ} t q, uninitR t q |-- anyR t q.

  #[global] Declare Instance anyR_type_ptr_observe σ ty q : Observe (type_ptrR ty) (anyR ty q).

  #[global] Instance anyR_as_fractional resolve ty : AsCFractional0 (anyR ty).
  Proof. solve_as_cfrac. Qed.

  Axiom _at_anyR_ptr_congP_transport : forall {σ} p p' ty q,
    ptr_congP σ p p' ** type_ptr ty p' |-- p |-> anyR ty q -* p' |-> anyR ty q.
End with_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (********************* DERIVED CONCEPTS ****************************)
  #[global] Instance validR_persistent : Persistent validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_timeless : Timeless validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_affine : Affine validR.
  Proof. rewrite validR_eq; refine _. Qed.

  Import rep_defs.INTERNAL.

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

  (** ** [alignedR] *)
  #[global] Instance alignedR_persistent {al} : Persistent (alignedR al).
  Proof. rewrite alignedR.unlock. apply _. Qed.
  #[global] Instance alignedR_affine {al} : Affine (alignedR al).
  Proof. rewrite alignedR.unlock. apply _. Qed.
  #[global] Instance alignedR_timeless {al} : Timeless (alignedR al).
  Proof. rewrite alignedR.unlock. apply _. Qed.

  #[global] Instance alignedR_divide_mono :
    Proper (flip N.divide ==> bi_entails) alignedR.
  Proof.
    intros m n ?.
    rewrite alignedR.unlock. constructor=>p/=. iIntros "!%".
    exact: aligned_ptr_divide_weaken.
  Qed.

  #[global] Instance alignedR_divide_flip_mono :
    Proper (N.divide ==> flip bi_entails) alignedR.
  Proof. solve_proper. Qed.

  Lemma alignedR_divide_weaken m n :
    (n | m)%N ->
    alignedR m ⊢ alignedR n.
  Proof. by move->. Qed.

  (* To use sparingly: we're deprecating [aligned_ptr] *)
  Lemma _at_alignedR (p : ptr) n :
    p |-> alignedR n -|- [| aligned_ptr n p |].
  Proof. by rewrite alignedR.unlock _at_as_Rep. Qed.

  #[global] Instance aligned_ofR_persistent {ty} : Persistent (aligned_ofR ty).
  Proof. rewrite aligned_ofR.unlock. apply _. Qed.
  #[global] Instance aligned_ofR_affine {ty} : Affine (aligned_ofR ty).
  Proof. rewrite aligned_ofR.unlock. apply _. Qed.
  #[global] Instance aligned_ofR_timeless {ty} : Timeless (aligned_ofR ty).
  Proof. rewrite aligned_ofR.unlock. apply _. Qed.

  Lemma aligned_ofR_aligned_ptr_ty p ty :
    p |-> aligned_ofR ty -|- [| aligned_ptr_ty ty p |].
  Proof.
    rewrite aligned_ofR.unlock alignedR.unlock /aligned_ptr_ty _at_exists only_provable_exist.
    f_equiv => n. rewrite _at_sep _at_as_Rep _at_only_provable.
    by iIntros "!%".
  Qed.

  Lemma type_ptrR_aligned_ofR ty :
    type_ptrR ty |-- aligned_ofR ty.
  Proof.
    apply Rep_entails_at => p.
    by rewrite _at_type_ptrR type_ptr_aligned_pure aligned_ofR_aligned_ptr_ty.
  Qed.

  Lemma type_ptr_aligned_ofR p ty :
    type_ptr ty p |-- p |-> aligned_ofR ty.
  Proof. by rewrite -type_ptrR_aligned_ofR _at_type_ptrR. Qed.

  Lemma has_type_noptr v ty :
    nonptr_prim_type ty ->
    has_type v ty -|- [| has_type_prop v ty |].
  Proof.
    intros; iSplit.
    iApply has_type_has_type_prop.
    by iApply has_type_prop_has_type_noptr.
  Qed.

  Lemma has_type_nullptr p :
    has_type (Vptr p) Tnullptr -|- p |-> nullR.
  Proof. by rewrite has_type_nullptr' nullR_eq _at_as_Rep. Qed.

  Lemma has_type_void v : has_type v Tvoid -|- [| v = Vvoid |].
  Proof. by rewrite has_type_noptr ?has_type_prop_void. Qed.

  Lemma has_type_ptr p ty :
    has_type (Vptr p) (Tpointer ty) -|- p |-> (validR ** aligned_ofR ty).
  Proof.
    by rewrite has_type_ptr' _at_sep _at_validR aligned_ofR_aligned_ptr_ty.
  Qed.

  (** ** [reference_to] *)
  #[global] Instance reference_to_valid ty p : Observe (valid_ptr p) (reference_to ty p).
  Proof. rewrite reference_to_elim. refine _. Qed.
  #[global] Instance reference_to_aligned ty p : Observe [| aligned_ptr_ty ty p |] (reference_to ty p).
  Proof. rewrite reference_to_elim. refine _. Qed.
  #[global] Instance reference_to_aligned_ofR ty (p : ptr) : Observe (p |-> aligned_ofR ty) (reference_to ty p).
  Proof. rewrite reference_to_elim aligned_ofR_aligned_ptr_ty. refine _. Qed.
  #[global] Instance reference_to_not_null ty p : Observe [| p <> nullptr |] (reference_to ty p).
  Proof. rewrite reference_to_elim. refine _. Qed.
  #[global] Instance reference_to_strict_valid ty p :
    TCEq (zero_sized_array ty) false ->
    Observe (strict_valid_ptr p) (reference_to ty p).
  Proof. rewrite reference_to_elim. move => ->. refine _. Qed.


  #[global] Instance reference_to_aligned_observe p ty :
    Observe (p |-> aligned_ofR ty) (reference_to ty p).
  Proof. rewrite aligned_ofR_aligned_ptr_ty reference_to_elim; refine _. Qed.
  #[global] Instance reference_to_valid_observe p ty :
    Observe (p |-> validR) (reference_to ty p).
  Proof. rewrite _at_validR reference_to_elim; refine _. Qed.

  Lemma null_nonnull (R : Rep) : nullR |-- nonnullR -* R.
  Proof.
    rewrite nullR_eq /nullR_def nonnullR.unlock.
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

  #[global] Instance derivationR_timeless cls mdc q : Timeless (derivationR cls mdc q) := _.
  #[global] Instance derivationR_cfractional cls mdc : CFractional (derivationR cls mdc) := _.
  #[global] Instance derivationR_as_frac cls mdc :
    AsCFractional0 (derivationR cls mdc).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance derivationR_strict_valid cls mdc q : Observe svalidR (derivationR cls mdc q).
  Proof.
    red. eapply Rep_entails_at. intros.
    rewrite _at_as_Rep _at_pers svalidR_eq _at_as_Rep.
    apply mdc_path_strict_valid.
  Qed.
  #[global] Instance mdc_path_not_null p cls path q : Observe [| p <> nullptr |] (p |-> derivationR cls path q).
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
  Proof. rewrite primR.unlock. apply _. Qed.
  #[global]
  Instance uninitR_type_ptr_observe ty q : Observe (type_ptrR ty) (uninitR ty q).
  Proof. rewrite uninitR_tptstoR. apply _. Qed.

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
  Proof. rewrite primR.unlock. apply _. Qed.
  #[global]
  Instance uninitR_nonnull_observe {ty q} :
    Observe nonnullR (uninitR ty q).
  Proof. rewrite uninitR_tptstoR. apply _. Qed.
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
      unfold N.to_nat. destruct (Pos.to_nat p) eqn:?; first lia.
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

  Lemma primR_tptsto_fuzzyR ty q v : primR ty q v |-- tptsto_fuzzyR ty q v.
  Proof. rewrite primR.unlock. iIntros "(_ & _ & $)". Qed.

  Lemma tptstoR_Vvoid_tptstoR_fuzzy q :
    tptstoR Tvoid q Vvoid -|- tptsto_fuzzyR Tvoid q Vvoid.
  Proof.
    rewrite tptsto_fuzzyR.unlock. split'.
    - iIntros "R". iExists Vvoid. by iFrame "R".
    - iIntros "(% & %Hval & R)". apply val_related_Vundef in Hval. by simplify_eq.
  Qed.
  Lemma tptsto_fuzzyR_Vvoid_primR q : tptsto_fuzzyR Tvoid q Vvoid -|- primR Tvoid q Vvoid.
  Proof.
    rewrite primR.unlock. rewrite left_id.
    by rewrite has_type_void pureR_only_provable only_provable_True// left_id.
  Qed.
  Lemma tptstoR_Vvoid_primR q : tptstoR Tvoid q Vvoid -|- primR Tvoid q Vvoid.
  Proof. by rewrite tptstoR_Vvoid_tptstoR_fuzzy tptsto_fuzzyR_Vvoid_primR. Qed.

  Definition is_raw_or_undef (v : val) : bool :=
    if v is (Vundef | Vraw _) then true else false.

  Lemma tptsto_fuzzyR_Vxxx_primR ty q v :
    ~~ is_raw_or_undef v -> tptsto_fuzzyR ty q v -|- primR ty q v.
  Proof.
    split'; try apply primR_tptsto_fuzzyR.
    rewrite primR.unlock. iIntros "R".
    iDestruct (observe_elim (pureR $ has_type_or_undef _ _) with "R") as "($ & #T)".
    rewrite has_type_or_undef_unfold -has_type_drop_qualifiers.
    rewrite pureR_or pureR_only_provable. iDestruct "T" as "[$ | ->]".
    by destruct v. done.
  Qed.

  Lemma tptstoR_Vxxx_primR ty q v :
    ~~ is_raw_or_undef v -> tptstoR ty q v |-- primR ty q v.
  Proof.
    intros. by rewrite tptsto_fuzzyR_intro tptsto_fuzzyR_Vxxx_primR.
  Qed.
End with_cpp.

mlock Definition structR `{Σ : cpp_logic} {σ : genv} (cls : globname) (q : cQp.t) : Rep :=
  as_Rep (fun p => struct_padding p cls q).
#[global] Arguments structR {_ Σ σ} cls q : assert.

mlock Definition unionR `{Σ : cpp_logic} {σ : genv} (cls : globname) (q : cQp.t) (i : option nat) : Rep :=
  as_Rep (fun p => union_padding p cls q i).
#[global] Arguments unionR {_ Σ σ} cls q i : assert.

Section padding.
  Context `{Σ : cpp_logic} {σ : genv}.
  Variable cls : globname.

  #[global] Instance structR_fractional : CFractional (structR cls).
  Proof. rewrite structR.unlock; eapply as_Rep_cfractional => ?; eapply struct_padding_fractional. Qed.
  #[global] Instance structR_cfractional_eta : CFractional (fun q => structR cls q).
  Proof.  apply structR_fractional. Qed.

  #[global] Instance structR_timeless : Timeless2 structR.
  Proof. rewrite structR.unlock; apply _. Qed.
  #[global] Instance structR_frac_valid : CFracValid0 (structR cls).
  Proof. rewrite structR.unlock. constructor. intros; apply as_Rep_only_provable_observe. refine _. Qed.
  #[global] Instance structR_frac_valid_eta : CFracValid0 (fun q => structR cls q).
  Proof. apply structR_frac_valid. Qed.

  #[global] Instance structR_as_fractional : AsCFractional0 (structR cls).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance union_fractional : CFractional1 (unionR cls).
  Proof. rewrite unionR.unlock; intros; eapply as_Rep_cfractional => ?; eapply union_padding_fractional. Qed.
  #[global] Instance union_timeless : Timeless3 unionR.
  Proof. rewrite unionR.unlock; apply _. Qed.
  #[global] Instance union_frac_valid : CFracValid1 (unionR cls).
  Proof. rewrite unionR.unlock. constructor. intros; apply as_Rep_only_provable_observe. refine _. Qed.

  #[global] Instance union_as_fractional : AsCFractional1 (unionR cls).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance structR_type_ptr_observe : forall q cls, Observe (type_ptrR (Tnamed cls)) (structR cls q).
  Proof.
    intros; eapply observe_at; intros.
    rewrite _at_type_ptrR structR.unlock _at_as_Rep. refine _.
  Qed.
  #[global] Instance structR_strict_valid_observe q : Observe svalidR (structR cls q).
  Proof. rewrite -type_ptrR_svalidR; apply _. Qed.
  #[global] Instance structR_valid_observe q : Observe validR (structR cls q).
  Proof. rewrite -svalidR_validR; apply _. Qed.

  #[global] Instance structR_nonnull q : Observe nonnullR (structR cls q).
  Proof.
    iIntros "H".
    iDestruct (observe (type_ptrR _) with "H") as "#T".
    iApply (observe with "T").
  Qed.


  #[global] Instance unionR_type_ptr_observe : forall q i, Observe (type_ptrR (Tnamed cls)) (unionR cls q i).
  Proof.
    intros; eapply observe_at; intros.
    rewrite _at_type_ptrR unionR.unlock _at_as_Rep. refine _.
  Qed.
  #[global] Instance unionR_strict_valid_observe q i : Observe svalidR (unionR cls q i).
  Proof. rewrite -type_ptrR_svalidR; apply _. Qed.
  #[global] Instance unionR_valid_observe q i : Observe validR (unionR cls q i).
  Proof. rewrite -svalidR_validR; apply _. Qed.

  #[global] Instance unionR_nonnull q i : Observe nonnullR (unionR cls q i).
  Proof.
    iIntros "H".
    iDestruct (observe (type_ptrR _) with "H") as "#T".
    iApply (observe with "T").
  Qed.

  #[global] Instance unionR_agree q q' i i' :
      Observe2 [| i = i' |] (unionR cls q i) (unionR cls q' i').
  Proof. rewrite unionR.unlock. eapply observe_2_at.
         intros; rewrite _at_only_provable !_at_as_Rep. refine _.
  Qed.

End padding.

#[global] Typeclasses Opaque derivationR.
#[global] Typeclasses Opaque type_ptrR validR svalidR.

#[deprecated(note="since 2022-04-07; use `nullR` instead")]
Notation is_null := nullR (only parsing).
#[deprecated(note="since 2022-04-07; use `nullR_eq` instead")]
Notation is_null_eq := nullR_eq (only parsing).
#[deprecated(note="since 2022-04-07; use `nullR_def` instead")]
Notation is_null_def := nullR_def (only parsing).
