(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** [object_repr.v] contains bundled definitions and utilities which are useful
    when operating on (or reasoning about) the "object representation" of a C++
    object (cf. <https://eel.is/c++draft/basic.types.general#4>). In BRiCk,
    [rawR]/[rawsR] - which are wrappers around [Vraw] [val]ues and lists of them,
    respectively - are used to refer to and manipulate these "object representations".
 *)
Require Import iris.proofmode.proofmode.
Require Import bedrock.prelude.base.

Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import arr pred heap_pred raw.

Require Import bedrock.lang.cpp.heap_notations.

Section Utilities.
  Context `{Σ : cpp_logic} {σ : genv}.

  #[local]
  Lemma big_sepL_type_ptr_shift_aux (p : ptr) (ty : type) (j n m : N) :
    is_Some (size_of σ ty) ->
    (j <= n)%N ->
        ([∗list] i ∈ seqN n m, type_ptr ty (p .[ ty ! Z.of_N i ]))
    -|- ([∗list] i ∈ seqN j m, type_ptr ty (p .[ ty ! Z.of_N (n - j) ] .[ty ! Z.of_N i ] )).
  Proof.
    generalize dependent j; generalize dependent n; generalize dependent p;
      induction m as [| m' IHm'] using N.peano_ind=> p n j Hsz Hj.
    - by rewrite !seqN_0 !big_sepL_nil.
    - rewrite !seqN_S_start !big_sepL_cons o_sub_sub.
      replace (Z.add (Z.of_N (n - j)) (Z.of_N j)) with (Z.of_N n) by lia.
      split'; iIntros "[$ tptrs]".
      + rewrite (IHm' _ _ (N.succ j)); [| by auto | by lia].
        by rewrite N.sub_succ.
      + iApply (IHm' _ _ (N.succ j)); [by auto | by lia |].
        by rewrite N.sub_succ.
  Qed.

  Lemma big_sepL_type_ptr_shift (n m : N) :
    forall (p : ptr) (ty : type),
      is_Some (size_of σ ty) ->
          ([∗list] i ∈ seqN n m, type_ptr ty (p .[ ty ! Z.of_N i ]))
      -|- ([∗list] i ∈ seqN 0 m, type_ptr ty (p .[ ty ! Z.of_N n ] .[ty ! Z.of_N i ] )).
  Proof.
    intros p ty Hsz.
    pose proof (big_sepL_type_ptr_shift_aux p ty 0 n m Hsz ltac:(lia)) as ->.
    split'; iApply big_sepL_mono; intros **=> /=; by rewrite N.sub_0_r.
  Qed.
End Utilities.

(* Definitions to ease consuming and reasoning about the collection of [type_ptr Tu8]
   facts induced by [type_ptr_obj_repr].
 *)
Section raw_type_ptrs.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* [obj_type_ptr ty p] collects all of the constituent [type_ptr Tu8] facts
     for the "object representation" of an object of type [ty] rooted at [p].
   *)
  Definition raw_type_ptrs_def (ty : type) (p : ptr) : mpred :=
    Exists (sz : N),
      [| size_of σ ty = Some sz |] **
      [∗list] i ∈ seqN 0 sz, type_ptr Tu8 (p .[ Tu8 ! Z.of_N i ]).
  Definition raw_type_ptrs_aux : seal (@raw_type_ptrs_def). Proof. by eexists. Qed.
  Definition raw_type_ptrs := raw_type_ptrs_aux.(unseal).
  Definition raw_type_ptrs_eq : @raw_type_ptrs = _ := raw_type_ptrs_aux.(seal_eq).

  (* [obj_type_ptr ty p] collects all of the constituent [type_ptr Tu8] facts
     for the "object representation" of an object of type [ty] rooted at [p].
   *)
  Definition raw_type_ptrsR_def (ty : type) : Rep := as_Rep (raw_type_ptrs_def ty).
  Definition raw_type_ptrsR_aux : seal (@raw_type_ptrsR_def). Proof. by eexists. Qed.
  Definition raw_type_ptrsR := raw_type_ptrsR_aux.(unseal).
  Definition raw_type_ptrsR_eq : @raw_type_ptrsR = _ := raw_type_ptrsR_aux.(seal_eq).

  Lemma type_ptr_raw_type_ptrs :
    forall (ty : type) (p : ptr),
      is_Some (size_of σ ty) ->
      type_ptr ty p |-- raw_type_ptrs ty p.
  Proof.
    intros * Hsz; rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
    destruct Hsz as [sz Hsz].
    iIntros "#tptr"; iExists sz; iFrame "%".
    by iApply type_ptr_obj_repr.
  Qed.

  Section Instances.
    #[global]
    Instance raw_type_ptrs_persistent : forall p ty,
      Persistent (raw_type_ptrs ty p).
    Proof. rewrite raw_type_ptrs_eq/raw_type_ptrs_def; apply: _. Qed.
    #[global]
    Instance raw_type_ptrsR_persistent : forall ty,
      Persistent (raw_type_ptrsR ty).
    Proof. rewrite raw_type_ptrsR_eq/raw_type_ptrsR_def; apply: _. Qed.

    #[global]
    Instance raw_type_ptrs_affine : forall p ty,
      Affine (raw_type_ptrs ty p).
    Proof. rewrite raw_type_ptrs_eq/raw_type_ptrs_def; apply: _. Qed.
    #[global]
    Instance raw_type_ptrsR_affine : forall ty,
      Affine (raw_type_ptrsR ty).
    Proof. rewrite raw_type_ptrsR_eq/raw_type_ptrsR_def; apply: _. Qed.

    #[global]
    Instance raw_type_ptrs_timeless : forall p ty,
      Timeless (raw_type_ptrs ty p).
    Proof. rewrite raw_type_ptrs_eq/raw_type_ptrs_def; apply: _. Qed.
    #[global]
    Instance raw_type_ptrsR_timeless : forall ty,
      Timeless (raw_type_ptrsR ty).
    Proof. rewrite raw_type_ptrsR_eq/raw_type_ptrsR_def; apply: _. Qed.

    Section observations.
      #[global]
      Lemma raw_type_ptrs_type_ptr_Tu8_obs (ty : type) (i : N) :
        forall (p : ptr) (sz : N),
          size_of σ ty = Some sz ->
          (i < sz)%N ->
          Observe (type_ptr Tu8 (p .[ Tu8 ! i ])) (raw_type_ptrs ty p).
      Proof.
        iIntros (p sz Hsz Hi) "#raw_tptrs !>".
        rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
        iDestruct "raw_tptrs" as (sz') "[%Hsz' tptrs]".
        rewrite {}Hsz' in Hsz; inversion Hsz; subst.
        iStopProof.
        induction sz as [| sz' IHsz'] using N.peano_ind; first lia.
        iIntros "#tptrs".
        assert (i = sz' \/ i < sz')%N as [Hi' | Hi'] by lia;
          rewrite seqN_S_end_app big_opL_app; cbn;
          iDestruct "tptrs" as "(#tptrs & #tptr & _)";
          by [subst | iApply IHsz'].
      Qed.
    End observations.
  End Instances.

  Section equivalences.
    #[local]
    Lemma raw_type_ptrs_array_aux :
      forall (ty : type) (cnt : N) (p : ptr) (i sz : N),
        size_of σ ty = Some sz ->
            ([∗list] j ∈ seqN (i * sz) (cnt * sz)%N,
               type_ptr Tu8 (p .[ Tu8 ! Z.of_N (i * sz) ] .[ Tu8 ! Z.of_N j ]))
        -|- ([∗list] j ∈ seqN i cnt,
               raw_type_ptrs ty (p .[ Tu8 ! Z.of_N ((i + j) * sz) ])).
    Proof.
      intros ty cnt; induction cnt as [| cnt' IHcnt'] using N.peano_ind=> p i sz Hsz;
        first by rewrite N.mul_0_l !seqN_0.
      rewrite Nmult_Sn_m {1}/seqN N2Nat.inj_add seq_app -N2Nat.inj_add fmap_app.
      fold (seqN (i * sz) sz) (seqN (i * sz + sz)%N (cnt' * sz)).
      replace (i * sz + sz)%N with ((i + 1) * sz)%N by lia;
        rewrite big_sepL_app.
      rewrite seqN_S_start big_sepL_cons -N.add_1_r.
      specialize (IHcnt' (p .[ Tu8 ! -sz ]) (i + 1)%N sz Hsz).
      rewrite !o_sub_sub in IHcnt'.
      split'; iIntros "[P Q]"; iSplitL "P".
      - rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
        iExists sz; iFrame "%".
        iDestruct (big_sepL_type_ptr_shift with "P") as "?"; auto.
        rewrite o_sub_sub.
        by replace (Z.add (Z.of_N (i * sz)) (Z.of_N (i * sz)))
          with (Z.of_N ((i + i) * sz))
          by lia.
      - iApply big_sepL_mono; last iApply IHcnt'.
        + intros **; simpl.
          rewrite o_sub_sub.
          by replace (Z.add (-sz) (Z.of_N ((i + 1 + y) * sz)))
            with (Z.of_N ((i + y) * sz))
            by lia.
        + iApply big_sepL_mono; last by iFrame.
          intros **; simpl.
          by replace (Z.add (-sz) (Z.of_N ((i + 1) * sz)))
            with (Z.of_N (i * sz))
            by lia.
      - rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
        iDestruct "P" as (sz') "[%Hsz' tptrs]".
        rewrite Hsz' in Hsz; inversion Hsz; subst.
        iApply big_sepL_type_ptr_shift; auto.
        rewrite o_sub_sub.
        by replace (Z.add (Z.of_N (i * sz)) (Z.of_N (i * sz)))
          with (Z.of_N ((i + i) * sz))
          by lia.
      - iApply big_sepL_mono; last iApply IHcnt'.
        + intros **; simpl.
          by replace (Z.add (-sz) (Z.of_N ((i + 1) * sz)))
            with (Z.of_N (i * sz))
            by lia.
        + iApply big_sepL_mono; last by iFrame.
          intros **; simpl.
          rewrite o_sub_sub.
          by replace (Z.add (-sz) (Z.of_N ((i + 1 + y) * sz)))
            with (Z.of_N ((i + y) * sz))
            by lia.
    Qed.

    Lemma raw_type_ptrs_array :
      forall (p : ptr) (ty : type) (cnt sz : N),
        size_of σ ty = Some sz ->
            raw_type_ptrs (Tarray ty cnt) p
        -|- [∗list] i ∈ seqN 0 cnt, raw_type_ptrs ty (p .[ Tu8 ! Z.of_N (i * sz) ]).
    Proof.
      intros p ty cnt sz Hsz.
      pose proof (raw_type_ptrs_array_aux ty cnt p 0 sz Hsz) as Haux.
      split'; iIntros "P";
        rewrite o_sub_0 in Haux; auto; rewrite offset_ptr_id in Haux;
        rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
      - iDestruct "P" as (array_sz) "[%Harray_sz tptrs]".
        apply size_of_array_shatter in Harray_sz as [sz' [? [Hsz' Harray_sz]]]; subst.
        rewrite Hsz' in Hsz; inversion Hsz; subst.
        rewrite N.mul_0_l in Haux; rewrite Haux.
        iApply big_sepL_mono; last by iFrame.
        intros k y Hk=> /=.
        by rewrite raw_type_ptrs_eq/raw_type_ptrs_def N.add_0_l.
      - pose proof (size_of_array ty cnt sz Hsz).
        iExists (cnt * sz)%N; iFrame "%".
        iApply Haux.
        iApply big_sepL_mono; last by iFrame.
        intros k y Hk=> /=.
        by rewrite raw_type_ptrs_eq/raw_type_ptrs_def N.add_0_l.
    Qed.
  End equivalences.
End raw_type_ptrs.
#[global] Arguments raw_type_ptrs {_ Σ σ} _ _.
#[global] Arguments raw_type_ptrsR {_ Σ σ} _.
#[global] Hint Opaque raw_type_ptrs raw_type_ptrsR : typeclass_instances.
