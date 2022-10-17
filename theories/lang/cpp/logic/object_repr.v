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
From bedrock.lang.cpp.logic Require Import arr pred heap_pred layout raw.

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

Section rawsR_transport.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma _at_rawsR_ptr_congP_transport (p1 p2 : ptr) (q : Qp) (rs : list raw_byte) :
        ptr_congP σ p1 p2 ** ([∗list] i ∈ seqN 0 (lengthN rs), type_ptr Tu8 (p2 .[ Tu8 ! Z.of_N i ]))
    |-- p1 |-> rawsR q rs -* p2 |-> rawsR q rs.
  Proof.
    generalize dependent p2; generalize dependent p1; induction rs;
      iIntros (p1 p2) "[#congP tptrs]"; iAssert (ptr_congP σ p1 p2) as "(% & #tptr1 & #tptr2)"=> //.
    - rewrite /rawsR !arrayR_nil !_at_sep !_at_only_provable !_at_validR.
      iIntros "[_ %]"; iFrame "%"; iApply (type_ptr_valid with "tptr2").
    - rewrite /rawsR !arrayR_cons !_at_sep !_at_type_ptrR !_at_offsetR; fold (rawsR q rs).
      iIntros "[_ [raw raws]]"; iFrame "#"; iSplitL "raw".
      + iApply (_at_rawR_ptr_congP_transport with "congP"); iFrame "∗".
      + destruct rs.
        * rewrite /rawsR !arrayR_nil !_at_sep !_at_only_provable !_at_validR.
          iDestruct "raws" as "[#valid %]"; iFrame "%".
          iApply type_ptr_valid_plus_one; iFrame "#".
        * specialize (IHrs (p1 .[ Tu8 ! 1 ]) (p2 .[ Tu8 ! 1 ])).

          iDestruct (observe (type_ptr Tu8 (p1 .[ Tu8 ! 1 ])) with "raws") as "#tptr1'". 1: {
            rewrite /rawsR arrayR_cons; apply: _.
          }

          iDestruct (observe (type_ptr Tu8 (p2 .[ Tu8 ! 1 ])) with "tptrs") as "#tptr2'". 1: {
            rewrite !lengthN_cons !N.add_1_r !seqN_S_start/=; apply: _.
          }

          rewrite lengthN_cons N.add_1_r seqN_S_start/=.
          rewrite big_sepL_type_ptr_shift; auto.
          replace (Z.of_N 1) with 1%Z by lia.
          iDestruct "tptrs" as "#[tptr' tptrs]".

          iApply (IHrs with "[tptrs]"); iFrame "#∗".
          unfold ptr_congP, ptr_cong; iPureIntro.
          destruct H as [p [o1 [o2 [Ho1 [Ho2 Hoffset_cong]]]]]; subst.
          exists p, (o1 .[ Tu8 ! 1 ]), (o2 .[ Tu8 ! 1 ]).
          rewrite ?offset_ptr_dot; intuition.
          unfold offset_cong in *.
          apply option.same_property_iff in Hoffset_cong as [? [Ho1 Ho2]].
          apply option.same_property_iff.
          rewrite !eval_offset_dot !eval_o_sub Ho1 Ho2 /=.
          by eauto.
  Qed.
End rawsR_transport.

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
    Lemma raw_type_ptrs_arrayR_Tu8_emp `(xs : list X) :
      forall (ty : type) (p : ptr) (sz : N),
        size_of σ ty = Some sz ->
        lengthN xs = sz ->
        xs <> nil ->
            raw_type_ptrs ty p
        -|- p |-> arrayR Tu8 (const emp) xs.
    Proof.
      intros * Hsz Hlen Hnonnil.
      rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
      rewrite arrayR_eq/arrayR_def arrR_eq/arrR_def.
      split'.
      - iIntros "P"; iDestruct "P" as (sz') "[%Hsz' #tptrs]".
        rewrite !_at_sep !_at_offsetR !_at_only_provable.
        assert (is_Some (size_of σ Tu8)) by eauto; iFrame "%".
        rewrite fmap_length -to_nat_lengthN Hlen N_nat_Z.
        rewrite Hsz' in Hsz; inversion Hsz; subst.
        iSplit.
        + rewrite (big_sepL_lookup _ _ (Nat.pred (length xs))). 2: {
            rewrite list_lookup_lookupN.
            eapply lookupN_seqN.
            intuition eauto.
            destruct xs; simpl; [by exfalso; apply Hnonnil |].
            rewrite /lengthN/=; lia.
          }
          rewrite N.add_0_l Nat2N.inj_pred; fold (lengthN xs).
          replace (Z.of_N (lengthN xs))
            with (N.pred (lengthN xs) + 1)%Z
            by (destruct xs; by [contradiction | rewrite /lengthN/=; lia]).
          rewrite -o_sub_sub _at_validR.
          by iApply type_ptr_valid_plus_one.
        + rewrite _at_big_sepL.
          iApply (big_sepL_mono (fun n _ => type_ptr Tu8 (p .[ Tu8 ! n ]))).
          2: {
            iStopProof; generalize dependent p; clear -Hnonnil;
              destruct xs as [| x xs]; first by contradiction.
            generalize dependent x; induction xs as [| x' xs IHxs];
              iIntros (x Hnonnil p) "#tptrs"; first done.
            specialize (IHxs x' ltac:(auto) (p .[ Tu8 ! 1 ])).
            rewrite fmap_cons big_sepL_cons.
            replace (lengthN (x :: x' :: xs))
              with (N.succ (lengthN (x' :: xs)))
              by (rewrite !lengthN_cons; lia).
            rewrite seqN_S_start big_sepL_cons.
            iDestruct "tptrs" as "[$ tptrs]".
            iApply (big_sepL_mono (fun n _ => type_ptr Tu8 (p .[ Tu8 ! 1 ] .[Tu8 ! n ])));
              first by (intros **; rewrite o_sub_sub;
                          by replace (Z.of_nat (S k)) with (1 + k)%Z by lia).
            iApply IHxs; iModIntro.
            by iApply (big_sepL_type_ptr_shift 1%N).
          }
          intros k y Hy.
          rewrite list_lookup_fmap in Hy.
          destruct (xs !! k); last by done.
          inversion Hy; subst.
          rewrite _at_offsetR _at_sep _at_emp _at_type_ptrR.
          iIntros "$".
      - rewrite !_at_sep !_at_offsetR _at_only_provable _at_validR _at_big_sepL.
        iIntros "(_ & _ & tptrs)".
        iExists sz; iFrame "%"; rewrite -Hlen; clear -Hnonnil.
        iDestruct (big_sepL_mono _ (fun n y => type_ptr Tu8 (p .[ Tu8 ! n ])) with "tptrs") as "tptrs".
        2: {
          iStopProof; generalize dependent p;
             destruct xs as [| x xs]; first by contradiction.
          generalize dependent x; induction xs as [| x' xs IHxs];
            iIntros (x Hnonnil p) "tptrs"; first by done.
          specialize (IHxs x' ltac:(auto) (p .[ Tu8 ! 1 ])).
          rewrite fmap_cons big_sepL_cons.
          replace (lengthN (x :: x' :: xs))
            with (N.succ (lengthN (x' :: xs)))
            by (rewrite !lengthN_cons; lia).
          rewrite seqN_S_start big_sepL_cons.
          iDestruct "tptrs" as "[$ tptrs]".
          iDestruct (big_sepL_mono _ (fun n _ => type_ptr Tu8 (p .[ Tu8 ! 1 ] .[Tu8 ! n ]))
                      with "tptrs") as "tptrs";
            first by (intros **; rewrite o_sub_sub;
                        by replace (Z.of_nat (S k)) with (1 + k)%Z by lia).
          iDestruct (IHxs with "tptrs") as "tptrs".
          by iApply (big_sepL_type_ptr_shift 1%N).
        }
        intros k y Hy.
        rewrite list_lookup_fmap in Hy.
        destruct (xs !! k); last by done.
        inversion Hy; subst.
        rewrite _at_offsetR _at_sep _at_emp _at_type_ptrR.
        iIntros "[$ _]".
    Qed.

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

    Lemma raw_type_ptrs_big_array :
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

Section primR_transport.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma _at_primR_ptr_congP_transport p p' ty q v :
    ptr_congP σ p p' ** type_ptr ty p' |-- p |-> primR ty q v -* p' |-> primR ty q v.
  Proof.
    iIntros "#[cong tptr'] prim".
    iDestruct (type_ptr_size with "tptr'") as "%Hsz"; destruct Hsz as [sz Hsz].
    iDestruct (type_ptr_raw_type_ptrs with "tptr'") as "raw_tptrs"; eauto.
    rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
    iDestruct "raw_tptrs" as (sz') "[%Hsz' tptrs]".
    rewrite Hsz' in Hsz; inversion Hsz; subst.
    rewrite primR_to_rawsR !_at_exists.
    iDestruct "prim" as (rs) "H"; iExists rs.
    rewrite !_at_sep !_at_only_provable !_at_type_ptrR.
    iDestruct "H" as "(raws & %raw_bytes & _)"; iFrame "#%".
    pose proof (raw_bytes_of_val_sizeof raw_bytes) as Hlen.
    rewrite Hlen in Hsz'; inversion Hsz'; subst.
    rewrite lengthN_fold.
    iRevert "raws".
    iApply _at_rawsR_ptr_congP_transport.
    by iFrame "#".
  Qed.
End primR_transport.

(* [Rep]s which can be encoded as [raw] bytes enjoy certain transport and cancellation properties *)
Section with_rawable.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context {X : Type} (R : Qp -> X -> Rep).
  Context (decode : list raw_byte -> X -> Prop) (encode : X -> list raw_byte -> Prop).
  Context (enc_dec_uniq : forall (x x' : X) (raws : list raw_byte),
              encode x raws -> decode raws x' -> x = x').
  (* NOTE (JH): structs with padding are rawable, but this direction is too strict to permit
     the nondeterminism inherent in the representation of padding.
   *)
  (* Context (dec_enc_uniq : forall (x x' : X) (raws : list raw_byte), *)
  (*             decode raws x -> encode x raws' -> ). *)
  Context (ty : type) (sz : N) (Hsz : size_of σ ty = Some sz) (Hnonzero : (sz <> 0)%N).
  Context (Hdecode_sz : forall (x : X) (rs : list raw_byte), decode rs x -> lengthN rs = sz).
  Context (Hencode_sz : forall (x : X) (rs : list raw_byte), encode x rs -> lengthN rs = sz).
  Context (HR_decode : forall (rs : list raw_byte) (p : ptr) (q : Qp),
                             p |-> rawsR q rs ** type_ptr ty p
                         |-- Exists (x : X),
                                [| decode rs x |] ** p |-> R q x).
  Context (HR_encode : forall (x : X) (p : ptr) (q : Qp),
                             p |-> R q x
                         |-- type_ptr ty p **
                             Exists (rs : list raw_byte),
                               [| encode x rs |] ** p |-> rawsR q rs).

  #[local] Lemma _at_rawable_R_obj_repr_aux (i : N) :
    forall (p : ptr) (q : Qp) (rs : list raw_byte),
          p .[ Tu8 ! i ] |-> rawsR q (dropN i rs)
      |-- p .[ Tu8 ! i ] |-> arrayR Tu8 (fun tt => anyR Tu8 q)
                                        (replicateN (lengthN rs - i) ()).
  Proof.
    intros **; clear Hsz Hdecode_sz Hencode_sz Hnonzero HR_decode HR_encode.
    generalize dependent i; generalize dependent p.
    induction rs as [| r rs IHrs]; intros p i.
    - rewrite replicateN_0 dropN_nil /rawsR !arrayR_nil.
      done.
    - destruct i as [| i' _] using N.peano_ind=>//.
      + rewrite -> o_sub_0 in *; auto.
        specialize (IHrs (p .[ Tu8 ! 1 ]) 0%N).
        rewrite -> offset_ptr_id in *.
        rewrite -> N.sub_0_r in *.
        rewrite lengthN_cons replicateN_succ /rawsR !arrayR_cons
                !_at_sep !_at_offsetR.
        iIntros "(#tptr & raw & raws)".
        iFrame "#"; iSplitL "raw".
        * rewrite rawR_eq/rawR_def _at_as_Rep.
          by iApply tptsto_raw_anyR.
        * rewrite o_sub_0 in IHrs; auto; rewrite offset_ptr_id in IHrs.
          iApply IHrs.
          rewrite dropN_zero /rawsR _at_type_ptrR; iFrame "#∗".
      + replace (dropN (N.succ i') (r :: rs))
          with (dropN i' rs)
          by (rewrite -N.add_1_r dropN_cons_succ//).
        rewrite lengthN_cons.
        replace (lengthN rs + 1 - N.succ i')%N
          with (lengthN rs - i')%N
          by lia.
        specialize (IHrs (p .[ Tu8 ! 1 ]) i').
        rewrite o_sub_sub in IHrs.
        replace (1 + Z.of_N i')%Z with (Z.of_N (N.succ i')) in IHrs by lia.
        by iApply IHrs.
  Qed.

  Lemma _at_rawable_R_arrayR_anyR :
    forall (p : ptr) (q : Qp) (x : X),
          p |-> R q x
      |-- p |-> arrayR Tu8 (fun tt => anyR Tu8 q) (replicateN sz ()).
  Proof using encode ty Hsz Hencode_sz Hnonzero HR_encode.
    intros **.
    rewrite HR_encode.
    iIntros "[#tptr H]"; iDestruct "H" as (rs) "[%Hrs raws]".
    pose proof (_at_rawable_R_obj_repr_aux 0 p q rs) as Haux.
    rewrite o_sub_0 in Haux; auto; rewrite offset_ptr_id in Haux.
    rewrite dropN_zero N.sub_0_r (Hencode_sz x) in Haux; last by assumption.
    by iApply Haux.
  Qed.

  Lemma _at_rawable_R_anyR :
    forall (p : ptr) (q : Qp) (x : X),
          p |-> R q x
      |-- p |-> anyR (Tarray Tu8 sz) q.
  Proof using encode ty Hsz Hencode_sz Hnonzero HR_encode.
    intros **; rewrite anyR_array repeatN_replicateN.
    by apply _at_rawable_R_arrayR_anyR.
  Qed.

  Lemma R_ptr_congP_transport_via_rawsR :
    forall (p p' : ptr) (q : Qp) (x : X),
      ptr_congP σ p p' ** type_ptr ty p' |-- p |-> R q x -* p' |-> R q x.
  Proof using decode encode enc_dec_uniq sz Hdecode_sz Hencode_sz Hsz HR_decode HR_encode Hnonzero.
    intros p p' q x; rewrite HR_encode.
    iIntros "#[cong tptr'] [#tptr H]"; iDestruct "H" as (rs) "[%Henc raws]".
    iDestruct (type_ptr_raw_type_ptrs with "tptr'") as "#raw_tptrs'"; auto.
    assert (rs <> []) as Hrs_nonnil
        by (intro CONTRA; subst; specialize (Hencode_sz x [] Henc);
            apply Hnonzero; rewrite -Hencode_sz; by apply lengthN_nil).
    rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
    iDestruct "raw_tptrs'" as (sz') "[%Hsz' tptrs']".
    rewrite Hsz in Hsz'; inversion Hsz'; subst.
    assert (sz' = lengthN rs) as -> by (by erewrite <- Hencode_sz).
    iDestruct (_at_rawsR_ptr_congP_transport with "[$] [$]") as "raws'".
    iCombine "raws' tptr'" as "H".
    iDestruct (HR_decode with "H") as "H".
    iDestruct "H" as (x') "[%Hdec R]".
    by rewrite (enc_dec_uniq x x' rs).
  Qed.
End with_rawable.