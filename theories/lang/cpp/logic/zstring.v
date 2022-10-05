(*
 * Copyright (C) BedRock Systems Inc. 2019-2021

 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From Coq Require Import ZArith.BinInt Lists.List.

From iris.proofmode Require Import proofmode.

Require Import bedrock.prelude.stdpp_ssreflect.

Require Import bedrock.prelude.base.
From bedrock.lang.bi Require Import
     prelude observe.
From bedrock.lang.cpp Require Import
     semantics.values
     logic.arr logic.heap_pred logic.mpred
     heap_notations.

Import ChargeNotation.
#[local] Open Scope Z_scope.

(** * [zstring]s

    [zstring]s reflect the "character array" which backs null-terminated strings
    in C++. These arrays include the null-terminator
 *)
Module zstring.
  Definition t := list Z.
  Bind Scope list_scope with t.

  (* [size] reflects the in-memory footprint of the null-terminated string (i.e. the
     length is one greater than that of the string as given by `std::strlen`).
   *)
  Definition _size (zs : t) : Z :=
    Z.of_nat (List.length zs).
  #[global] Arguments _size zs : simpl never.
  Notation size zs := (_size zs%Z).

  (* [strlen] mirrors the behavior of the standard-library function of the same name
     (i.e. the length DOES NOT include the null-terminator).
   *)
  Definition _strlen (zs : t) : Z :=
    (size zs - 1)%Z.
  #[global] Arguments _strlen zs : simpl never.
  Notation strlen zs := (_strlen zs%Z).

  Definition _WF {σ : genv} (zs : t) : Prop :=
    exists zs', zs = zs' ++ [0] /\ not (In 0 zs') /\
    List.Forall (λ c : Z, has_type c Tuchar) zs.
  #[global] Arguments _WF {σ} zs : simpl never.
  Notation WF zs := (_WF zs%Z).

  (* this definition is less intensional, and seems to work more
     smoothly wrt. automation: *)
  Definition _WF' {σ : genv} (zs : t) : Prop :=
    (exists v, nth_error zs 0 = Some v) /\
    (forall i, Z.of_nat i <= strlen zs ->
          exists z, nth_error zs i = Some z /\ has_type (Vint z) Tuchar) /\
    (forall i, Z.of_nat i < strlen zs ->
          exists z, nth_error zs i = Some z /\ z <> 0) /\
    forall i, Z.of_nat i = strlen zs -> nth_error zs i = Some 0.
  #[global] Arguments _WF' {σ} zs : simpl never.
  Notation WF' zs := (_WF' zs%Z).

  Section WF_Theory.
    Context {σ : genv}.
    Remark not_WF_nil : not (WF []).
    Proof.
      rewrite /_WF; intro CONTRA;
        destruct CONTRA as [? [CONTRA ?]];
        eapply app_cons_not_nil; eauto.
    Qed.

    Remark WF_singleton : WF [0].
    Proof.
      rewrite /_WF; exists []; repeat split.
      - intro CONTRA; by inversion CONTRA.
      - repeat constructor; apply has_int_type; rewrite /bound/=; by lia.
    Qed.

    Lemma WF_singleton_inj :
      forall (z : Z),
        WF [z] ->
        z = 0.
    Proof.
      intros * [zs [Hzs [Hin Hbounds]]].
      destruct zs; simpl in *; inversion Hzs.
      - reflexivity.
      - exfalso; eapply app_cons_not_nil; by eauto.
    Qed.

    Lemma WF_nonempty_inj :
      forall (zs : t),
        WF zs ->
        exists z zs', zs = z :: zs'.
    Proof.
      move=> zs Hzstring; induction zs; [ | by eauto].
      unfold WF in Hzstring.
      destruct Hzstring as [? [CONTRA ?]].
      now apply app_cons_not_nil in CONTRA.
    Qed.

    Lemma WF_cons :
      forall (z : Z) (zs : t),
        (z <> 0)%Z ->
        has_type (Vint z) Tuchar ->
        WF (z :: zs) <->
        WF zs.
    Proof.
      intros * Hnonzero Hz; split; [intro WF_zs | intro WF_z]; unfold WF in *.
      - destruct WF_zs as [zs' [Hzs' [Hin Hbounds]]].
        exists (tail zs'); split; destruct zs'=> //=;
          [rewrite app_nil_l in Hzs' | | |];
          inversion Hzs'=> //.
        split.
        + intro; apply Hin=> //=; auto.
        + inversion Hbounds; by subst.
      - destruct WF_z as [zs' [Hzs' [Hin Hbounds]]];
          exists (z :: zs'); split.
        + by subst.
        + split.
          * intro CONTRA; apply Hin; by inversion CONTRA.
          * by constructor.
    Qed.
  End WF_Theory.

  Section size_Theory.
    Context {σ : genv}.

    (* Use [rewrite size_unfold/=] to reduce away a [size] application to a
       concrete string; if complete reduction is not possible, this is
       equivalent to unfolding the [size] notation.
     *)
    Lemma size_unfold (zs : t) :
      size zs = Unfold _size (size zs).
    Proof. by unfold size. Qed.

    Lemma size_strlen (zs : t) :
      size zs = strlen zs + 1.
    Proof. unfold strlen; by rewrite Z.sub_simpl_r. Qed.

    Remark size_nil : size [] = 0.
    Proof. by rewrite size_unfold. Qed.

    Lemma size_cons :
      forall (z : Z) (zs : t),
        size (z :: zs) = 1 + size zs.
    Proof. intros *; rewrite !size_unfold/=; by lia. Qed.

    Lemma size_cons':
      forall (z : Z) (zs : t),
        (z <> 0)%Z ->
        WF (z :: zs) ->
        Z.to_nat (size (z :: zs)) = S (Z.to_nat (size zs)).
    Proof.
      move=> z zs Hz Hzstring; inversion Hzstring as [zs' [Hzs' HIn]];
        unfold strlen, size; simpl.
      replace ((length zs + 1)%nat - 1)%Z
        with (Z.of_nat (length zs))
        by lia.
      destruct zs=> //=.
      lia.
    Qed.

    Lemma size_app :

      forall (zs zs' : t),
        size (zs ++ zs') = size zs + size zs'.
    Proof.
      intros *; induction zs as [| z zs'' IHzs'']; simpl in *.
      - by rewrite size_nil Z.add_0_l.
      - by rewrite !size_cons IHzs'' Z.add_assoc.
    Qed.

    Lemma size_nil_cons_contra :
      forall (z : Z) (zs : t),
        not (size (z :: zs) = size []).
    Proof. intros *; intro CONTRA; unfold size in CONTRA; by inversion CONTRA. Qed.

    Lemma size_nonneg : forall (zs : t), (0 <= size zs).
    Proof. intros *; destruct zs; unfold size; simpl; by lia. Qed.

    Lemma size_neg_inj : forall (zs : t), (0 = size zs)%Z -> zs = [].
    Proof. move=> [ | a s] Hlen=> //. Qed.
  End size_Theory.

  Section strlen_Theory.
    Context {σ : genv}.

    (* Use [rewrite strlen_unfold/=] to reduce away a [strlen] application to a
       concrete string; if complete reduction is not possible, this is
       equivalent to unfolding the [strlen] notation.
     *)
    Lemma strlen_unfold (zs : t) :
      strlen zs = Unfold _size (Unfold _strlen (strlen zs)).
    Proof. by unfold strlen. Qed.

    Lemma strlen_size (zs : t) :
      strlen zs = size zs - 1.
    Proof. by unfold strlen. Qed.

    Remark strlen_nil : strlen [] = -1.
    Proof. by rewrite strlen_unfold. Qed.

    Lemma strlen_cons (zs : t) :
      forall (z : Z),
        strlen (z :: zs) = 1 + strlen zs.
    Proof. intros *; rewrite !strlen_unfold/=; by lia. Qed.

    Lemma strlen_cons':
      forall (z : Z) (zs : t),
        (z <> 0)%Z ->
        WF (z :: zs) ->
        Z.to_nat (strlen (z :: zs)) = S (Z.to_nat (strlen zs)).
    Proof.
      move=> z zs Hz Hzstring; inversion Hzstring as [zs' [Hzs' HIn]];
        unfold strlen, size; simpl.
      replace ((length zs + 1)%nat - 1)%Z
        with (Z.of_nat (length zs))
        by lia.
      destruct zs=> //=.
      - apply WF_singleton_inj in Hzstring; subst; lia.
      - lia.
    Qed.

    Lemma strlen_app :
      forall (zs zs' : t),
        strlen (zs ++ zs') = size zs + strlen zs'.
    Proof.
      intros *; induction zs as [| z zs'' IHzs'']; simpl in *.
      - rewrite !size_unfold !strlen_unfold/=; by lia.
      - by rewrite !strlen_cons !size_cons IHzs'' Z.add_assoc.
    Qed.

    Lemma strlen_nil_cons_contra :
      forall (z : Z) (zs : t),
        not (strlen (z :: zs) = strlen []).
    Proof.
      intros *.
      unfold strlen.
      pose proof (size_nil_cons_contra z zs).
      by lia.
    Qed.

    Lemma strlen_lowerbound : forall (zs : t), (-1 <= strlen zs)%Z.
    Proof.
      intros *; destruct zs;
        unfold strlen, size;
        simpl; by lia.
    Qed.

    Lemma strlen_nonneg : forall (zs : t),
        WF zs ->
        (0 <= strlen zs).
    Proof.
      intros * Hzstring.
      inversion Hzstring as [zs' [Hzs' HIn]].
      rewrite Hzs' strlen_app.
      pose proof (strlen_lowerbound zs').
      pose proof (size_nonneg zs').
      unfold strlen; unfold size at 2.
      simpl; by lia.
    Qed.

    Lemma strlen_neg_inj : forall (zs : t), (-1 = strlen zs)%Z -> zs = [].
    Proof.
      move=> [ | a s] Hlen=> //; exfalso.
      pose proof (strlen_nil_cons_contra a s) as H.
      apply H; by rewrite strlen_nil.
    Qed.
  End strlen_Theory.

  Section WFs_equiv_Theory.
    Context {σ : genv}.
    Section helpers.
      Lemma len0_take (zs : t)
            (H0 : 0 < List.length zs)
            (H : forall i : nat, Z.of_nat i = strlen zs -> nth_error zs i = Some 0%Z) :
        zs = take (List.length zs - 1) zs ++ [0%Z].
      Proof.
        rewrite -[zs](firstn_skipn (List.length zs - 1)). f_equal.
        { rewrite app_length take_length drop_length.
          set x := List.length zs.
          have ->: ((x - 1) `min` x + (x - (x - 1)) - 1 = x - 1)%nat by lia.
            by rewrite firstn_skipn. }
        elim: zs H0 H; first by inversion 1.
        move => z zs IH /= H0 H. have ->: (List.length zs - 0 = List.length zs)%nat by lia.
        destruct zs; first by move: (H 0%nat eq_refl); inversion 1.
        destruct zs; first by move: (H 1%nat eq_refl); inversion 1.
        apply: IH; first by simpl; lia.
        case; unfold strlen, size; rewrite /List.length -/List.length; first by lia.
        move => n ?. simpl. move: (H (S (S n))). apply.
        rewrite Nat2Z.inj_succ; unfold strlen, size; rewrite /List.length -/List.length. lia.
      Qed.

      Lemma forall_not0 (zs : t)
            (H : ∀ i : nat, (i <= strlen zs)%Z →
                          ∃ z : Z, nth_error zs i = Some z ∧ has_type (Vint z) Tuchar)
            (H' : forall i : nat, (i < strlen zs)%Z ->
                          ∃ z : Z, nth_error zs i = Some z /\ z <> 0):
        List.Forall (fun z : Z => z <> 0 /\ has_type (Vint z) Tuchar) (take (List.length zs - 1) zs).
      Proof.
        induction zs; first by constructor.
        simpl. have ->: (List.length zs - 0 = List.length zs)%nat by lia. destruct zs.
        { simpl. constructor. }
        simpl. constructor.
        { move: (H 0%nat); case.
          { unfold strlen, size; rewrite /List.length -/List.length. lia. }
            move => x /= []; inversion 1; subst; intuition.
            specialize (H' 0%nat ltac:(rewrite !strlen_cons;
                                     pose proof (strlen_lowerbound zs);
                                     by lia)) as [? [? CONTRA]];
              simpl in *; inversion H1; congruence. }
        have <-: (List.length zs - 0 = List.length zs)%nat by lia. apply: IHzs.
        case.
        { move => h1; exists z. split => //.
          destruct zs. 1: {
            specialize (H 1%nat ltac:(rewrite strlen_unfold/=; lia))
              as [z' [Hnth Htype]].
            simpl in Hnth; inversion Hnth; by subst.
          }
          move: (H 1%nat); unfold strlen, size; case => //.
          { rewrite /List.length -/List.length. lia. }
            by move => x /=; case; inversion 1; subst. }
        move => n; unfold strlen, size; rewrite /List.length -/List.length => h.
        move: (H (S (S n))); case.
        { unfold strlen, size; rewrite /List.length -/List.length. lia. }
        move => x /=; case => h1 h2; exists x; split => //.
        intros i Hstrlen.
        rewrite [strlen (_ :: _ :: _)]strlen_cons in H'.
        specialize (H' (S i) ltac:(lia)) as [x [? ?]].
        exists x; by intuition.
      Qed.

      Lemma nth_error_strlen_contra :
        forall (n : nat) (zs : t),
          strlen zs < Z.of_nat n ->
          forall z, not (nth_error zs n = Some z).
      Proof.
        intros n; induction n; intros **.
        - destruct zs=> //.
          rewrite strlen_cons in H.
          pose proof (strlen_lowerbound zs).
          by lia.
        - destruct zs=> //.
          simpl; apply IHn.
          rewrite strlen_cons in H.
          pose proof (strlen_lowerbound zs).
          by lia.
      Qed.
    End helpers.

    Lemma WFs_equiv (zs : t) : WF' zs <-> WF zs.
    Proof.
      (* this is a horrible proof *)
      unfold WF, WF'; split.
      { case; case => x h1 []h2 []h3 h4.
        exists (take (List.length zs - 1) zs). repeat split.
        { apply: len0_take => //.
          clear - h1; case: zs h1 => //= a l _; lia. }
        2: {
          apply List.Forall_forall; intros z Hin.
          pose proof (In_nth_error zs z Hin) as [n Hnth].
          assert (n < strlen zs \/ Z.of_nat n = strlen zs \/ strlen zs < n)
            as [Hn | [Hn | Hn]] by lia.
          - specialize (h2 n ltac:(lia)) as [? ?]; intuition; congruence.
          - specialize (h4 n Hn).
            rewrite h4 in Hnth; inversion Hnth.
            apply has_char_type; rewrite /bound/=; by lia.
          - exfalso; eapply nth_error_strlen_contra; by eauto.
        }
        suff: List.Forall (fun x => x <> 0 /\ has_type (σ:=σ) (Vint x) Tuchar)
                          (take (Datatypes.length zs - 1) zs).
        { clear - zs. elim: zs => //= [_ [] //|a zs IH /=]. rewrite Nat.sub_0_r.
          destruct zs as [|z zs]; first done. move => /= /Forall_cons [[??]?].
          move => [//|]. simpl in IH. rewrite Nat.sub_0_r in IH. apply IH. done. }
        apply: forall_not0. apply h2. apply h3. }
      case => zs' []-> h1. split.
      { destruct zs'; simpl; first by exists 0.
                                          by exists z. }
      split.
      { move => i. unfold strlen, size; rewrite app_length Nat2Z.inj_add /= => h2.
        assert (i < List.length zs' \/ i = List.length zs')%nat
          as [h2' | h2'] by lia; clear h2. 2: {
          subst; exists 0; clear h1; split.
          - by induction zs'=> //=.
          - by apply has_char_type; rewrite /bound/=; lia.
        }
        rewrite nth_error_app1 => //.
        elim: zs' i h1 h2' => /=; first by lia.
        move => a lx IH i h1 h2. destruct i.
        { exists a; split => //.
          inversion h1 as [? Hforall].
          apply Forall_cons in Hforall.
          by intuition. }
        case: (IH i). 1: {
          split.
          - move => X; apply h1; by right.
          - destruct h1 as [? Hforall]; by apply List.Forall_inv_tail in Hforall. }
        1: by lia.
        move => x []h3 h4; exists x => /=; split => //. }

      split. 1: {
        move => i; unfold strlen, size.
        rewrite app_length/=; intros Hi.
        assert (i < length zs')%nat as Hzs' by lia; clear Hi.
        pose proof (nth_error_app1 zs' [0] Hzs') as Hnth.
        pose proof (nth_In zs' 0 Hzs') as Hin.
        rewrite Hnth; erewrite nth_error_nth' with (d:=0); eauto; eexists;
          split; eauto.
        intro CONTRA; rewrite CONTRA in Hin.
        inversion h1; by congruence.
      }
      move => i; unfold strlen, size.
      rewrite app_length Nat2Z.inj_add /= => h2.
      have ->: i = List.length zs' by lia. clear h2.
      rewrite nth_error_app2 //.
      have ->: (List.length zs' - List.length zs' = 0)%nat by lia. by [].
    Qed.

    Lemma WF'_singleton_inj :
      forall (z : Z),
        WF' [z] ->
        z = 0.
    Proof. intros *; rewrite WFs_equiv; by apply WF_singleton_inj. Qed.

    Remark not_WF'_nil : not (WF' []).
    Proof. rewrite WFs_equiv; by apply not_WF_nil. Qed.

    Lemma WF'_nonempty_inj :
      forall (zs : t),
        WF' zs ->
        exists z zs', zs = z :: zs'.
    Proof. intros *; rewrite WFs_equiv; by apply WF_nonempty_inj. Qed.

    Lemma WF'_cons :
      forall (z : Z) (zs : t),
        (z <> 0)%Z ->
        has_type (Vint z) Tuchar ->
        WF' (z :: zs) <->
        WF' zs.
    Proof. intros *; rewrite !WFs_equiv; by apply WF_cons. Qed.
  End WFs_equiv_Theory.

  Section with_Σ.
    Context `{Σ : cpp_logic} `{σ : genv}.

    (* The toplevel definition of [zstring.bufR]: *)

    Definition bufR (q : Qp) (sz : Z) (zs : t) : Rep :=
      [| size zs <= sz |] **
      arrayR Tuchar (fun c => primR Tuchar q (Vint c)) zs ** [| WF zs |] **
      .[Tuchar ! size zs]
         |-> arrayR Tuchar (fun _ => primR Tuchar q 0) (repeat () (Z.to_nat (sz - size zs))).
    (* The toplevel definition of [zstring.bufR']: *)
    Definition bufR' (q : Qp) (sz : Z) (zs : t) : Rep :=
      [| size zs <= sz |] **
      arrayR Tuchar (fun c => primR Tuchar q (Vint c)) zs ** [| WF' zs |] **
      .[Tuchar ! size zs]
         |-> arrayR Tuchar (fun _ => primR Tuchar q 0) (repeat () (Z.to_nat (sz - size zs))).

    #[global] Instance bufR_WF_observe :
      forall q (sz : Z) (zs : t),
        Observe [| WF zs |] (bufR q sz zs).
    Proof. refine _. Qed.

    #[global] Instance bufR'_WF_observe :
      forall q (sz : Z) (zs : t),
        Observe [| WF' zs |] (bufR' q sz zs).
    Proof. refine _. Qed.

    Lemma bufRs_equiv (q : Qp) (sz : Z) (zs : t) :
      bufR q sz zs -|- bufR' q sz zs.
    Proof. intros *; by rewrite /bufR/bufR' WFs_equiv. Qed.

    (* The toplevel definition of [zstring.R]: *)
    Definition R (q : Qp) (zs : t) : Rep :=
      arrayR Tuchar (fun c => primR Tuchar q (Vint c)) zs ** [| WF zs |].
    (* The toplevel definition of [zstring.R']: *)
    Definition R' (q : Qp) (zs : t) : Rep :=
      arrayR Tuchar (fun c => primR Tuchar q (Vint c)) zs ** [| WF' zs |].

    #[global] Instance R_WF_observe :
      forall q (zs : t),
        Observe [| WF zs |] (R q zs).
    Proof. refine _. Qed.

    #[global] Instance R'_WF'_observe :
      forall q (zs : t),
        Observe [| WF' zs |] (R' q zs).
    Proof. refine _. Qed.

    Lemma Rs_equiv :
      forall (q : Qp) (zs : t),
        R q zs -|- R' q zs.
    Proof. intros *; by rewrite /R/R' WFs_equiv. Qed.

    Section Theory.
      #[local] Open Scope string_scope.

      Section bufR.
        Remark bufR_nil : forall (q : Qp) (sz : Z), bufR q sz [] |-- False.
        Proof.
          intros *.
          iIntros "rest"; rewrite /bufR.
          iDestruct "rest" as "(?&?& %CONTRA &?)".
          by apply not_WF_nil in CONTRA.
        Qed.

        (* TODO (AUTO): Investigate whether or not this hint actually fires. *)
        #[global] Instance bufR_sz_contra :
          forall (q : Qp) (sz : Z) (zs : t),
            Observe2 False [| sz < size zs |] (bufR q sz zs).
        Proof. intros *; rewrite /Observe2/bufR; iIntros "%H [%CONTRA ?]"; by lia. Qed.

        #[global] Instance bufR_singleton :
          forall (q : Qp) (sz : Z) (z : Z),
            Observe [| z = 0 |]%Z (bufR q sz [z]).
        Proof.
          intros *; rewrite /Observe/bufR; iIntros "(% & Hz & %HWF & rest)".
          iModIntro; iPureIntro; by apply WF_singleton_inj.
        Qed.

        Lemma bufR_cons :
          forall (q : Qp) (sz : Z) (z : Z) (zs : t),
            z <> 0 ->
            bufR q sz (z :: zs) -|-
            primR Tuchar q z ** .[Tu8 ! 1] |-> bufR q (sz - 1) zs.
        Proof.
          intros * Hz; split'.
          - rewrite /bufR arrayR_cons.
            iIntros "[%Hsz [[? [Hz Hzs]] [%HWF Hrest]]]".
            assert (size zs <= sz - 1) by (rewrite size_cons in Hsz; by lia).
            iDestruct (observe [| has_type (Vint z) _ |] with "Hz") as "%".
            assert (WF zs) by (apply WF_cons in HWF; assumption).
            rewrite !_offsetR_sep !_offsetR_only_provable
                    size_cons -_offsetR_sub_sub
                    Z.sub_add_distr;
              by iFrame "∗%".
          - rewrite /bufR arrayR_cons !_offsetR_sep !_offsetR_only_provable;
              iIntros "[H [%Hsz [? [%HWF Hrest]]]]".
            iDestruct (observe (type_ptrR Tuchar) with "H") as "#?".
            assert (size (z :: zs) <= sz) by (rewrite size_cons; by lia).
            iDestruct (observe [| has_type (Vint z) _ |] with "H") as "%".
            assert (WF (z :: zs)) by (apply WF_cons; assumption).
            rewrite size_cons -!_offsetR_sub_sub Z.sub_add_distr.
            iFrame "∗#%"; iPureIntro; by lia.
        Qed.

        #[global] Instance bufR_cons_cons_head_nonzero :
          forall (q : Qp) (sz : Z) (z z' : Z) (zs : t),
            Observe [| z <> 0 |]%Z (bufR q sz (z :: z' :: zs)).
        Proof.
          intros *.
          apply: observe_intro_only_provable.
          rewrite /bufR; unfold WF; iIntros "[%Hsz [Hzs [%WF Hrest]]]"; iPureIntro.
          destruct WF as [zs' [Hzs' HIn]].
          destruct zs'=> //=.
          inversion Hzs'.
          intro CONTRA; apply HIn; subst.
            by constructor.
        Qed.

        Lemma bufR_has_type :
          forall (q : Qp) (sz : Z) (zs : t),
            strlen zs < sz ->
                bufR q sz zs
            |-- bufR q sz zs ** [| List.Forall (fun c => has_type (Vint c) Tuchar) zs |].
        Proof.
          intros **; generalize dependent sz; induction zs; intros **.
          - rewrite {1}bufR_nil; by iIntros.
          - destruct zs=> //=.
            + iIntros "H"; iDestruct (observe [| a = 0 |]%Z with "H") as "%H'".
              iFrame "∗"; iPureIntro.
              try repeat constructor; subst.
              apply has_char_type; rewrite /bound; simpl in *; lia.
            + iIntros "H"; iDestruct (observe [| WF (a :: z :: zs) |] with "H") as "%H'".
              assert (1 <= size (a :: z :: zs)). {
                rewrite -> size_cons in *.
                pose proof (size_nonneg (z :: zs)).
                by lia.
              }
              iDestruct (observe [| a <> 0 |]%Z with "H") as "%H''"; iStopProof.
              rewrite {1}bufR_cons; auto; rewrite primR_has_type IHzs.
              iIntros "[[? %has_type] ?]"; iStopProof.
              rewrite _offsetR_sep _offsetR_only_provable.
              iIntros "[head [tail %has_types]]"; iCombine "head tail" as "H".
              rewrite -bufR_cons; [| done]; iFrame "∗"; iPureIntro.
              apply Forall_cons_2; auto.
              rewrite -> !strlen_cons in *.
              pose proof (size_nonneg (z :: zs)).
              by lia.
        Qed.

        (* TODO (AUTO): Fix this once we add the correct observations for arrayR *)
        #[global] Instance bufR_type_ptrR_observe :
          forall q (sz : Z) (zs : t),
            Observe (type_ptrR Tu8) (bufR q sz zs).
        Proof.
          move=> q sz zs; rewrite /bufR; destruct zs.
          - rewrite /Observe. iIntros "[? [? [%CONTRA ?]]]";
              exfalso; now apply not_WF_nil.
          - rewrite arr.arrayR_cons; refine _.
        Qed.

        #[global] Instance bufR_validR_end_observe :
          forall q (sz : Z) (zs : t),
            Observe (.[Tuchar ! sz] |-> validR) (bufR q sz zs).
        Proof.
          move=> q sz zs; rewrite /bufR/Observe.
          iIntros "[%Hsz [array [%HWF rest]]]".
          iAssert (arrayR Tuchar (fun c => primR Tuchar q (Vint c))
                          (zs ++ repeat 0 (Z.to_nat (sz - size zs))))
            with "[array rest]" as "array'". 2: {
            assert (Z.to_nat sz <= length (zs ++ repeat 0%Z (Z.to_nat (sz - size zs))))%nat
              as AUX. 1: {
              rewrite app_length repeat_length.
              unfold strlen in Hsz.
              unfold size in *.
              lia.
            }
            pose proof (arrayR_valid_obs (λ c : Z, primR Tuchar q c) Tuchar (Z.to_nat sz)
                                         (zs ++ repeat 0 (Z.to_nat (sz - size zs)))
                                         AUX).
            iDestruct (observe (.[ Tnum char_bits Unsigned ! sz ] |-> validR) with "array'")
              as "#?"; auto.
            rewrite Z2Nat.id in H; auto.
            pose proof (size_nonneg zs).
            lia.
          }
          rewrite arrayR_eq/arrayR_def fmap_app arrR_append fmap_length; unfold size.
          iFrame.
          rewrite arrR_proper; [by iFrame |].
          generalize (Z.to_nat (sz - length zs)); intros n.
          induction n=> //=.
          setoid_rewrite IHn.
          rewrite /fmap.
          reflexivity.
        Qed.

        #[global] Instance bufR_validR_inbounds_observe :
          forall q sz (z : Z) (zs : t),
            (0 <= z <= sz)%Z ->
            Observe (.[Tuchar ! z] |-> validR) (bufR q sz zs).
        Proof.
          intros **; generalize dependent zs; induction z; intros **; simpl in *.
          - rewrite ->o_sub_0 by eauto; rewrite _offsetR_id; refine _.
          - assert (Z.pos p < sz \/ Z.pos p = sz)%Z
              as [Hp | Hp] by lia; last by (rewrite Hp; refine _).
            unfold Observe, bufR.
            move: H Hp; generalize (Z.pos p).
            iIntros (z H Hz) "[%SZ [zs [_ zeros]]]".
            assert (z <= length zs \/ length zs < z)%Z
              as [Hz' | Hz'] by lia.
            + iClear "zeros".
              iDestruct (observe (.[Tnum char_bits Unsigned ! z] |-> validR) with "zs")
                as "#valid"; last by iFrame "#".
              pose proof (arrayR_valid_obs
                            (fun c => primR (Tnum char_bits Unsigned) q (Vint c))
                            (Tnum char_bits Unsigned) (Z.to_nat z) zs ltac:(lia)).
              by rewrite ->Z2Nat.id in H0 by lia.
            + iClear "zs".
              iDestruct (observe (.[Tnum char_bits Unsigned ! z] |-> validR) with "zeros")
                as "#valid"; last by iFrame "#".
              assert (exists z', size zs + z' = z /\ 0 <= z')
                as [z' [Hz'' Hneg]]
                by (exists (z - size zs)%Z; unfold size; lia);
                subst.
              rewrite -_offsetR_sub_sub; apply _offsetR_observe.
              pose proof (arrayR_valid_obs
                            (fun c => primR (Tnum char_bits Unsigned) q 0)
                            (Tnum char_bits Unsigned) (Z.to_nat z')
                            (repeat () (Z.to_nat (sz - size zs)))
                            ltac:(rewrite repeat_length; lia)).
              by rewrite ->Z2Nat.id in H0 by lia.
          - by lia.
        Qed.
      End bufR.

      Section bufR'.
        #[local] Ltac lift_WF2WF' H :=
          intros **; rewrite -!bufRs_equiv; by apply H.

        Remark bufR'_nil : forall (q : Qp) (sz : Z), bufR' q sz [] |-- False.
        Proof. lift_WF2WF' bufR_nil. Qed.

        (* TODO (AUTO): Investigate whether or not this hint actually fires. *)
        #[global] Instance bufR'_sz_contra :
          forall (q : Qp) (sz : Z) (zs : t),
            Observe2 False [| sz < size zs |] (bufR' q sz zs).
        Proof. lift_WF2WF' bufR_sz_contra. Qed.

        #[global] Instance bufR'_singleton :
          forall (q : Qp) (sz : Z) (z : Z),
            0 <= sz ->
            Observe [| z = 0 |]%Z (bufR' q sz [z]).
        Proof. lift_WF2WF' bufR_singleton. Qed.

        Lemma bufR'_cons :
          forall (q : Qp) (sz : Z) (z : Z) (zs : t),
            z <> 0 ->
            bufR' q sz (z :: zs) -|-
            primR Tuchar q z ** .[Tu8 ! 1] |-> bufR' q (sz - 1) zs.
        Proof. lift_WF2WF' bufR_cons. Qed.

        #[global] Instance bufR'_cons_cons_head_nonzero :
          forall (q : Qp) (sz : Z) (z z' : Z) (zs : t),
            Observe [| z <> 0 |]%Z (bufR' q sz (z :: z' :: zs)).
        Proof.  lift_WF2WF' bufR_cons_cons_head_nonzero. Qed.

        Lemma bufR'_has_type :
          forall (q : Qp) (sz : Z) (zs : t),
            strlen zs < sz ->
                bufR' q sz zs
            |-- bufR' q sz zs ** [| List.Forall (fun c => has_type (Vint c) Tuchar) zs |].
        Proof. lift_WF2WF' bufR_has_type. Qed.

        #[global] Instance bufR'_type_ptrR_observe :
          forall q (sz : Z) (zs : t),
            Observe (type_ptrR Tu8) (bufR' q sz zs).
        Proof. lift_WF2WF' bufR_type_ptrR_observe. Qed.

        #[global] Instance bufR'_validR_end_observe :
          forall q (sz : Z) (zs : t),
            Observe (.[Tuchar ! sz] |-> validR) (bufR' q sz zs).
        Proof. lift_WF2WF' bufR_validR_end_observe. Qed.

        #[global] Instance bufR'_validR_inbounds_observe :
          forall q sz (z : Z) (zs : t),
            (0 <= z <= sz)%Z ->
            Observe (.[Tuchar ! z] |-> validR) (bufR' q sz zs).
        Proof. lift_WF2WF' bufR_validR_inbounds_observe. Qed.
      End bufR'.

      Lemma bufR_unfold :
        forall (q : Qp) (sz : Z) (zs : t),
          bufR q sz zs -|-
          [| size zs <= sz |] ** R q zs **
          .[ Tuchar ! size zs] |-> arrayR Tuchar (fun _ => primR Tuchar q 0)
                                           (repeat () (Z.to_nat (sz - size zs))).
      Proof.
        intros **; split'.
        - rewrite /bufR/R; iIntros "(%&?&%&?)"; by iFrame "∗%".
        - rewrite /bufR/R; iIntros "[% [[? %] ?]]"; by iFrame "∗%".
      Qed.

      Lemma bufR'_unfold :
        forall (q : Qp) (sz : Z) (cstr : t),
          bufR' q sz cstr -|-
          [| size cstr <= sz |] ** R' q cstr **
          .[ Tuchar ! size cstr] |-> arrayR Tuchar (fun _ => primR Tuchar q 0)
                                             (repeat () (Z.to_nat (sz - size cstr))).
      Proof. intros **; rewrite -!bufRs_equiv -!Rs_equiv; by apply bufR_unfold. Qed.

      Section R_Theory.
        Lemma R_bufR_equiv :
          forall q (zs : t),
            R q zs ≡ bufR q (size zs) zs.
        Proof.
          intros **; rewrite /R/bufR; split'.
          - iIntros "[array %HWF]".
            assert (size zs <= size zs) by lia.
            rewrite Z.sub_diag/= arrayR_nil.
            iDestruct (observe (.[Tuchar ! size zs] |-> validR) with "array") as "#?". 1: {
              unfold size; apply arrayR_valid_obs; by lia.
            }
            rewrite _offsetR_sep _offsetR_only_provable;
              iFrame "#∗%"; iPureIntro; by eauto.
          - iIntros "[%Hzs [array [%HWF rest]]]"; by iFrame "∗%".
        Qed.

        #[local] Ltac try_lift_bufR H :=
          intros **; rewrite !R_bufR_equiv; eapply H; eauto.

        Remark R_nil : forall (q : Qp), R q [] |-- False.
        Proof. try_lift_bufR bufR_nil. Qed.

        #[global] Instance R_singleton :
          forall (q : Qp) (z : Z),
            Observe [| z = 0 |]%Z (R q [z]).
        Proof. try_lift_bufR bufR_singleton. Qed.

        Lemma R_cons :
          forall (q : Qp) (z : Z) (zs : t),
            z <> 0 ->
            R q (z :: zs) -|-
            primR Tuchar q z ** .[Tu8 ! 1] |-> R q zs.
        Proof.
          intros **; rewrite !R_bufR_equiv.
          replace (size zs) with ((size (z :: zs)) - 1)
            by (rewrite size_cons; lia).
          eapply bufR_cons; eauto.
        Qed.

        #[global] Instance R_cons_cons_head_nonzero :
          forall (q : Qp) (z z' : Z) (zs : t),
            Observe [| z <> 0 |]%Z (R q (z :: z' :: zs)).
        Proof. try_lift_bufR bufR_cons_cons_head_nonzero. Qed.

        Lemma R_has_type :
          forall (q : Qp) (zs : t),
                R q zs
            |-- R q zs ** [| List.Forall (fun c => has_type (Vint c) Tuchar) zs |].
        Proof.
          try_lift_bufR bufR_has_type.
          unfold strlen; by lia.
        Qed.

        (* TODO (AUTO): Fix this once we add the correct observations for arrayR *)
        #[global] Instance R_type_ptrR_observe :
          forall q (zs : t),
            Observe (type_ptrR Tu8) (R q zs).
        Proof. try_lift_bufR bufR_type_ptrR_observe. Qed.

        #[global] Instance R_validR_end_observe :
          forall q (zs : t),
            Observe (.[Tuchar ! size zs] |-> validR) (R q zs).
        Proof. try_lift_bufR bufR_validR_end_observe. Qed.

        #[global] Instance R_validR_end_observe' :
          forall q (zs : t),
            Observe (.[Tuchar ! strlen zs] |-> .[Tuchar ! 1] |-> validR) (R q zs).
        Proof.
          intros *; pose proof (R_validR_end_observe q zs).
          rewrite _offsetR_sub_sub; unfold size, strlen in *.
          unfold size in *.
          by replace (length zs - 1 + 1)%Z
            with (Z.of_nat (length zs))
            by lia.
        Qed.

        #[global] Instance R_validR_inbounds_observe :
          forall q (z : Z) (zs : t),
            (0 <= z <= size zs)%Z ->
            Observe (.[Tuchar ! z] |-> validR) (R q zs).
        Proof.
          intros * Hsize; unfold R; unfold size in Hsize.
          apply observe_sep_l.
          pose proof (arrayR_valid_obs
                        (fun c => primR (Tnum char_bits Unsigned) q (Vint c))
                        (Tnum char_bits Unsigned) (Z.to_nat z) zs ltac:(lia)).
          by rewrite ->Z2Nat.id in H by lia.
        Qed.
      End R_Theory.

      Section R'_Theory.
        #[local] Ltac lift_WF2WF' H :=
          intros **; rewrite -!Rs_equiv; by apply H.

        Lemma R'_bufR'_equiv :
          forall q (zs : t),
            R' q zs ≡ bufR' q (size zs) zs.
        Proof. intros **; rewrite -Rs_equiv -bufRs_equiv; by apply R_bufR_equiv. Qed.

        Remark R'_nil : forall (q : Qp), R' q [] |-- False.
        Proof. lift_WF2WF' R_nil. Qed.

        #[global] Instance R'_singleton :
          forall (q : Qp) (z : Z),
            Observe [| z = 0 |]%Z (R' q [z]).
        Proof. lift_WF2WF' R_singleton. Qed.

        Lemma R'_cons :
          forall (q : Qp) (z : Z) (zs : t),
            z <> 0 ->
            R' q (z :: zs) -|-
            primR Tuchar q z ** .[Tu8 ! 1] |-> R' q zs.
        Proof. lift_WF2WF' R_cons. Qed.

        #[global] Instance R'_cons_cons_head_nonzero :
          forall (q : Qp) (z z' : Z) (zs : t),
            Observe [| z <> 0 |]%Z (R' q (z :: z' :: zs)).
        Proof. lift_WF2WF' R_cons_cons_head_nonzero. Qed.

        Lemma R'_has_type :
          forall (q : Qp) (zs : t),
                R' q zs
            |-- R' q zs ** [| List.Forall (fun c => has_type (Vint c) Tuchar) zs |].
        Proof. lift_WF2WF' R_has_type. Qed.

        #[global] Instance R'_type_ptrR_observe :
          forall q (zs : t),
            Observe (type_ptrR Tu8) (R' q zs).
        Proof. lift_WF2WF' R_type_ptrR_observe. Qed.

        #[global] Instance R'_validR_end_observe :
          forall q (zs : t),
            Observe (.[Tuchar ! size zs] |-> validR) (R' q zs).
        Proof. lift_WF2WF' R_validR_end_observe. Qed.

        #[global] Instance R'_validR_end_observe' :
          forall q (zs : t),
            Observe (.[Tuchar ! strlen zs] |-> .[Tuchar ! 1] |-> validR) (R' q zs).
        Proof. lift_WF2WF' R_validR_end_observe'. Qed.

        #[global] Instance R'_validR_inbounds_observe :
          forall q (z : Z) (zs : t),
            (0 <= z <= size zs)%Z ->
            Observe (.[Tuchar ! z] |-> validR) (R' q zs).
        Proof. lift_WF2WF' R_validR_inbounds_observe. Qed.
      End R'_Theory.

      Lemma R_unfold :
        forall (q : Qp) (zs : t),
              R q zs
          -|- arrayR Tuchar (fun c => primR Tuchar q (Vint c)) zs ** [| WF zs |].
      Proof. intros **; split'; by rewrite /R. Qed.

      Lemma R'_unfold :
        forall (q : Qp) (zs : t),
              R' q zs
          -|- arrayR Tuchar (fun c => primR Tuchar q (Vint c)) zs ** [| WF' zs |].
      Proof. intros **; split'; by rewrite /R'. Qed.
    End Theory.
  End with_Σ.
End zstring.

Section zstring_pure_hint_test_pre.
  (* TODO (AUTO; cc/ @paolo): globally setting this prevents the use
       of the [Fail] vernacular.
   *)
  Goal not True.
  Proof.
    (* by auto. *)
    (* > In nested Ltac calls to "by (tactic)" and "tactics.done", last call failed. *)
    (* > No applicable tactic. *)

    Fail (by auto).
    (* > In nested Ltac calls to "by (tactic)" and "tactics.done", last call failed. *)
    (* > No applicable tactic. *)
  Abort.
  #[local] Unset Ltac Backtrace.

  Goal forall {σ : genv}, not (zstring.WF []).
  Proof. Fail (by auto with pure). Abort.

  Goal
    forall z z' z'' zs n,
      zstring.strlen zs = n ->
      zstring.strlen (z :: z' :: z'' :: zs) = 3 + n.
  Proof. intros * Hzs. Fail (by auto with pure). Abort.
End zstring_pure_hint_test_pre.

(* TODO (AUTO; JH): talk with @janno w.r.t the appropriate way to package these; hopefully
     further porting work will elucidate the appropriate export strategy.
 *)
#[global] Hint Resolve
   (* WF lemmas *)
   zstring.not_WF_nil zstring.WF_cons zstring.WFs_equiv
   zstring.WF_singleton zstring.WF_singleton_inj
   zstring.WF_nonempty_inj

   (* Bound Lemmas *)
   zstring.strlen_nonneg zstring.strlen_lowerbound
   zstring.size_nonneg

   (* Symbolic reasoning about [size]/[strlen]; check out the
      [zstring.{size, strlen}_unfold*] lemmas if you wish to
      manually reduce applications which involve ground terms.
    *)
   zstring.strlen_cons zstring.strlen_cons'
   zstring.size_cons zstring.size_cons'
  : pure.

Section zstring_pure_hint_test_post.
  #[local] Unset Ltac Backtrace.

  Goal forall {σ : genv}, not (zstring.WF []).
  Proof. by auto with pure. Abort.

  Goal
    forall z z' z'' zs n,
      zstring.strlen zs = n ->
      zstring.strlen (z :: z' :: z'' :: zs) = 3 + n.
  Proof. intros * Hzs. Fail (by auto with pure). Abort.
End zstring_pure_hint_test_post.
