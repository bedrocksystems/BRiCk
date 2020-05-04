(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From iris.base_logic.lib Require Export iprop.
From iris.bi.lib Require Import fractional.
Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.fancy_updates.
Require Import iris.base_logic.lib.own.
Require Import iris.base_logic.lib.cancelable_invariants.
Require Import iris.algebra.lib.frac_auth.
Require Import iris.algebra.excl.
Require Import iris.algebra.gmap.
Require Import iris.proofmode.tactics.

From bedrock.lang.cpp Require Import ast semantics.
Require Import bedrock.lang.cpp.logic.pred.

Set Default Proof Using "Type".

(* todo: does this not exist as a library somewhere? *)
Definition fractionalR (o : ofeT) : cmraT :=
  prodR fracR (agreeR o).
Definition frac {o: ofeT} (q : Qp) (v : o) : fractionalR o :=
  (q, to_agree v).

Lemma Some_valid:
  forall M (A : cmraT) (x : cmra_car A),
    (@uPred_cmra_valid (iResUR M) (optionR A) (@Some (cmra_car A) x)) -|-
    (@uPred_cmra_valid (iResUR M) A x).
Proof.
  intros M A x.
  rewrite (@uPred_primitive.option_validI (iResUR M) _ (Some x)). reflexivity.
Qed.
Lemma None_valid:
  forall M (A : cmraT) (x : cmra_car A),
    (@uPred_cmra_valid (iResUR M) (optionR A) None) -|- bi_pure True.
Proof.
  intros M A x.
  rewrite (@uPred_primitive.option_validI (iResUR M) _ None). reflexivity.
Qed.

Lemma join_singleton_eq : forall `{Countable K, EqDecision K} {V : cmraT} (k : K) (v1 v2 : V),
    {[ k := v1 ]} ⋅ {[ k := v2 ]} =@{gmap K V} {[ k := v1 ⋅ v2 ]}.
Proof. intros. by apply (merge_singleton _ _ _ v1 v2). Qed.

Lemma singleton_valid_norm :
  ltac:(match type of @singleton_valid with
        | ?T => let X := eval simpl in T in exact X
        end).
Proof. exact @singleton_valid. Defined.

Lemma frac_op {A : ofeT} (l : A)  (p q : Qp) :
  frac p l ⋅ frac q l ≡ frac (p + q) l.
Proof. by rewrite -pair_op agree_idemp. Qed.


(** soundness proof *)

Module SimpleCPP
(*  : CPP_LOGIC. (* Coq takes a long time checking this with the type ascription *) *).

  Definition addr : Set := N.
  Definition byte : Set := N.
  Variant runtime_val : Set :=
  | Rundef
    (* ^ undefined value, semantically, it means "any value" *)
  | Rval (_ : byte)
    (* ^ machine level byte *)
  | Rpointer_chunk (_ : ptr) (index : nat).
    (* ^ you need the same pointer and consecutive integers to "have" a pointer.
     *)

  Class cppG' (Σ : gFunctors) : Type :=
    { memG : inG Σ (gmapR addr (fractionalR (leibnizO runtime_val)))
      (* ^ this represents the contents of physical memory *)
    ; ghost_memG : inG Σ (gmapR ptr (fractionalR (leibnizO val)))
      (* ^ this represents the contents of the C++ runtime that might
         not be represented in physical memory, e.g. values stored in
         registers or temporaries on the stack *)
    ; mem_injG : inG Σ (gmapUR ptr (agreeR (leibnizO (option addr))))
      (* ^ this carries the (compiler-supplied) mapping from C++ locations
         (represented as pointers) to physical memory addresses. Locations that
         are not stored in physical memory (e.g. because they are register
         allocated) are mapped to [None] *)
    ; blocksG : inG Σ (gmapUR ptr (agreeR (leibnizO (Z * Z))))
      (* ^ this represents the minimum and maximum offset of the block *)
    ; codeG : inG Σ (gmapUR ptr (agreeR (leibnizO (Func + Method + Ctor + Dtor))))
      (* ^ this carries the (compiler-supplied) mapping from C++ locations
         to the code stored at that location *)
    ; has_inv' :> invG Σ
    ; has_cinv' :> cinvG Σ
    }.

  Definition cppG : gFunctors -> Type := cppG'.
  Definition has_inv : forall Σ, cppG Σ -> invG Σ := @has_inv'.
  Definition has_cinv : forall Σ, cppG Σ -> cinvG Σ := @has_cinv'.
  Existing Class cppG.

  Record cpp_ghost : Type :=
    { heap_name : gname
    ; ghost_heap_name : gname
    ; mem_inj_name : gname
    ; blocks_name : gname
    ; code_name : gname
    }.
  Definition _cpp_ghost := cpp_ghost.

  Class cpp_logic {thread_info : biIndex} : Type :=
  { _Σ : gFunctors
  ; _ghost : _cpp_ghost
  ; has_cppG :> cppG _Σ }.
  Arguments cpp_logic : clear implicits.
  Coercion _Σ : cpp_logic >-> gFunctors.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    Existing Instances memG ghost_memG mem_injG blocksG codeG.

    Definition mpred := iProp Σ.
    Definition mpredI : bi :=
      {| bi_car := mpred
       ; bi_ofe_mixin := (iPropI Σ).(bi_ofe_mixin)
       ; bi_bi_mixin := (iPropI Σ).(bi_bi_mixin) |}.
    (* todo: Fix the warning generated from this definition *)
    Definition mpredSI : sbi :=
      {| sbi_car := mpred
       ; sbi_ofe_mixin := (iPropI Σ).(bi_ofe_mixin)
       ; sbi_bi_mixin := (iPropI Σ).(bi_bi_mixin)
       ; sbi_sbi_mixin := (iPropSI Σ).(sbi_sbi_mixin) |}.

    Lemma singleton_valid_at_norm :
      ∀ (K : Type) (EqDecision0 : EqDecision K) (H : Countable K) (A : cmraT) (i : K) (x : A),
        ✓ ({[i := x]} : gmap K A) ⊣⊢@{mpredI} ✓ x.
    Proof.
      intros. simpl. rewrite gmap_validI.
      split'.
      - iIntros "X".
        iDestruct ("X" $! i) as "X".
        rewrite lookup_insert.
        iStopProof.
        clear.
        rewrite Some_valid.
        reflexivity.
      - iIntros "X" (lll).
        destruct (decide (i = lll)).
        + subst. rewrite lookup_insert. rewrite Some_valid. iFrame.
        + rewrite lookup_insert_ne; eauto.
    Qed.

    (** pointer validity *)
    Definition valid_ptr (p : ptr) : mpred.
    refine ([| p = nullptr |] \\//
            (Exists base l h o,
                own _ghost.(blocks_name) {[ base := to_agree (l, h) ]} **
                [| (l <= o < h)%Z |] ** [| p = offset_ptr_ o base |])).
    unshelve eapply blocksG; apply has_cppG. refine _.
    Defined.

    Theorem valid_ptr_persistent : forall p, Persistent (valid_ptr p).
    Proof. intros. red. iIntros "#H". iFrame "#". Qed.
    Theorem valid_ptr_affine : forall p, Affine (valid_ptr p).
    Proof. intros. red. iIntros "_". iStopProof. reflexivity. Qed.
    Existing Instance valid_ptr_persistent.
    Existing Instance valid_ptr_affine.

    Theorem valid_ptr_nullptr : |-- valid_ptr nullptr.
    Proof. unfold valid_ptr. iLeft. iModIntro. iStopProof.
           eapply bi.pure_intro. reflexivity.
    Qed.

    Definition Z_to_bytes (n : nat) (v : Z) : list runtime_val :=
      let p := Z.modulo v (2 ^ n) in
      Rval <$> List.rev ((fun i : nat => Z.to_N (Z.land 255 (Z.shiftr p (8 * i)))) <$> seq 0 n).

    Definition size_to_bytes (s : bitsize) : nat :=
      match s with
      | W8 => 1
      | W16 => 2
      | W32 => 4
      | W64 => 8
      | W128 => 16
      end.
    Definition POINTER_BYTES : nat := 8.

    Definition aptr (p : ptr) : list runtime_val :=
      List.map (Rpointer_chunk p) (seq 0 POINTER_BYTES).

    Definition cptr (a : N) : list runtime_val :=
      Z_to_bytes POINTER_BYTES (Z.of_N a).

    Definition encodes (σ : genv) (t : type) (v : val) (vs : list runtime_val) : mpred.
    refine
      match erase_qualifiers t with
      | Tint sz sgn
      | Tchar sz sgn =>
        match v with
        | Vint v => [| vs = Z_to_bytes (size_to_bytes sz) v |]
        | _ => lfalse
        end
      | Tmember_pointer _ _ =>
        match v with
        | Vint v =>
          (* note: this is really an offset *)
          [| vs = Z_to_bytes POINTER_BYTES v |]
        | _ => lfalse
        end

      | Tbool =>
        match v with
        | Vint 0 => [| vs = Rval 0%N :: nil |]
        | Vint 1 => [| vs = Rval 1%N :: nil |]
        | _ => lfalse
        end
      | Tnullptr =>
        [| vs = cptr 0 |]
      | Tfloat _ => lfalse
      | Tarch _ _ => lfalse
      | Tpointer _ =>
        match v with
        | Vptr p =>
          if decide (p = nullptr) then
            [| vs = cptr 0 |]
          else
            Exists (l : option addr),
              own _ghost.(mem_inj_name) {[ p := to_agree l ]} **
              match l with
              | None => [| vs = aptr p |]
              | Some l => [| vs = cptr l |]
              end
        | _ => lfalse
        end
      | Tfunction _ _
      | Treference _
      | Trv_reference _ =>
        match v with
        | Vptr p =>
          [| p <> nullptr |] **
          Exists (l : option addr),
            own _ghost.(mem_inj_name) {[ p := to_agree l ]} **
            match l with
            | None => [| vs = aptr p |]
            | Some l => [| vs = cptr l |]
            end
        | _ => lfalse
        end
      | Tqualified _ _ => lfalse (* unreachable *)
      | Tvoid
      | Tarray _ _
      | Tnamed _ => lfalse (* not directly encoded in memory *)
      end.
    all: try (unshelve eapply mem_injG; apply has_cppG).
    all: refine _.
    Defined.

    Instance encodes_persistent : forall σ t v vs, Persistent (encodes σ t v vs).
    Proof.
      unfold encodes.
      intros; destruct (erase_qualifiers t); intros;
        destruct v; try refine _.
      - destruct (decide (p = nullptr)); refine _.
      - destruct z; refine _.
        destruct p; refine _.
    Qed.

    Instance encodes_proper :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> lentails) encodes.
    Proof.
      do 6 red. intros; subst. reflexivity.
    Qed.

    Local Ltac go_encode X Y :=
      let ll := fresh in
      let rr := fresh in
        iDestruct X as (ll) "[OL ZL]";
        iDestruct Y as (rr) "[OR ZR]";
        iDestruct (own_valid_2 with "OL OR") as X;
        rewrite join_singleton_eq singleton_valid_at_norm
                agree_validI agree_equivI;
        iDestruct X as %[];
        destruct ll; iDestruct "ZR" as %[]; iFrame.

    Theorem encodes_consistent : forall σ t v a b,
        encodes σ t v a ** encodes σ t v b |-- [| a = b |].
    Proof.
      unfold encodes.
      intros; destruct (erase_qualifiers t); intros;
        destruct v; try refine _.
      all: try solve [ iIntros "[X Y]"; iDestruct "X" as %[]
                     | iIntros "[X Y]"; iDestruct "Y" as %[]; iFrame ].
      - destruct (decide (p = nullptr)).
        + iIntros "[X Y]"; iDestruct "Y" as %[]; iFrame.
        + iIntros "[X Y]".
          go_encode "X" "Y".
      - iIntros "[[_ X] [_ Y]]"; go_encode "X" "Y".
      - iIntros "[[_ X] [_ Y]]"; go_encode "X" "Y".
      - iIntros "[[_ X] [_ Y]]"; go_encode "X" "Y".
      - destruct z;
        try (iIntros "[X Y]"; iDestruct "Y" as %[]; iFrame).
        destruct p; try (iIntros "[X Y]"; iDestruct "Y" as %[]; iFrame).
    Qed.

    Instance encodes_timeless : forall σ t v a, Timeless (encodes σ t v a).
    Proof.
      intros. unfold encodes. destruct (erase_qualifiers t); destruct v; refine _.
      - destruct (decide (p = nullptr)); refine _.
      - destruct z; refine _.
        destruct p; refine _.
    Qed.

    Definition val_ (a : ptr) (v : val) (q : Qp) : mpred.
    refine (
      own _ghost.(ghost_heap_name) {[ a := frac (o:=leibnizO val) q v ]}).
    apply (@ghost_memG Σ); apply has_cppG.
    refine _.
    Defined.

    Instance: Fractional (val_ a rv).
    Proof.
      unfold val_. red.
      intros.
      etransitivity; [ | eapply own_op ].
      eapply own_proper.
      by rewrite op_singleton frac_op.
    Qed.

    Instance: AsFractional (val_ a rv q) (fun q => val_ a rv q) q.
    Proof. constructor. reflexivity. refine _. Qed.

    Instance: Timeless (val_ a rv q).
    Proof. intros; refine _. Qed.


    Definition byte_ (a : addr) (rv : runtime_val) (q : Qp) : mpred.
    refine (
      own _ghost.(heap_name) {[ a := frac (o:=leibnizO _) q rv ]}).
    apply (@memG Σ); apply has_cppG.
    refine _.
    Defined.

    Instance: Fractional (byte_ a rv).
    Proof.
      unfold byte_. red.
      intros.
      match goal with
      | |- _ -|- @own ?S ?O ?Z ?G ?L ** own _ ?R =>
        rewrite <- (@own_op S O Z G L R)
      end.
      eapply own_proper.
      red. red. red. simpl. red. intros.
      destruct (decide (a = i)); subst.
      { rewrite lookup_op.
        repeat rewrite lookup_insert.
        rewrite -Some_op.
        rewrite frac_op. reflexivity. }
      { rewrite lookup_op.
        repeat rewrite lookup_singleton_ne; eauto. }
    Qed.

    Instance: AsFractional (byte_ a rv q) (fun q => byte_ a rv q) q.
    Proof. constructor. reflexivity. refine _. Qed.

    Instance: Timeless (byte_ a rv q).
    Proof. intros; refine _. Qed.

    Definition bytes (a : addr) (vs : list runtime_val) (q : Qp) : mpred.
    refine (
      [∗list] ov ∈ zip (seq 0 (List.length vs)) vs,
        (let '(o,rv) := ov in
        byte_ (a+N.of_nat o)%N rv) q)%I.
    Defined.

    Instance: Timeless (bytes a rv q).
    Proof. unfold bytes.
           intros; refine _.
           eapply big_sepL_timeless.
           intros. destruct x.
           refine _.
    Qed.

    Instance: Fractional (bytes a vs).
    Proof. red. unfold bytes.
           intros.
           eapply fractional_big_sepL.
           intros. destruct x. refine _.
    Qed.

    Instance: AsFractional (bytes a vs q) (bytes a vs) q.
    Proof. constructor; refine _. reflexivity. Qed.


    (* heap points to *)
    Definition tptsto {σ:genv} (t : type) (q : Qp) (p : ptr) (v : val) : mpred.
    Proof.
      refine (Exists (a : option addr),
              [| has_type v t |] **
              own _ghost.(mem_inj_name) {[ p := to_agree a ]} **
              match a with
              | Some a =>
                Exists vs,
                encodes σ t v vs ** bytes a vs q
              | None => val_ p v q
              end).
      1: apply (@mem_injG Σ); apply has_cppG.
      refine _.
    Defined.

    Theorem tptsto_proper_entails :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> lentails) (@tptsto).
    Proof.
      do 6 red; intros; subst.
      unfold tptsto.
      iIntros "H".
      iDestruct "H" as (a) "[#De [#Mi Lo]]".
      iExists (a).
      iFrame "#".
      iFrame.
    Qed.
    Theorem tptsto_proper_equiv :
      Proper (genv_eq ==> eq ==> eq ==> eq ==> eq ==> lequiv) (@tptsto).
    Proof.
      do 6 red; intros. split';
       eapply tptsto_proper_entails; eauto; apply H.
    Qed.

    Theorem tptsto_fractional :
      forall {σ} ty p v, Fractional (λ q, @tptsto σ ty q p v).
    Proof.
      red. intros. unfold tptsto.
      iSplit.
      - iIntros "H".
        iDestruct "H" as (a) "[#De [#Mi By]]".
        destruct a.
        + iDestruct "By" as (vs) "[#En By]".
          rewrite fractional.
          iDestruct "By" as "[L R]".
          iSplitL "L".
          * iExists (Some a); iFrame; iFrame "#". iExists vs. iFrame "#". eauto.
          * iExists (Some a); iFrame; iFrame "#". iExists vs. iFrame "#". eauto.
        + rewrite fractional.
          iDestruct "By" as "[L R]".
          iSplitL "L".
          * iExists None; iFrame; iFrame "#".
          * iExists None; iFrame; iFrame "#".
      - iIntros "[H1 H2]".
        iDestruct "H1" as (a) "[#De1 [#Mi1 By1]]".
        iDestruct "H2" as (a2) "[#De2 [#Mi2 By2]]".
        iExists a; iFrame "#".
        iDestruct (own_valid_2 with "Mi1 Mi2") as "X".
        rewrite join_singleton_eq.
        rewrite singleton_valid_at_norm.
        rewrite agree_validI.
        rewrite agree_equivI.
        iDestruct "X" as %[].
        destruct a.
        + iDestruct "By1" as (vs) "[#En1 By1]".
          iDestruct "By2" as (vs2) "[#En2 By2]".
          iDestruct (encodes_consistent with "[En1 En2]") as "Z".
          { iSplit. iApply "En1". iApply "En2". }
          iDestruct "Z" as %[].
          iExists vs; iFrame "#".
          rewrite fractional. iFrame.
        + rewrite fractional. iFrame.
    Qed.
    Theorem tptsto_as_fractional :
      forall {σ} ty q p v, AsFractional (@tptsto σ ty q p v) (λ q, @tptsto σ ty q p v)%I q.
    Proof.
      intros. constructor. reflexivity.
      apply tptsto_fractional.
    Qed.

    Theorem tptsto_timeless :
      forall {σ} ty q p v, Timeless (@tptsto σ ty q p v).
    Proof.
      intros. unfold tptsto. red.
      iIntros "H".
      iDestruct "H" as (a) "[#H [X Y]]".
      iExists a.
      repeat rewrite timeless.
      iSplit; iFrame "#".
      iSplit; iFrame.
    Qed.

    Theorem tptsto_has_type : forall σ t q p v,
        @tptsto σ t q p v |-- @tptsto σ t q p v ** [| has_type v t |].
    Proof.
      unfold tptsto.
      intros.
      iIntros "H".
      iDestruct "H" as (a) "[#H X]".
      iFrame "#".
      iExists a. iFrame.
    Qed.

    (** the pointer points to the code

      note that in the presence of code-loading, function calls will
      require an extra side-condition that the code is loaded.
     *)
    Definition code_at (f : Func) (p : ptr) : mpred.
    refine (own _ghost.(code_name) {[ p := to_agree (inl (inl (inl f))) ]}).
    apply (@codeG Σ); apply has_cppG.
    all: refine _.
    Defined.

    Definition method_at (m : Method) (p : ptr) : mpred.
    refine (own _ghost.(code_name) {[ p := to_agree (inl (inl (inr m))) ]}).
    apply (@codeG Σ); apply has_cppG.
    all: refine _.
    Defined.

    Definition ctor_at (c : Ctor) (p : ptr) : mpred.
    refine (own _ghost.(code_name) {[ p := to_agree (inl (inr c)) ]}).
    apply (@codeG Σ); apply has_cppG.
    all: refine _.
    Defined.

    Definition dtor_at (d : Dtor) (p : ptr) : mpred.
    refine (own _ghost.(code_name) {[ p := to_agree (inr d) ]}).
    apply (@codeG Σ); apply has_cppG.
    all: refine _.
    Defined.

    Theorem code_at_persistent : forall f p, Persistent (@code_at f p).
    Proof. red. intros. iIntros "#X". iFrame "#". Qed.
    Theorem code_at_affine : forall f p, Affine (@code_at f p).
    Proof. red. intros. eauto. Qed.

    Theorem method_at_persistent : forall f p, Persistent (@method_at f p).
    Proof. red. intros. iIntros "#X". iFrame "#". Qed.
    Theorem method_at_affine : forall f p, Affine (@method_at f p).
    Proof. red. intros. eauto. Qed.

    Theorem ctor_at_persistent : forall f p, Persistent (@ctor_at f p).
    Proof. red. intros. iIntros "#X". iFrame "#". Qed.
    Theorem ctor_at_affine : forall f p, Affine (@ctor_at f p).
    Proof. red. intros. eauto. Qed.

    Theorem dtor_at_persistent : forall f p, Persistent (@dtor_at f p).
    Proof. red. intros. iIntros "#X". iFrame "#". Qed.
    Theorem dtor_at_affine : forall f p, Affine (@dtor_at f p).
    Proof. red. intros. eauto. Qed.

  End with_cpp.

End SimpleCPP.
