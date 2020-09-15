(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.algebra Require Import excl gmap.
From iris.algebra.lib Require Import frac_auth.
From iris.bi Require Import monpred.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export iprop.
From iris.base_logic.lib Require Import fancy_updates own.
From iris.base_logic.lib Require Import cancelable_invariants.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import pred z_to_bytes.

Set Default Proof Using "Type".
Set Suggest Proof Using.

(* todo: does this not exist as a library somewhere? *)
Definition fractionalR (V : Type) : cmraT :=
  prodR fracR (agreeR (leibnizO V)).
Definition frac {V : Type} (q : Qp) (v : V) : fractionalR V :=
  (q, to_agree v).

Lemma frac_op {V} (l : V)  (p q : Qp) :
  frac p l ⋅ frac q l ≡ frac (p + q) l.
Proof. by rewrite -pair_op agree_idemp. Qed.

Local Lemma length__Z_to_bytes_le n sgn v :
  length (_Z_to_bytes_le n sgn v) = n.
Proof. apply _Z_to_bytes_le_length. Qed.

Local Lemma length__Z_to_bytes {σ} n sgn v :
  length (_Z_to_bytes (σ:=σ) n sgn v) = n.
Proof. apply _Z_to_bytes_length. Qed.

(** soundness proof *)

Module SimpleCPP_BASE <: CPP_LOGIC_CLASS.

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

  Definition Z_to_bytes {σ:genv} (n : nat) (sgn: signed) (v : Z) : list runtime_val :=
    Rval <$> _Z_to_bytes (σ:=σ) n sgn v.

  Lemma length_Z_to_bytes {σ} n sgn v : length (Z_to_bytes (σ:=σ) n sgn v) = n.
  Proof. by rewrite/Z_to_bytes fmap_length length__Z_to_bytes. Qed.

  Class cppG' (Σ : gFunctors) : Type :=
    { heapG : inG Σ (gmapR addr (fractionalR runtime_val))
      (* ^ this represents the contents of physical memory *)
    ; ghost_memG : inG Σ (gmapR ptr (fractionalR val))
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
    ; has_inv : invG Σ
    ; has_cinv : cinvG Σ
    }.
  Existing Instances heapG ghost_memG mem_injG blocksG codeG has_inv has_cinv.

  Definition cppG : gFunctors -> Type := cppG'.
  Existing Class cppG.
  Instance cppG_cppG' Σ : cppG Σ -> cppG' Σ := id.
  Typeclasses Opaque cppG. (* Prevent turning instances of cppG' into cppG and risking loops. *)

  Record cpp_ghost : Type :=
    { heap_name : gname
    ; ghost_heap_name : gname
    ; mem_inj_name : gname
    ; blocks_name : gname
    ; code_name : gname
    }.
  Definition _cpp_ghost := cpp_ghost.

  Include CPP_LOGIC_CLASS_MIXIN.
End SimpleCPP_BASE.

Module SimpleCPP.
  Include SimpleCPP_BASE.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    (** pointer validity *)
    (** Pointers past the end of an object/array can be valid; see
    https://eel.is/c++draft/expr.add#4 *)
    Definition valid_ptr (p : ptr) : mpred :=
      [| p = nullptr |] \\//
            Exists base l h o,
                own _ghost.(blocks_name) (A := (gmapUR ptr (agreeR (leibnizO (Z * Z)))))
                {[ base := to_agree (l, h) ]} **
                [| (l <= o <= h)%Z |] ** [| p = offset_ptr_ o base |].

    Theorem valid_ptr_persistent : forall p, Persistent (valid_ptr p).
    Proof. apply _. Qed.
    Theorem valid_ptr_affine : forall p, Affine (valid_ptr p).
    Proof. apply _. Qed.
    Theorem valid_ptr_timeless : forall p, Timeless (valid_ptr p).
    Proof. apply _. Qed.
    Existing Instance valid_ptr_persistent.
    Existing Instance valid_ptr_affine.
    Existing Instance valid_ptr_timeless.

    Theorem valid_ptr_nullptr : |-- valid_ptr nullptr.
    Proof. by iLeft. Qed.

    Definition size_to_bytes (s : bitsize) : nat :=
      match s with
      | W8 => 1
      | W16 => 2
      | W32 => 4
      | W64 => 8
      | W128 => 16
      end.

    Section with_genv.
      Variable σ : genv.

      Let POINTER_BYTES : nat := N.to_nat σ.(pointer_size).

      Definition aptr (p : ptr) : list runtime_val :=
        List.map (Rpointer_chunk p) (seq 0 POINTER_BYTES).

      Notation Z_to_bytes := (Z_to_bytes (σ:=σ)).

      Definition cptr (a : N) : list runtime_val :=
        Z_to_bytes POINTER_BYTES Unsigned (Z.of_N a).

      Lemma length_aptr p : length (aptr p) = POINTER_BYTES.
      Proof. by rewrite/aptr fmap_length seq_length. Qed.
      Lemma length_cptr a : length (cptr a) = POINTER_BYTES.
      Proof. by rewrite /cptr length_Z_to_bytes. Qed.

      (** WRT pointer equality, see https://eel.is/c++draft/expr.eq#3 *)
      Definition encodes (t : type) (v : val) (vs : list runtime_val) : mpred :=
        match erase_qualifiers t with
        | Tint sz sgn =>
          match v with
          | Vint v => [| vs = Z_to_bytes (size_to_bytes sz) sgn v |]
          | Vundef => [| length vs = size_to_bytes sz |]
          | _ => lfalse
          end
        | Tmember_pointer _ _ =>
          match v with
          | Vint v =>
            (* note: this is really an offset *)
            [| vs = Z_to_bytes POINTER_BYTES Unsigned v |]
          | Vundef => [| length vs = POINTER_BYTES |]
          | _ => lfalse
          end

        | Tbool =>
          if decide (v = Vint 0) then [| vs = [Rval 0%N] |]
          else if decide (v = Vint 1) then [| vs = [Rval 1%N] |]
          else lfalse
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
              [| vs = aptr p |]
          | _ => lfalse
          end
        | Tfunction _ _
        | Treference _
        | Trv_reference _ =>
          match v with
          | Vptr p =>
            [| p <> nullptr |] **
            [| vs = aptr p |]
          | Vundef => [| length vs = POINTER_BYTES |]
          | _ => lfalse
          end
        | Tqualified _ _ => lfalse (* unreachable *)
        | Tvoid
        | Tarray _ _
        | Tnamed _ => lfalse (* not directly encoded in memory *)
        end.

      Global Instance encodes_persistent : forall t v vs, Persistent (encodes t v vs).
      Proof.
        unfold encodes.
        intros; destruct (erase_qualifiers t); intros;
          destruct v; try refine _.
        - case_decide; refine _.
        - destruct z; refine _.
          destruct p; refine _.
      Qed.

      Global Instance encodes_timeless : forall t v a, Timeless (encodes t v a).
      Proof.
        intros. unfold encodes. destruct (erase_qualifiers t); destruct v; refine _.
        - case_decide; refine _.
        - destruct z; refine _.
          destruct p; refine _.
      Qed.

      Local Hint Resolve bi.False_elim : core.
      Local Hint Resolve length_Z_to_bytes : core.
      Local Hint Resolve length_aptr : core.
      Local Hint Resolve length_cptr : core.

      Lemma length_encodes t v vs :
        encodes t v vs |-- [|
          length vs = match erase_qualifiers t with
          | Tbool => 1
          | Tint sz _ => size_to_bytes sz

          | Tmember_pointer _ _ | Tnullptr | Tpointer _
          | Tfunction _ _ | Treference _ | Trv_reference _ =>
            POINTER_BYTES

          | _ => 0	(* dummy *)
          end
        |].
      Proof.
        rewrite/encodes. destruct (erase_qualifiers _), v; try done; intros;
        repeat match goal with
        | |- [| _ = _ |] |-- [| _ |] => f_equiv=>->
        | |- [| _ ≠ _ |] ** [| _ = _ |] |-- [| _ |] => rewrite bi.sep_elim_r
        | |- context [@decide _ _] => case_decide
        end;
        auto.
      Qed.

      Local Hint Extern 1 =>
        match goal with
        | |- (False ∗ _ ⊢ _)%I => rewrite bi.sep_elim_l; apply bi.False_elim
        | |- (_ ∗ False ⊢ _)%I => rewrite bi.sep_elim_r; apply bi.False_elim
        end : core.
      Lemma encodes_agree t v1 v2 vs :
        encodes t v1 vs |-- encodes t v2 vs -* [| v1 = v2 |].
      Proof.
        apply bi.wand_intro_r.
        rewrite/encodes. case: (erase_qualifiers t)=>//=.
        - move=>_. case: v1; auto=>p1. case: v2; auto=>p2.
          (* PDS: I see no way to proceed when p1 null, p2 nonnull *)
      Abort.
    End with_genv.

    Instance Z_to_bytes_proper :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq) (@Z_to_bytes).
    Proof.
      intros ?? Hσ. repeat intro. subst. unfold Z_to_bytes, _Z_to_bytes.
      f_equal.
      rewrite !seal_eq /_Z_to_bytes_def.
      by setoid_rewrite Hσ.
    Qed.

    Theorem encodes_consistent σ t v1 v2 vs1 vs2 :
        encodes σ t v1 vs1 ** encodes σ t v2 vs2 |-- [| length vs1 = length vs2 |].
    Proof.
      rewrite !length_encodes.
      iDestruct 1 as "[%Ha %Hb]". iPureIntro. by rewrite Ha Hb.
    Qed.

    Instance cptr_proper :
      Proper (genv_leq ==> eq ==> eq) cptr.
    Proof.
      do 3 red; intros; subst.
      unfold cptr. setoid_rewrite H. reflexivity.
    Qed.

    Instance aptr_proper :
      Proper (genv_leq ==> eq ==> eq) aptr.
    Proof.
      do 3 red; intros; subst.
      unfold aptr. setoid_rewrite H. reflexivity.
    Qed.

    Instance encodes_proper :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> lentails) encodes.
    Proof.
      do 5 red. intros; subst.
      unfold encodes.
      destruct (erase_qualifiers y0); auto.
      all: destruct y1; auto.
      all: try (setoid_rewrite H; reflexivity).
      { destruct (decide (p = nullptr)); try setoid_rewrite H; auto. }
    Qed.

    Definition val_ (a : ptr) (v : val) (q : Qp) : mpred :=
      own _ghost.(ghost_heap_name)
      (A := gmapR ptr (fractionalR (leibnizO val)))
      {[ a := frac (o:=leibnizO val) q v ]}.

    Lemma val_agree a v1 v2 q1 q2 :
      val_ a v1 q1 |-- val_ a v2 q2 -* ⌜v1 = v2⌝.
    Proof.
      apply bi.wand_intro_r.
      rewrite/val_ -own_op own_valid singleton_op.
      rewrite uPred.discrete_valid singleton_valid.
      by f_equiv=>/pair_valid [] _ /= /agree_op_invL'.
    Qed.

    Instance: Fractional (val_ a rv).
    Proof.
      unfold val_. red.
      intros. by rewrite -own_op singleton_op frac_op.
    Qed.

    Instance: AsFractional (val_ a rv q) (fun q => val_ a rv q) q.
    Proof. constructor. reflexivity. refine _. Qed.

    Instance: Timeless (val_ a rv q).
    Proof. apply _. Qed.


    (* Note: the current definition doesn't take weak memory into accoutn. In
      particular, it doesn't rely on the thread-local info for the value rv. *)
    Definition byte_ (a : addr) (rv : runtime_val) (q : Qp) : mpred :=
      own _ghost.(heap_name) (A := (gmapR addr (fractionalR (leibnizO runtime_val))))
      {[ a := frac (o:=leibnizO _) q rv ]}.

    Lemma byte_agree a rv1 rv2 q1 q2 :
      byte_ a rv1 q1 |-- byte_ a rv2 q2 -* ⌜rv1 = rv2⌝.
    Proof.
      apply bi.wand_intro_r.
      rewrite/byte_ -own_op own_valid singleton_op.
      rewrite uPred.discrete_valid singleton_valid.
      by f_equiv=>/pair_valid [] _ /= /agree_op_invL'.
    Qed.

    Instance: Fractional (byte_ a rv).
    Proof.
      unfold byte_. red.
      intros. by rewrite -own_op singleton_op frac_op.
    Qed.

    Instance: AsFractional (byte_ a rv q) (fun q => byte_ a rv q) q.
    Proof. constructor. reflexivity. refine _. Qed.

    Instance: Timeless (byte_ a rv q).
    Proof. apply _. Qed.

    Lemma frac_valid {A : Type} q1 q2 (v1 v2 : A) :
      ✓ (frac q1 v1 ⋅ frac q2 v2) → ✓ (q1 + q2)%Qp ∧ v1 = v2.
    Proof. by rewrite pair_valid/= =>-[]? /agree_op_invL'. Qed.

    Theorem byte_consistent a b b' q q' :
      byte_ a b q ** byte_ a b' q' |-- byte_ a b (q + q') ** [| b = b' |].
    Proof.
      iIntros "[Hb Hb']".
      iDestruct (byte_agree with "Hb Hb'") as %->. by iFrame.
    Qed.

    Definition bytes (a : addr) (vs : list runtime_val) (q : Qp) : mpred :=
      ([∗list] o ↦ v ∈ vs, (byte_ (a+N.of_nat o)%N v) q)%I.

    Lemma bytes_nil a q : bytes a [] q -|- emp.
    Proof. done. Qed.

    Lemma bytes_cons a v vs q :
      bytes a (v :: vs) q -|- byte_ a v q ** bytes (N.succ a) vs q.
    Proof.
      rewrite /bytes big_sepL_cons/=. do 2!f_equiv.
      - lia.
      - move=>o v'. f_equiv. lia.
    Qed.

    Lemma bytes_agree a vs1 vs2 q1 q2 :
      length vs1 = length vs2 →
      bytes a vs1 q1 ⊢ bytes a vs2 q2 -∗ ⌜vs1 = vs2⌝.
    Proof.
      revert a vs2. induction vs1 as [ |v vs1 IH]=>a vs2.
      { intros ->%symmetry%nil_length_inv. auto. }
      destruct vs2 as [ |v' vs2]; first done. intros [= Hlen].
      rewrite !bytes_cons.
      iIntros "[Hv Hvs1] [Hv' Hvs2] /=".
      iDestruct (byte_agree with "Hv Hv'") as %->.
      by iDestruct (IH _ _ Hlen with "Hvs1 Hvs2") as %->.
    Qed.

    Instance: Timeless (bytes a rv q).
    Proof. apply _. Qed.

    Instance: Fractional (bytes a vs).
    Proof. apply _. Qed.

    Instance: AsFractional (bytes a vs q) (bytes a vs) q.
    Proof. constructor; refine _. reflexivity. Qed.

    Theorem bytes_consistent : forall q q' b b' a, length b = length b' ->
        bytes a b q ** bytes a b' q' |-- bytes a b (q + q') ** [| b = b' |].
    Proof.
      intros. iIntros "[Hb Hb']".
      iDestruct (bytes_agree with "Hb Hb'") as %->; auto.
      by iFrame "Hb Hb' %".
    Qed.
    Definition mem_inj_own (p : ptr) (va : option N) : mpred :=
      own _ghost.(mem_inj_name) (A := gmapUR ptr (agreeR (leibnizO (option addr))))
        {[ p := to_agree va ]}.

    (* heap points to *)
    Definition tptsto {σ:genv} (t : type) (q : Qp) (p : ptr) (v : val) : mpred :=
      Exists (a : option addr),
              mem_inj_own p a **
              match a with
              | Some a =>
                Exists vs,
                encodes σ t v vs ** bytes a vs q
              | None => val_ p v q
              end.

    Theorem tptsto_mono :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> (⊢)) (@tptsto).
    Proof. solve_proper. Qed.

    Theorem tptsto_proper :
      Proper (genv_eq ==> eq ==> eq ==> eq ==> eq ==> (≡)) (@tptsto).
    Proof.
      intros σ1 σ2 Hσ ??-> ??-> ??-> ??->.
      split'; eapply tptsto_mono; eauto; apply Hσ.
    Qed.

    Theorem tptsto_fractional :
      forall {σ} ty p v, Fractional (λ q, @tptsto σ ty q p v).
    Proof.
      red. intros. unfold tptsto.
      iSplit.
      - iDestruct 1 as ([]) "[#Mi By]".
        + iDestruct "By" as (vs) "(#En & L & R)".
          iSplitL "L"; iExists (Some a); eauto with iFrame.
        + iDestruct "By" as "[L R]".
          iSplitL "L"; iExists None; eauto with iFrame.
      - iIntros "[H1 H2]".
        iDestruct "H1" as (a) "[#Mi1 By1]".
        iDestruct "H2" as (a2) "[#Mi2 By2]".
        iExists a; iFrame "#".
        iDestruct (own_valid_2 with "Mi1 Mi2") as %X.
        revert X.
        rewrite singleton_op singleton_valid => /agree_op_invL' ?. subst a2.
        destruct a.
        + iDestruct "By1" as (vs) "[#En1 By1]".
          iDestruct "By2" as (vs2) "[#En2 By2]".
          iDestruct (encodes_consistent with "[En1 En2]") as "%".
          iSplit; [ iApply "En1" | iApply "En2" ].
          iDestruct (bytes_consistent with "[By1 By2]") as "[Z %]";
            eauto with iFrame.
        + iFrame.
    Qed.

    Theorem tptsto_timeless :
      forall {σ} ty q p v, Timeless (@tptsto σ ty q p v).
    Proof. apply _. Qed.

    Theorem tptsto_agree : forall σ t q1 q2 p v1 v2,
        @tptsto σ t q1 p v1 ** @tptsto σ t q2 p v2 |-- [| v1 = v2 |].
    Proof.
      iDestruct 1 as "[H1 H2]".
      iDestruct "H1" as (ma1) "(Hp1 & Hv1)".
      iDestruct "H2" as (ma2) "(Hp2 & Hv2)".
      iDestruct (own_valid_2 with "Hp1 Hp2") as "%Hv". iClear "Hp1 Hp2".
      move: Hv. rewrite singleton_op singleton_valid=>/agree_op_invL' ->.
      case: ma2=>[a| ]; last by iDestruct (val_agree with "Hv1 Hv2") as %->.
      iDestruct "Hv1" as (vs1) "[He1 Hb1]".
      iDestruct "Hv2" as (vs2) "[He2 Hb2]".
      iDestruct (encodes_consistent _ _ _ _ vs1 vs2 with "[He1 He2]") as %?; auto.
      iDestruct (bytes_agree with "Hb1 Hb2") as %->; auto. iClear "Hb1 Hb2".
      (* PDS: I see no way to proceed. The preceding lemma
      [encodes_agree] seems unsound wrt the present ghost state. *)
      (* GMM: this seems provable as long as neither v1 nor v2 is Vundef.
       *)
    Abort.

    (** the pointer points to the code

      note that in the presence of code-loading, function calls will
      require an extra side-condition that the code is loaded.
     *)
    Local Definition code_ghost_at
      (f : (Func + Method + Ctor + Dtor)) (p : ptr) : mpred :=
      own _ghost.(code_name)
        (A := (gmapUR ptr (agreeR (leibnizO (Func + Method + Ctor + Dtor)))))
        {[ p := to_agree f ]}.

    Definition code_at (_ : genv) (f : Func) (p : ptr) : mpred :=
      code_ghost_at (inl (inl (inl f))) p.
    Definition method_at (_ : genv) (m : Method) (p : ptr) : mpred :=
      code_ghost_at (inl (inl (inr m))) p.
    Definition ctor_at (_ : genv) (c : Ctor) (p : ptr) : mpred :=
      code_ghost_at (inl (inr c)) p.
    Definition dtor_at (_ : genv) (d : Dtor) (p : ptr) : mpred :=
      code_ghost_at (inr d) p.

    Theorem code_at_persistent : forall s f p, Persistent (@code_at s f p).
    Proof. apply _. Qed.
    Theorem code_at_affine : forall s f p, Affine (@code_at s f p).
    Proof. apply _. Qed.
    Theorem code_at_timeless : forall s f p, Timeless (@code_at s f p).
    Proof. apply _. Qed.

    Theorem method_at_persistent : forall s f p, Persistent (@method_at s f p).
    Proof. apply _. Qed.
    Theorem method_at_affine : forall s f p, Affine (@method_at s f p).
    Proof. apply _. Qed.
    Theorem method_at_timeless : forall s f p, Timeless (@method_at s f p).
    Proof. apply _. Qed.

    Theorem ctor_at_persistent : forall s f p, Persistent (@ctor_at s f p).
    Proof. apply _. Qed.
    Theorem ctor_at_affine : forall s f p, Affine (@ctor_at s f p).
    Proof. apply _. Qed.
    Theorem ctor_at_timeless : forall s f p, Timeless (@ctor_at s f p).
    Proof. apply _. Qed.

    Theorem dtor_at_persistent : forall s f p, Persistent (@dtor_at s f p).
    Proof. apply _. Qed.
    Theorem dtor_at_affine : forall s f p, Affine (@dtor_at s f p).
    Proof. apply _. Qed.
    Theorem dtor_at_timeless : forall s f p, Timeless (@dtor_at s f p).
    Proof. apply _. Qed.

    (** physical representation of pointers
     *)
    Definition pinned_ptr (va : N) (p : ptr) : mpred :=
      [| p = nullptr /\ va = 0%N |] \\//
      ([| p <> nullptr |] ** mem_inj_own p (Some va)).

    Theorem pinned_ptr_persistent : forall va p, Persistent (pinned_ptr va p).
    Proof. apply _. Qed.
    Theorem pinned_ptr_affine : forall va p, Affine (pinned_ptr va p).
    Proof. apply _. Qed.
    Theorem pinned_ptr_timeless : forall va p, Timeless (pinned_ptr va p).
    Proof. apply _. Qed.
    Theorem pinned_ptr_unique : forall va va' p,
        pinned_ptr va p ** pinned_ptr va' p |-- bi_pure (va = va').
    Proof.
      intros. iIntros "[A B]".
      iDestruct "A" as "[[->->] | [% A]]"; iDestruct "B" as "[[%->] | [% B]]"; auto.
      iDestruct (own_valid_2 with "A B") as %Hp. iPureIntro.
      move: Hp. rewrite singleton_op singleton_valid=>/agree_op_invL'. by case.
    Qed.

    Definition type_ptr {resolve : genv} (c: type) (p : ptr) : mpred :=
      Exists (o : option addr) n,
               [| @align_of resolve c = Some n |] ** mem_inj_own p o **
               match o with
               | None => ltrue
               | Some addr => [| N.modulo addr n = 0%N |]
               end.

    Theorem type_ptr_persistent : forall σ p ty,
        Persistent (type_ptr (resolve:=σ) ty p).
    Proof. refine _. Qed.

    (* todo(gmm): this isn't accurate, but it is sufficient to show that the axioms are
    instantiatable. *)
    Definition identity {σ : genv} (this : globname) (most_derived : option globname)
               (q : Qp) (p : ptr) : mpred := ltrue.

    (** this allows you to forget an object identity, necessary for doing
        placement [new] over an existing object.
     *)
    Theorem identity_forget : forall σ mdc this p,
        @identity σ this (Some mdc) 1 p |-- @identity σ this None 1 p.
    Proof. rewrite /identity. eauto. Qed.

  End with_cpp.

End SimpleCPP.

Module Type SimpleCPP_INTF := SimpleCPP_BASE <+ CPP_LOGIC.
Module L : SimpleCPP_INTF := SimpleCPP.
