(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
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

(* todo: does this not exist as a library somewhere? *)
Definition fractionalR (V : Type) : cmraT :=
  prodR fracR (agreeR (leibnizO V)).
Definition frac {V : Type} (q : Qp) (v : V) : fractionalR V :=
  (q, to_agree v).

Lemma frac_op {V} (l : V)  (p q : Qp) :
  frac p l ⋅ frac q l ≡ frac (p + q) l.
Proof. by rewrite -pair_op agree_idemp. Qed.

Local Lemma length__Z_to_bytes {σ} n sgn v :
  length (_Z_to_bytes n (values.byte_order σ) sgn v) = n.
Proof. apply _Z_to_bytes_length. Qed.

(** soundness proof *)

Module SimpleCPP_BASE <: CPP_LOGIC_CLASS.

  Definition addr : Set := N.
  Definition byte : Set := N.
  Variant runtime_val' : Set :=
  | Rundef
    (* ^ undefined value, semantically, it means "any value" *)
  | Rval (_ : byte)
    (* ^ machine level byte *)
  | Rpointer_chunk (_ : ptr) (index : nat).
    (* ^ you need the same pointer and consecutive integers to "have" a pointer.
     *)

  Definition Z_to_bytes {σ:genv} (n : bitsize) (sgn: signed) (v : Z) : list runtime_val' :=
    Rval <$> _Z_to_bytes (bytesNat n) (values.byte_order σ) sgn v.

  Lemma length_Z_to_bytes {σ} n sgn v : length (Z_to_bytes (σ:=σ) n sgn v) = bytesNat n.
  Proof. by rewrite /Z_to_bytes fmap_length length__Z_to_bytes. Qed.

  Record cpp_ghost : Type :=
    { heap_name : gname
    ; ghost_mem_name : gname
    ; mem_inj_name : gname
    ; blocks_name : gname
    ; code_name : gname
    }.
  Definition _cpp_ghost := cpp_ghost.

  Class cppG' (Σ : gFunctors) : Type :=
    { heapG : inG Σ (gmapR addr (fractionalR runtime_val'))
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

  Include CPP_LOGIC_CLASS_MIXIN.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Definition heap_own (a : addr) (q : Qp) (r : runtime_val') : mpred :=
      own (A := gmapR addr (fractionalR runtime_val'))
      _ghost.(heap_name) {[ a := frac q r ]}.
    Definition ghost_mem_own (p : ptr) (q : Qp) (v : val) : mpred :=
      own (A := gmapR ptr (fractionalR (leibnizO val)))
        _ghost.(ghost_mem_name) {[ p := frac q v ]}.
    Definition mem_inj_own (p : ptr) (va : option N) : mpred :=
      own (A := gmapUR ptr (agreeR (leibnizO (option addr))))
        _ghost.(mem_inj_name) {[ p := to_agree va ]}.
    Definition blocks_own (p : ptr) (l h : Z) : mpred :=
      own (A := gmapUR ptr (agreeR (leibnizO (Z * Z))))
        _ghost.(blocks_name) {[ p := to_agree (l, h) ]}.

    (** the pointer points to the code

      note that in the presence of code-loading, function calls will
      require an extra side-condition that the code is loaded.
     *)
    Definition code_own (p : ptr) (f : Func + Method + Ctor + Dtor) : mpred :=
      own _ghost.(code_name)
        (A := gmapUR ptr (agreeR (leibnizO (Func + Method + Ctor + Dtor))))
        {[ p := to_agree f ]}.
  End with_cpp.
End SimpleCPP_BASE.

(* TODO: make this a [Module Type] and provide an instance for it. *)
Module SimpleCPP_VIRTUAL.
  Include SimpleCPP_BASE.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Parameter vbyte : forall (va : addr) (rv : runtime_val') (q : Qp), mpred.

    Axiom vbyte_fractional : forall va rv, Fractional (vbyte va rv).
    Axiom vbyte_timeless : forall va rv q, Timeless (vbyte va rv q).
    Global Existing Instances vbyte_fractional vbyte_timeless.

    Definition vbytes (a : addr) (rv : list runtime_val') (q : Qp) : mpred :=
      [∗list] o ↦ v ∈ rv, (vbyte (a+N.of_nat o)%N v q).

    Global Instance: forall va rv, Fractional (vbytes va rv).
    Proof. intros; apply fractional_big_sepL. intros; apply vbyte_fractional. Qed.

    Global Instance: forall va rv q,
      AsFractional (vbytes va rv q) (vbytes va rv) q.
    Proof. constructor; refine _. reflexivity. Qed.

    Global Instance: forall va rv q, Timeless (vbytes va rv q).
    Proof. apply _. Qed.
  End with_cpp.
End SimpleCPP_VIRTUAL.

Module SimpleCPP.
  Include SimpleCPP_VIRTUAL.

  Definition runtime_val := runtime_val'.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    (** pointer validity *)
    (** Pointers past the end of an object/array can be valid; see
    https://eel.is/c++draft/expr.add#4 *)
    Definition valid_ptr (p : ptr) : mpred :=
      [| p = nullptr |] \\//
            Exists base l h o,
                blocks_own base l h **
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

    (** This is a very simplistic definition of [provides_storage].
    A more useful definition should probably not be persistent. *)
    Definition provides_storage (base newp : ptr) (_ : type) : mpred := [| base = newp |].

    Section with_genv.
      Variable σ : genv.

      Let POINTER_BITSZ : bitsize := pointer_size_bitsize σ.
      Notation POINTER_BYTES := (bytesNat POINTER_BITSZ).

      Definition aptr (p : ptr) : list runtime_val :=
        Rpointer_chunk p <$> (seq 0 POINTER_BYTES).

      Notation Z_to_bytes := (Z_to_bytes (σ:=σ)).

      Definition cptr (a : N) : list runtime_val :=
        Z_to_bytes POINTER_BITSZ Unsigned (Z.of_N a).

      Lemma length_aptr p : length (aptr p) = POINTER_BYTES.
      Proof. by rewrite/aptr fmap_length seq_length. Qed.
      Lemma length_cptr a : length (cptr a) = POINTER_BYTES.
      Proof. by rewrite /cptr length_Z_to_bytes. Qed.

      Lemma bytesNat_nnonnull b : bytesNat b <> 0.
      Proof. by destruct b. Qed.
      Local Hint Resolve bytesNat_nnonnull : core.

      Lemma bytesNat_nnonnull' b : bytesNat b = S (pred (bytesNat b)).
      Proof. by rewrite (Nat.succ_pred _ (bytesNat_nnonnull _)). Qed.

      Lemma list_not_nil_cons {T} (xs : list T) : xs <> nil -> ∃ h t, xs = h :: t.
      Proof. case: xs => //= x xs. eauto. Qed.

      Lemma _Z_to_bytes_cons n x y z : n <> 0 -> ∃ a b, _Z_to_bytes n x y z = a :: b.
      Proof.
        intros Hne.
        apply list_not_nil_cons.
        rewrite -(Nat.succ_pred n Hne) {Hne} _Z_to_bytes_eq /_Z_to_bytes_def /=.
        case: x => //= Heq.
        eapply app_cons_not_nil, symmetry, Heq.
      Qed.
      Lemma Z_to_bytes_cons bs x y : ∃ a b, Z_to_bytes bs x y = Rval a :: b.
      Proof.
        unfold Z_to_bytes.
        edestruct _Z_to_bytes_cons as (? & ? & ->) => //; eauto.
      Qed.

      Lemma cptr_ne_aptr p n : cptr p <> aptr n.
      Proof.
        rewrite /cptr /aptr bytesNat_nnonnull'.
        by edestruct Z_to_bytes_cons as (? & ? & ->).
      Qed.

      (** WRT pointer equality, see https://eel.is/c++draft/expr.eq#3 *)
      Definition pure_encodes_undef (n : bitsize) (vs : list runtime_val) : Prop :=
        vs = repeat Rundef (bytesNat n).
      Lemma length_pure_encodes_undef n vs :
        pure_encodes_undef n vs ->
        length vs = bytesNat n.
      Proof. rewrite /pure_encodes_undef => ->. exact: repeat_length. Qed.

      Definition in_Z_to_bytes_bounds (cnt' : bitsize) sgn z :=
        let cnt := bytesNat cnt' in
        match sgn with
        | Signed => (- 2 ^ (8 * cnt - 1) ≤ z)%Z ∧ (z ≤ 2 ^ (8 * cnt - 1) - 1)%Z
        | Unsigned => (0 ≤ z)%Z ∧ (z < 2 ^ (8 * cnt))%Z
        end.

      Lemma _Z_to_bytes_inj_1 cnt endianness sgn z :
        in_Z_to_bytes_bounds cnt sgn z ->
        _Z_from_bytes endianness sgn (_Z_to_bytes (bytesNat cnt) endianness sgn z) = z.
      Proof. apply _Z_from_to_bytes_roundtrip. Qed.

      Lemma _Z_to_bytes_inj_2 cnt endianness sgn z1 z2 :
        in_Z_to_bytes_bounds cnt sgn z1 ->
        in_Z_to_bytes_bounds cnt sgn z2 ->
        _Z_to_bytes (bytesNat cnt) endianness sgn z1 = _Z_to_bytes (bytesNat cnt) endianness sgn z2 ->
        z1 = z2.
      Proof.
        intros Hb1 Hb2 Heq%(f_equal (_Z_from_bytes endianness sgn)).
        move: Heq. by rewrite !_Z_to_bytes_inj_1.
      Qed.
      Instance: Inj eq eq Rval.
      Proof. by injection 1. Qed.

      Lemma Z_to_bytes_inj cnt sgn z1 z2 :
        in_Z_to_bytes_bounds cnt sgn z1 ->
        in_Z_to_bytes_bounds cnt sgn z2 ->
        Z_to_bytes cnt sgn z1 = Z_to_bytes cnt sgn z2 ->
        z1 = z2.
      Proof.
        rewrite /Z_to_bytes; intros Hb1 Hb2 Heq%(inj (fmap Rval)).
        exact: _Z_to_bytes_inj_2.
      Qed.

      Definition pure_encodes (t : type) (v : val) (vs : list runtime_val) : Prop :=
        match erase_qualifiers t with
        | Tint sz sgn =>
          match v with
          | Vint v =>
            in_Z_to_bytes_bounds sz sgn v /\
            vs = Z_to_bytes sz sgn v
          | Vundef => pure_encodes_undef sz vs
          | _ => False
          end
        | Tmember_pointer _ _ =>
          match v with
          | Vint v =>
            (* note: this is really an offset *)
            in_Z_to_bytes_bounds POINTER_BITSZ Unsigned v /\
            vs = Z_to_bytes POINTER_BITSZ Unsigned v
          | Vundef => pure_encodes_undef POINTER_BITSZ vs
          | _ => False
          end
        | Tbool =>
          if decide (v = Vint 0) then vs = [Rval 0%N]
          else if decide (v = Vint 1) then vs = [Rval 1%N]
          else False
        | Tnullptr =>
          vs = cptr 0 /\ v = Vptr nullptr
        | Tfloat _ => False
        | Tarch _ _ => False
        | Tpointer _ =>
          match v with
          | Vptr p =>
            if decide (p = nullptr) then
              vs = cptr 0
            else
              vs = aptr p
          | _ => False
          end
        | Tfunction _ _
        | Treference _
        | Trv_reference _ =>
          match v with
          | Vptr p =>
            p <> nullptr /\
            vs = aptr p
          | Vundef => pure_encodes_undef POINTER_BITSZ vs
          | _ => False
          end
        | Tqualified _ _ => False (* unreachable *)
        | Tvoid
        | Tarray _ _
        | Tnamed _ => False (* not directly encoded in memory *)
        end.
      Definition encodes (t : type) (v : val) (vs : list runtime_val) : mpred :=
        [| pure_encodes t v vs |].

      Global Instance encodes_persistent : forall t v vs, Persistent (encodes t v vs) := _.

      Global Instance encodes_timeless : forall t v a, Timeless (encodes t v a) := _.

      Local Hint Resolve length_Z_to_bytes : core.
      Local Hint Resolve length_aptr : core.
      Local Hint Resolve length_cptr : core.
      Local Hint Resolve length_pure_encodes_undef : core.

      Lemma length_encodes t v vs :
        pure_encodes t v vs ->
          length vs = match erase_qualifiers t with
          | Tbool => 1
          | Tint sz _ => bytesNat sz

          | Tmember_pointer _ _ | Tnullptr | Tpointer _
          | Tfunction _ _ | Treference _ | Trv_reference _ =>
            POINTER_BYTES

          | _ => 0	(* dummy *)
          end.
      Proof.
        rewrite /pure_encodes => H.
        destruct (erase_qualifiers _) => //;
          destruct v => //; destruct_and? => //;
          repeat case_decide => //;
           simplify_eq; eauto.
      Qed.
      Global Instance Inj_aptr: Inj eq eq aptr.
      Proof.
        rewrite /aptr => p1 p2.
        by rewrite bytesNat_nnonnull'; csimpl => -[? _].
      Qed.

      Lemma pure_encodes_undef_aptr bitsz p :
        pure_encodes_undef bitsz (aptr p) -> False.
      Proof.
        rewrite /pure_encodes_undef /aptr.
        by rewrite (bytesNat_nnonnull' POINTER_BITSZ) (bytesNat_nnonnull' bitsz).
      Qed.

      Lemma pure_encodes_undef_Z_to_bytes bitsz sgn z :
        pure_encodes_undef bitsz (Z_to_bytes bitsz sgn z) ->
        False.
      Proof.
        rewrite /pure_encodes_undef /= bytesNat_nnonnull'.
        by edestruct Z_to_bytes_cons as (? & ? & ->).
      Qed.

      Local Hint Resolve pure_encodes_undef_aptr pure_encodes_undef_Z_to_bytes : core.

      Lemma encodes_agree t v1 v2 vs :
        encodes t v1 vs |-- encodes t v2 vs -* [| v1 = v2 |].
      Proof.
        rewrite/encodes/pure_encodes.
        iIntros "%H1 %H2 !%".
        destruct (erase_qualifiers t) eqn:? =>//=; intros;
          repeat (try (case_decide || case_match); destruct_and?; simplify_eq => //).
        all: by [
          edestruct cptr_ne_aptr | edestruct pure_encodes_undef_aptr |
          edestruct pure_encodes_undef_Z_to_bytes |
          f_equiv; exact: Z_to_bytes_inj ].
      Qed.
    End with_genv.

    Instance Z_to_bytes_proper :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq) (@Z_to_bytes).
    Proof.
      intros ?? Hσ. repeat intro. subst. rewrite /Z_to_bytes /_Z_to_bytes_eq /_Z_to_bytes_def.
      f_equal.
      by rewrite ->Hσ.
    Qed.

    Theorem encodes_consistent σ t v1 v2 vs1 vs2 :
      encodes σ t v1 vs1 |-- encodes σ t v2 vs2 -* [| length vs1 = length vs2 |].
    Proof. iIntros "!%". by move=>/length_encodes -> /length_encodes ->. Qed.

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
    Instance: RewriteRelation genv_leq := {}.

    Local Lemma pure_encodes_undef_pointer_size x y xs :
      genv_leq x y ->
      pure_encodes_undef (pointer_size_bitsize x) xs ->
      pure_encodes_undef (pointer_size_bitsize y) xs.
    Proof. by intros ->. Qed.

    Instance encodes_proper :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> lentails) encodes.
    Proof.
      intros ?? Heq; solve_proper_prepare; f_equiv.
      unfold pure_encodes, impl.
      destruct (erase_qualifiers y0); auto.
      all: destruct y1; auto.
      all: try by intuition eauto using pure_encodes_undef_pointer_size.
      all: try by [destruct (decide (p = nullptr)); rewrite Heq; intuition auto].
      all: try by rewrite Heq.
    Qed.

    Definition val_ (a : ptr) (v : val) (q : Qp) : mpred :=
      ghost_mem_own a q v.

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


    Definition byte_ (a : addr) (rv : runtime_val) (q : Qp) : mpred :=
      heap_own a q rv.

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

    Lemma byte_update (a : addr) (rv rv' : runtime_val) :
      byte_ a rv 1 |-- |==> byte_ a rv' 1.
    Proof. by apply own_update, singleton_update, cmra_update_exclusive. Qed.

    Definition bytes (a : addr) (vs : list runtime_val) (q : Qp) : mpred :=
      [∗list] o ↦ v ∈ vs, (byte_ (a+N.of_nat o)%N v) q.

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

    Theorem bytes_consistent {q q' b b' a} : length b = length b' ->
        bytes a b q ** bytes a b' q' |-- bytes a b (q + q') ** [| b = b' |].
    Proof.
      intros. iIntros "[Hb Hb']".
      iDestruct (bytes_agree with "Hb Hb'") as %->; auto.
      by iFrame "Hb Hb' %".
    Qed.

    Lemma bytes_update (a : addr) vs vs' :
      length vs = length vs' →
      bytes a vs 1 |-- |==> bytes a vs' 1.
    Proof.
      rewrite /bytes -big_sepL_bupd.
      revert a vs'.
      induction vs as [ | v vs IH]; intros a vs' EqL.
      { simplify_list_eq. symmetry in EqL. apply length_zero_iff_nil in EqL.
        by subst vs'. }
      destruct vs' as [ |v' vs'].
      { exfalso. done. }
      rewrite 2!big_sepL_cons. apply bi.sep_mono'.
      { by apply byte_update. }
      iPoseProof (IH (a + 1)%N vs') as "HL".
      { simpl in EqL. lia. }
      iIntros "By".
      iDestruct ("HL" with "[By]") as "By";
        iApply (big_sepL_mono with "By"); intros; simpl;
        rewrite (_: a + N.of_nat (S k) = a + 1 + N.of_nat k)%N.
        done. lia. done. lia.
    Qed.

    Lemma mem_inj_own_agree p ma1 ma2 :
      mem_inj_own p ma1 |-- mem_inj_own p ma2 -* [| ma1 = ma2 |].
    Proof.
      iIntros "o1 o2".
      iDestruct (own_valid_2 with "o1 o2") as %X.
      revert X.
      rewrite singleton_op singleton_valid => /agree_op_invL' ?. by subst ma2.
    Qed.

    (* heap points to *)
    Definition tptsto {σ:genv} (t : type) (q : Qp) (p : ptr) (v : val) : mpred :=
      [| p <> nullptr |] **
      Exists (a : option addr),
              mem_inj_own p a **
              match a with
              | Some a =>
                Exists vs,
                encodes σ t v vs ** bytes a vs q ** vbytes a vs q
              | None => val_ p v q
              end.

    Theorem tptsto_nonnull {σ} ty q a :
      @tptsto σ ty q nullptr a |-- False.
    Proof. iDestruct 1 as (Hne) "_". naive_solver. Qed.

    Theorem tptsto_mono :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> (⊢)) (@tptsto).
    Proof. solve_proper. Qed.

    Theorem tptsto_proper :
      Proper (genv_eq ==> eq ==> eq ==> eq ==> eq ==> (≡)) (@tptsto).
    Proof.
      intros σ1 σ2 Hσ ??-> ??-> ??-> ??->.
      split'; eapply tptsto_mono; eauto; apply Hσ.
    Qed.

    Theorem tptsto_fractional {σ} ty p v :
      Fractional (λ q, @tptsto σ ty q p v).
    Proof.
      rewrite /tptsto; apply fractional_sep; first by apply _.
      rewrite /Fractional; intros q1 q2.
      iSplit.
      - iDestruct 1 as ([]) "[#Mi By]".
        + iDestruct "By" as (vs) "(#En & [L1 R1] & [L2 R2])".
          iSplitL "L1 L2"; iExists (Some a); eauto with iFrame.
        + iDestruct "By" as "[L R]".
          iSplitL "L"; iExists None; eauto with iFrame.
      - iIntros "[H1 H2]".
        iDestruct "H1" as (a1) "[#Mi1 By1]".
        iDestruct "H2" as (a2) "[#Mi2 By2]".
        iExists a1; iFrame "#".
        iDestruct (mem_inj_own_agree with "Mi1 Mi2") as %?. subst a2.
        destruct a1; last by iFrame.
        iDestruct "By1" as (vs) "[#En1 [By1 VBy1]]".
        iDestruct "By2" as (vs2) "[#En2 [By2 VBy2]]".
        iDestruct (encodes_consistent with "En1 En2") as %Heq.
        iDestruct (bytes_consistent Heq with "[By1 By2]") as "[Z ->]";
          eauto with iFrame.
    Qed.

    Theorem tptsto_timeless :
      forall {σ} ty q p v, Timeless (@tptsto σ ty q p v).
    Proof. apply _. Qed.

    Theorem tptsto_agree : forall σ t q1 q2 p v1 v2,
        @tptsto σ t q1 p v1 ** @tptsto σ t q2 p v2 |-- [| v1 = v2 |].
    Proof.
      iDestruct 1 as "[H1 H2]".
      iDestruct "H1" as (Hnn1 ma1) "(Hp1 & Hv1)".
      iDestruct "H2" as (Hnn2 ma2) "(Hp2 & Hv2)".
      iDestruct (mem_inj_own_agree with "Hp1 Hp2") as %?. subst ma1.
      iClear "Hp1 Hp2".
      case: ma2=>[a| ]; last by iDestruct (val_agree with "Hv1 Hv2") as %->.
      iDestruct "Hv1" as (vs1) "[He1 [Hb1 Vb1]]".
      iDestruct "Hv2" as (vs2) "[He2 [Hb2 Vb2]]".
      iDestruct (encodes_consistent _ _ _ _ vs1 vs2 with "[He1 He2]") as %?; auto.
      iDestruct (bytes_agree with "Hb1 Hb2") as %->; auto. iClear "Hb1 Hb2".
      iApply (encodes_agree with "He1 He2").
    Qed.

    Definition code_at (_ : genv) (f : Func) (p : ptr) : mpred :=
      code_own p (inl (inl (inl f))).
    Definition method_at (_ : genv) (m : Method) (p : ptr) : mpred :=
      code_own p (inl (inl (inr m))).
    Definition ctor_at (_ : genv) (c : Ctor) (p : ptr) : mpred :=
      code_own p (inl (inr c)).
    Definition dtor_at (_ : genv) (d : Dtor) (p : ptr) : mpred :=
      code_own p (inr d).

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
      iDestruct (mem_inj_own_agree with "A B") as %Hp. by inversion Hp.
    Qed.

    Theorem pinned_ptr_borrow : forall {σ} ty p v va M,
      @tptsto σ ty 1 p v ** pinned_ptr va p ** [| p <> nullptr |] |--
      |={M}=> Exists vs, @encodes σ ty v vs ** vbytes va vs 1 **
              (Forall v' vs', @encodes  σ ty v' vs' -* vbytes va vs' 1 -*
                              |={M}=> @tptsto σ ty 1 p v').
    Proof.
      intros. iIntros "(TP & PI & %)".
      iDestruct "PI" as "[[% %]|[% MJ]]"; [done| ].
      iDestruct "TP" as (_ ma) "[MJ' TP]".
      iDestruct (mem_inj_own_agree with "MJ MJ'") as %?. subst ma.
      iDestruct "TP" as (vs) "(#EN & Bys & VBys)".
      iIntros "!>".
      iExists vs. iFrame "EN VBys".
      iIntros (v' vs') "#EN' VBys".
      iDestruct (encodes_consistent _ _ _ _ vs vs' with "[$EN $EN']") as %EQL.
      iMod (bytes_update _ _ vs' with "Bys") as "Bys'"; first done.
      iModIntro.
      iSplit; first done. iExists (Some va). iFrame "MJ".
      iExists vs'. eauto with iFrame.
    Qed.

    Theorem provides_storage_pinned_ptr : forall res newp aty va,
       provides_storage res newp aty ** pinned_ptr va res |-- pinned_ptr va newp.
    Proof. iIntros (????) "[-> $]". Qed.

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

Module Type SimpleCPP_INTF :=  SimpleCPP_BASE <+ CPP_LOGIC.
Module L : SimpleCPP_INTF := SimpleCPP.
