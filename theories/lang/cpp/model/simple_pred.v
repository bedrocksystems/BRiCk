(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License. 
 * See the LICENSE-BedRock file in the repository root for details. 
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

From bedrock.lang.prelude Require Import base option.
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import pred z_to_bytes.

Implicit Types (vt : validity_type) (σ resolve : genv).

(* todo: does this not exist as a library somewhere? *)
Definition fractionalR (V : Type) : cmraT :=
  prodR fracR (agreeR (leibnizO V)).
Definition frac {V : Type} (q : Qp) (v : V) : fractionalR V :=
  (q, to_agree v).

Lemma frac_op {V} (l : V) (p q : Qp) :
  frac p l ⋅ frac q l ≡ frac (p + q) l.
Proof. by rewrite -pair_op agree_idemp. Qed.

Lemma frac_valid {A : Type} {q1 q2} {v1 v2 : A} :
  ✓ (frac q1 v1 ⋅ frac q2 v2) → ✓ (q1 + q2)%Qp ∧ v1 = v2.
Proof. by move /pair_valid => /= []? /agree_op_invL'. Qed.

Section fractional.
  Context {K V : Type} `{Countable K} `{inG Σ (gmapR K (fractionalR V))}.

  Let gmap_own γ q k v :=
    own (A := gmapR K (fractionalR V)) γ {[ k := frac q v ]}.
  Global Instance fractional_own_frac γ k v :
    Fractional (λ q, gmap_own γ q k v).
  Proof. intros q1 q2. by rewrite -own_op singleton_op frac_op. Qed.

  Global Instance fractional_own_frac_as_fractional γ k v q :
    AsFractional (gmap_own γ q k v) (λ q, gmap_own γ q k v) q.
  Proof. exact: Build_AsFractional. Qed.

  Global Instance gmap_own_agree :
    Observe2 [| v1 = v2 |] (gmap_own γ q1 k v1) (gmap_own γ q2 k v2).
  Proof.
    intros. apply: observe_2_intro_persistent.
    apply bi.wand_intro_r; rewrite /gmap_own -own_op singleton_op.
    rewrite own_valid uPred.discrete_valid singleton_valid.
    by iIntros "!%" => /frac_valid [].
  Qed.

  Global Instance gmap_own_frac_valid γ (q : Qp) k v :
    Observe [| q ≤ 1 |]%Qc (gmap_own γ q k v).
  Proof.
    apply: observe_intro_persistent.
    rewrite /gmap_own own_valid !uPred.discrete_valid singleton_valid.
    by iIntros "!%" => /pair_valid [? _].
  Qed.
End fractional.

(* Stand-in for an actual model of PTRS_FULL.
Ensures that everything needed is properly functorized. *)
Module Type PTRS_I := PTRS <+ PTRS_DERIVED <+ PTR_INTERNAL.
Declare Module PTRS_IMPL : PTRS_I.
Declare Module RAW_BYTES_IMPL : RAW_BYTES.
Module Type PTRS_FULL_I := PTRS_FULL <+ PTR_INTERNAL.
Module Import PTRS_FULL_IMPL : PTRS_FULL_I :=
  PTRS_IMPL <+ RAW_BYTES_IMPL <+ VAL_MIXIN <+ PTRS_MIXIN.

Implicit Types (p : ptr).

(** A consistency proof for [CPP_LOGIC_CLASS] *)
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
    Rval <$> _Z_to_bytes (bytesNat n) (genv_byte_order σ) sgn v.

  Lemma length_Z_to_bytes {σ} n sgn v : length (Z_to_bytes (σ:=σ) n sgn v) = bytesNat n.
  Proof. by rewrite /Z_to_bytes fmap_length _Z_to_bytes_length. Qed.

  Record cpp_ghost : Type :=
    { heap_name : gname
    ; ghost_mem_name : gname
    ; mem_inj_name : gname
    ; blocks_name : gname
    ; code_name : gname
    }.
  Definition _cpp_ghost := cpp_ghost.

  Class cppG' (Σ : gFunctors) : Type :=
    { heapG :> inG Σ (gmapR addr (fractionalR runtime_val'))
      (* ^ this represents the contents of physical memory *)
    ; ghost_memG :> inG Σ (gmapR ptr (fractionalR val))
      (* ^ this represents the contents of the C++ runtime that might
         not be represented in physical memory, e.g. values stored in
         registers or temporaries on the stack *)
    ; mem_injG :> inG Σ (gmapUR ptr (agreeR (leibnizO (option addr))))
      (* ^ this carries the (compiler-supplied) mapping from C++ locations
         (represented as pointers) to physical memory addresses. Locations that
         are not stored in physical memory (e.g. because they are register
         allocated) are mapped to [None] *)
    ; blocksG :> inG Σ (gmapUR ptr (agreeR (leibnizO (Z * Z))))
      (* ^ this represents the minimum and maximum offset of the block *)
    ; codeG :> inG Σ (gmapUR ptr (agreeR (leibnizO (Func + Method + Ctor + Dtor))))
      (* ^ this carries the (compiler-supplied) mapping from C++ locations
         to the code stored at that location *)
    ; has_inv :> invG Σ
    ; has_cinv :> cinvG Σ
    }.

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
      own (A := gmapR ptr (fractionalR val))
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

(* TODO: provide an instance for this. *)
Module Type SimpleCPP_VIRTUAL.
  Import SimpleCPP_BASE.

  Section with_cpp.
    Context `{Σ : cpp_logic}.
    Parameter vbyte : forall (va : addr) (rv : runtime_val') (q : Qp), mpred.

    Axiom vbyte_fractional : forall va rv, Fractional (vbyte va rv).
    Axiom vbyte_timeless : forall va rv q, Timeless (vbyte va rv q).
    Global Existing Instances vbyte_fractional vbyte_timeless.

    Definition vbytes (a : addr) (rv : list runtime_val') (q : Qp) : mpred :=
      [∗list] o ↦ v ∈ rv, (vbyte (a+N.of_nat o)%N v q).

    Global Instance vbytes_fractional va rv : Fractional (vbytes va rv).
    Proof. apply fractional_big_sepL; intros. apply vbyte_fractional. Qed.

    Global Instance vbytes_as_fractional va rv q :
      AsFractional (vbytes va rv q) (vbytes va rv) q.
    Proof. exact: Build_AsFractional. Qed.

    Global Instance vbytes_timeless va rv q : Timeless (vbytes va rv q) := _.
  End with_cpp.
End SimpleCPP_VIRTUAL.

Module SimpleCPP.
  Include SimpleCPP_BASE.
  Include SimpleCPP_VIRTUAL.
  Include PTRS_FULL_IMPL.

  Definition runtime_val := runtime_val'.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    Parameter live_alloc_id : alloc_id -> mpred.
    Axiom live_alloc_id_timeless : forall aid, Timeless (live_alloc_id aid).
    Global Existing Instance live_alloc_id_timeless.

    Definition live_ptr (p : ptr) :=
      default False%I (live_alloc_id <$> ptr_alloc_id p).
    Axiom nullptr_live : |-- live_ptr nullptr.

    (** pointer validity *)
    (** Pointers past the end of an object/array can be valid; see
    https://eel.is/c++draft/expr.add#4 *)
    Definition in_range (vt : validity_type) (l o h : Z) : mpred :=
      [| (l <= o < h)%Z \/ (vt = Relaxed /\ o = h) |].

    Lemma in_range_weaken l o h :
      in_range Strict l o h |-- in_range Relaxed l o h.
    Proof. rewrite /in_range/=. f_equiv. rewrite/impl. tauto. Qed.

    Definition _valid_ptr vt (p : ptr) : mpred :=
      [| p = nullptr |] \\//
            Exists base l h o,
                blocks_own base l h **
                in_range vt l o h ** [| p = offset_ptr_ o base |] **
                [| ptr_vaddr p <> Some 0%N |].
    (* strict validity (not past-the-end) *)
    Notation strict_valid_ptr := (_valid_ptr Strict).
    (* relaxed validity (past-the-end allowed) *)
    Notation valid_ptr := (_valid_ptr Relaxed).

    Instance _valid_ptr_persistent : forall b p, Persistent (_valid_ptr b p) := _.
    Instance _valid_ptr_affine : forall b p, Affine (_valid_ptr b p) := _.
    Instance _valid_ptr_timeless : forall b p, Timeless (_valid_ptr b p) := _.

    (* Needs validity to exclude non-null pointers with 0 addresses but
    non-null provenance (which can be created by pointer arithmetic!) as
    invalid. *)
    Lemma same_address_eq_null p tv :
      _valid_ptr tv p |--
      [| same_address p nullptr <-> p = nullptr |].
    Proof.
      rewrite /_valid_ptr same_address_eq; iIntros "[->|H]";
        [ |iDestruct "H" as (????) "(_ & _ & _ & %Hne)"]; iIntros "!%".
      by rewrite same_property_iff ptr_vaddr_nullptr; naive_solver.
      rewrite same_property_iff; split; last intros ->;
        rewrite ptr_vaddr_nullptr; naive_solver.
    Qed.

    Theorem _valid_ptr_nullptr b : |-- _valid_ptr b nullptr.
    Proof. by iLeft. Qed.

    Lemma strict_valid_relaxed p :
      strict_valid_ptr p |-- valid_ptr p.
    Proof. rewrite /_valid_ptr/=. by setoid_rewrite in_range_weaken. Qed.

    Axiom valid_ptr_alloc_id : forall p,
      valid_ptr p |-- [| is_Some (ptr_alloc_id p) |].
    (** This is a very simplistic definition of [provides_storage].
    A more useful definition should probably not be persistent. *)
    Definition provides_storage (base newp : ptr) (_ : type) : mpred :=
      [| same_address base newp |].
    Lemma provides_storage_same_address base newp ty :
      provides_storage base newp ty |-- [| same_address base newp |].
    Proof. done. Qed.

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
      Proof. by rewrite /aptr fmap_length seq_length. Qed.
      Lemma length_cptr a : length (cptr a) = POINTER_BYTES.
      Proof. by rewrite /cptr length_Z_to_bytes. Qed.

      Lemma bytesNat_pos b : bytesNat b > 0.
      Proof. by case: b =>/=; lia. Qed.

      Lemma bytesNat_nnonnull b : bytesNat b <> 0.
      Proof. have := bytesNat_pos b. lia. Qed.
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

      Lemma cptr_ne_aptr p n : cptr n <> aptr p.
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

      Global Instance encodes_nonvoid t v vs :
        Observe [| t <> Tvoid |] (encodes t v vs).
      Proof. apply: observe_intro_persistent; iIntros "!%". by destruct t. Qed.

      Lemma length_encodes t v vs :
        pure_encodes t v vs ->
          length vs = match erase_qualifiers t with
          | Tbool => 1
          | Tint sz _ => bytesNat sz

          | Tmember_pointer _ _ | Tnullptr | Tpointer _
          | Tfunction _ _ | Treference _ | Trv_reference _ =>
            POINTER_BYTES

          | _ => 1	(* dummy for absurd case, but useful for length_encodes_pos. *)
          end.
      Proof.
        rewrite /pure_encodes => H.
        destruct (erase_qualifiers _) => //;
          destruct v => //; destruct_and? => //;
          repeat case_decide => //;
           simplify_eq; eauto.
      Qed.

      Lemma length_encodes_pos t v vs :
        pure_encodes t v vs ->
        length vs > 0.
      Proof.
        move=> /length_encodes ->. have ?: 1 > 0 by exact: le_n.
        repeat case_match; by [ | exact: bytesNat_pos].
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

      Global Instance encodes_agree t v1 v2 vs :
        Observe2 [| v1 = v2 |] (encodes t v1 vs) (encodes t v2 vs).
      Proof.
        apply: observe_2_intro_persistent; rewrite /encodes /pure_encodes;
          iIntros (H1 H2) "!%".
        destruct (erase_qualifiers t) eqn:? =>//=; intros;
          repeat (try (case_decide || case_match); destruct_and?; simplify_eq => //);
        by [
          edestruct cptr_ne_aptr | edestruct pure_encodes_undef_aptr |
          edestruct pure_encodes_undef_Z_to_bytes |
          f_equiv; exact: Z_to_bytes_inj ].
      Qed.

      Global Instance encodes_consistent t v1 v2 vs1 vs2 :
        Observe2 [| length vs1 = length vs2 |] (encodes t v1 vs1) (encodes t v2 vs2).
      Proof. iIntros "!%". by move=> /length_encodes -> /length_encodes ->. Qed.
    End with_genv.

    Instance Z_to_bytes_proper :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq) (@Z_to_bytes).
    Proof. intros ?? Hσ%genv_byte_order_proper. solve_proper. Qed.

    Instance cptr_proper :
      Proper (genv_leq ==> eq ==> eq) cptr.
    Proof. rewrite /cptr => σ1 σ2 Heq ?? ->. by rewrite Heq. Qed.

    Instance aptr_proper :
      Proper (genv_leq ==> eq ==> eq) aptr.
    Proof. rewrite /aptr => σ1 σ2 Heq ?? ->. by rewrite Heq. Qed.

    Instance encodes_proper :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> lentails) encodes.
    Proof.
      unfold encodes; intros σ1 σ2 Heq t1 t2 -> v1 v2 -> vs1 vs2 ->.
      f_equiv; unfold pure_encodes, impl;
        destruct (erase_qualifiers t2) => //; destruct v2 => //;
        try case_decide; rewrite ?Heq //.
    Qed.

    Definition val_ (a : ptr) (v : val) (q : Qp) : mpred :=
      ghost_mem_own a q v.

    Global Instance val_agree a v1 v2 q1 q2 :
      Observe2 [|v1 = v2|] (val_ a v1 q1) (val_ a v2 q2) := _.

    Global Instance val_frac_valid a v (q : Qp) :
      Observe ([| q ≤ 1 |])%Qc (val_ a v q) := _.

    Instance val_fractional a rv : Fractional (val_ a rv) := _.
    Instance val_as_fractional a rv q :
      AsFractional (val_ a rv q) (val_ a rv) q := _.
    Instance val_timeless a rv q : Timeless (val_ a rv q) := _.


    Definition byte_ (a : addr) (rv : runtime_val) (q : Qp) : mpred :=
      heap_own a q rv.

    Global Instance byte_agree a v1 v2 q1 q2 :
      Observe2 [|v1 = v2|] (byte_ a v1 q1) (byte_ a v2 q2) := _.
    Global Instance byte_frac_valid a rv (q : Qp) :
      Observe ([| q ≤ 1 |])%Qc (byte_ a rv q) := _.

    Instance byte_fractional : Fractional (byte_ a rv) := _.
    Instance byte_as_fractional a rv q :
      AsFractional (byte_ a rv q) (fun q => byte_ a rv q) q := _.
    Instance: Timeless (byte_ a rv q) := _.

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

    Lemma bytes_agree {a vs1 vs2 q1 q2} :
      length vs1 = length vs2 →
      bytes a vs1 q1 ⊢ bytes a vs2 q2 -∗ ⌜vs1 = vs2⌝.
    Proof.
      revert a vs2. induction vs1 as [ |v vs1 IH]=> a vs2.
      { intros ->%symmetry%nil_length_inv. auto. }
      destruct vs2 as [ |v' vs2]; first done. intros [= Hlen].
      rewrite !bytes_cons.
      iIntros "[Hv Hvs1] [Hv' Hvs2] /=".
      iDestruct (byte_agree with "Hv Hv'") as %->.
      by iDestruct (IH _ _ Hlen with "Hvs1 Hvs2") as %->.
    Qed.

    Lemma bytes_frac_valid a vs (q : Qp) :
      length vs > 0 ->
      bytes a vs q |-- [| q ≤ 1 |]%Qc.
    Proof.
      rewrite /bytes; case: vs => [ |v vs _] /=; first by lia.
      rewrite byte_frac_valid. by iIntros "[% _]".
    Qed.

    Instance bytes_timeless a rv q : Timeless (bytes a rv q) := _.
    Instance bytes_fractional a vs : Fractional (bytes a vs) := _.
    Instance bytes_as_fractional a vs q :
      AsFractional (bytes a vs q) (bytes a vs) q.
    Proof. exact: Build_AsFractional. Qed.

    Lemma bytes_update {a : addr} {vs} vs' :
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
        rewrite (_: a + N.of_nat (S k) = a + 1 + N.of_nat k)%N //; lia.
    Qed.

    Instance mem_inj_own_agree p (oa1 oa2 : option N) :
      Observe2 [| oa1 = oa2 |] (mem_inj_own p oa1) (mem_inj_own p oa2).
    Proof.
      apply /observe_2_intro_persistent /bi.wand_intro_r.
      rewrite -own_op singleton_op.
      rewrite own_valid uPred.discrete_valid singleton_valid.
      by iIntros "!%" => /= /agree_op_invL'.
    Qed.

    (** heap points to *)
    (* Auxiliary definitions.
      They're not exported, so we don't give them a complete theory;
      however, some of their proofs can be done via TC inference *)
    Local Definition addr_encodes
        (σ : genv) (t : type) (q : Qp) (a : addr) (v : val) (vs : list runtime_val) :=
      encodes σ t v vs ** bytes a vs q ** vbytes a vs q.

    Local Instance addr_encodes_fractional {σ} ty a v vs :
      Fractional (λ q, addr_encodes σ ty q a v vs) := _.

    Local Instance addr_encodes_agree_dst σ t a v1 v2 vs1 vs2 q1 q2 :
      Observe2 [| vs1 = vs2 |]
        (addr_encodes σ t q1 a v1 vs1)
        (addr_encodes σ t q2 a v2 vs2).
    Proof.
      apply: observe_2_intro_persistent.
      iIntros "[En1 [By1 _]] [En2 [By2 _]]".
      iDestruct (encodes_consistent with "En1 En2") as %Heq.
      by iDestruct (bytes_agree Heq with "By1 By2") as %->.
    Qed.

    Local Instance addr_encodes_agree_src σ t v1 v2 a vs1 vs2 q1 q2 :
      Observe2 [| v1 = v2 |]
        (addr_encodes σ t q1 a v1 vs1)
        (addr_encodes σ t q2 a v2 vs2).
    Proof.
      iIntros "H1 H2".
      iDestruct (addr_encodes_agree_dst with "H1 H2") as %->.
      (* Using encodes_agree *)
      iApply (observe_2 with "H1 H2").
    Qed.

    Global Instance addr_encodes_frac_valid {σ} ty (q : Qp) a v vs :
      Observe [| q ≤ 1 |]%Qc (addr_encodes σ ty q a v vs).
    Proof.
      apply: observe_intro_persistent.
      iDestruct 1 as (Hen%length_encodes_pos) "[B _]".
      by iApply (bytes_frac_valid with "B").
    Qed.

    Local Definition oaddr_encodes
        (σ : genv) (t : type) (q : Qp) (oa : option addr) p (v : val) :=
        match oa with
        | Some a =>
          Exists vs,
          addr_encodes σ t q a v vs
        | None => [| t <> Tvoid |] ** val_ p v q
        end.

    Local Instance oaddr_encodes_fractional {σ} t oa p v :
      Fractional (λ q, oaddr_encodes σ t q oa p v).
    Proof. rewrite /oaddr_encodes; destruct oa; apply _. Qed.

    Local Instance oaddr_encodes_nonvoid {σ} ty q oa p v :
      Observe [| ty <> Tvoid |] (oaddr_encodes σ ty q oa p v).
    Proof. destruct oa; apply _. Qed.
    Local Instance oaddr_encodes_frac_valid {σ} t (q : Qp) oa p v :
      Observe [| q ≤ 1 |]%Qc (oaddr_encodes σ t q oa p v).
    Proof. destruct oa; apply _. Qed.

    Definition code_at (_ : genv) (f : Func) (p : ptr) : mpred :=
      code_own p (inl (inl (inl f))).
    Definition method_at (_ : genv) (m : Method) (p : ptr) : mpred :=
      code_own p (inl (inl (inr m))).
    Definition ctor_at (_ : genv) (c : Ctor) (p : ptr) : mpred :=
      code_own p (inl (inr c)).
    Definition dtor_at (_ : genv) (d : Dtor) (p : ptr) : mpred :=
      code_own p (inr d).

    Instance code_at_persistent : forall s f p, Persistent (@code_at s f p) := _.
    Instance code_at_affine : forall s f p, Affine (@code_at s f p) := _.
    Instance code_at_timeless : forall s f p, Timeless (@code_at s f p) := _.

    Instance method_at_persistent : forall s f p, Persistent (@method_at s f p) := _.
    Instance method_at_affine : forall s f p, Affine (@method_at s f p) := _.
    Instance method_at_timeless : forall s f p, Timeless (@method_at s f p) := _.

    Instance ctor_at_persistent : forall s f p, Persistent (@ctor_at s f p) := _.
    Instance ctor_at_affine : forall s f p, Affine (@ctor_at s f p) := _.
    Instance ctor_at_timeless : forall s f p, Timeless (@ctor_at s f p) := _.

    Instance dtor_at_persistent : forall s f p, Persistent (@dtor_at s f p) := _.
    Instance dtor_at_affine : forall s f p, Affine (@dtor_at s f p) := _.
    Instance dtor_at_timeless : forall s f p, Timeless (@dtor_at s f p) := _.

    Axiom code_at_live   : forall s f p,   @code_at s f p |-- live_ptr p.
    Axiom method_at_live : forall s f p, @method_at s f p |-- live_ptr p.
    Axiom ctor_at_live   : forall s f p,   @ctor_at s f p |-- live_ptr p.
    Axiom dtor_at_live   : forall s f p,   @dtor_at s f p |-- live_ptr p.
    (** physical representation of pointers
     *)
    Definition pinned_ptr (va : N) (p : ptr) : mpred :=
      valid_ptr p **
      ([| p = nullptr /\ va = 0%N |] \\//
      ([| p <> nullptr /\ ptr_vaddr p = Some va |] ** mem_inj_own p (Some va))).

    Instance pinned_ptr_persistent va p : Persistent (pinned_ptr va p) := _.
    Instance pinned_ptr_affine va p : Affine (pinned_ptr va p) := _.
    Instance pinned_ptr_timeless va p : Timeless (pinned_ptr va p) := _.
    (* Currently false, while we fix the model. *)
    Axiom pinned_ptr_eq : forall va p,
      pinned_ptr va p -|- [| pinned_ptr_pure va p |] ** valid_ptr p.
    Instance pinned_ptr_unique va va' p :
      Observe2 [| va = va' |] (pinned_ptr va p) (pinned_ptr va' p).
    Proof.
      apply: observe_2_intro_persistent.
      iIntros "A B".
      iDestruct "A" as "[_ [[->->] | [[%%] A]]]"; iDestruct "B" as "[_ [[%->] | [[%%] B]]]" => //.
      by iDestruct (observe_2_elim_pure (Some va = Some va') with "A B") as %[= ->].
    Qed.

    Lemma pinned_ptr_null : |-- pinned_ptr 0 nullptr.
    Proof. iSplit; by [iApply _valid_ptr_nullptr | iLeft]. Qed.

    (* Not true in the current model, requires making pinned_ptr part of pointers. *)
    Axiom offset_pinned_ptr : forall resolve o n va p,
      eval_offset resolve o = Some n ->
      valid_ptr (p .., o) |--
      pinned_ptr va p -* pinned_ptr (Z.to_N (Z.of_N va + n)) (p .., o).

    Instance pinned_ptr_valid va p :
      Observe (valid_ptr p) (pinned_ptr va p) := _.

    Theorem provides_storage_pinned_ptr : forall res newp aty va,
       provides_storage res newp aty ** pinned_ptr va res |-- pinned_ptr va newp.
    Proof.
      rewrite /provides_storage /pinned_ptr.
      iIntros (????) "[%Hsame ?]".
    Admitted.

    (* XXX: with this definition, we cannot prove all pointers have alignment 1. Again, fix by replacing
    mem_inj_own with a pure function of pointers (returning [option vaddr]). *)
    Definition aligned_ptr (n : N) (p : ptr) : mpred :=
      [| p = nullptr |] \\//
      Exists (o : option addr), mem_inj_own p o **
               match o with
               | Some va => [| (n | va)%N |]
               (* This clause comes from [type_ptr]; here, it means that
               non-pinned pointers are indefinitely aligned.
               However, the whole theory of [aligned_ptr] demands [pinned_ptr], so this is not a real problem. *)
               | None => ltrue
               end.
    Instance aligned_ptr_persistent n p : Persistent (aligned_ptr n p) := _.
    Instance aligned_ptr_affine n p : Affine (aligned_ptr n p) := _.
    Instance aligned_ptr_timeless n p : Timeless (aligned_ptr n p) := _.

    Lemma pinned_ptr_aligned_divide va n p :
      pinned_ptr va p ⊢
      aligned_ptr n p ∗-∗ [| (n | va)%N |].
    Proof.
      rewrite /pinned_ptr /aligned_ptr /=.
      iDestruct 1 as "[_ [[-> ->]|[[%%] MO1]]]". {
        iSplit; last by iIntros; iLeft.
        by iIntros "_ !%"; exact: N.divide_0_r.
      }
      iSplit; last by iIntros; iRight; eauto.
      iDestruct 1 as "[->|H]"; first done; iDestruct "H" as (o) "[MO2 Ha]".
      by iDestruct (mem_inj_own_agree with "MO1 MO2") as "<-".
    Qed.

    Definition type_ptr {resolve : genv} (ty : type) (p : ptr) : mpred :=
      (* To decide: do we want the "p nonnull" clause? *)
      [| p <> nullptr |] **
      (Exists align, [| @align_of resolve ty = Some align |] ** aligned_ptr align p) **

      strict_valid_ptr p ** valid_ptr (p .., o_sub resolve ty 1).
      (* TODO: inline valid_ptr, and assert validity of the range, like we should do in tptsto!
      For 0-byte objects, should we assert ownership of one byte, to get character pointers? *)
      (* alloc_own (alloc_id p) (l, h) **
      [| l <= ptr_addr p <= ptr_addr (p .., o_sub resolve ty 1) <= h  *)

    Instance type_ptr_persistent σ p ty : Persistent (type_ptr (resolve:=σ) ty p) := _.
    Instance type_ptr_affine σ p ty : Affine (type_ptr (resolve:=σ) ty p) := _.
    Instance type_ptr_timeless σ p ty : Timeless (type_ptr (resolve:=σ) ty p) := _.

    Lemma type_ptr_strict_valid resolve ty p :
      type_ptr (resolve := resolve) ty p |-- strict_valid_ptr p.
    Proof. iDestruct 1 as "(_ & _ & $ & _)". Qed.

    Lemma type_ptr_valid_plus_one resolve ty p :
      (* size_of resolve ty = Some sz -> *)
      type_ptr (resolve := resolve) ty p |--
      valid_ptr (p .., o_sub resolve ty 1).
    Proof. iDestruct 1 as "(_ & _ & _ & $)". Qed.

    Lemma type_ptr_nonnull resolve ty p :
      type_ptr (resolve := resolve) ty p |-- [| p <> nullptr |].
    Proof. iDestruct 1 as "($ & _ & _)". Qed.

    Lemma type_ptr_aligned σ ty p :
      type_ptr (resolve := σ) ty p |--
      Exists align, [| @align_of σ ty = Some align |] ** aligned_ptr align p.
    Proof. by iDestruct 1 as "(_ & $ & _)". Qed.

    (* TODO: is o_sub Proper? *)
    Instance o_sub_mono :
      Proper (genv_leq ==> eq ==> eq ==> eq) (@o_sub).
    Admitted.

    Instance type_ptr_mono :
      Proper (genv_leq ==> eq ==> eq ==> (⊢)) (@type_ptr).
    Proof.
      rewrite /type_ptr => σ1 σ2 Heq.
      solve_proper_prepare. do 3 f_equiv.
      - intros ?. (do 2 f_equiv) => Hal1.
        move: Heq => /Proper_align_of /(_ y y eq_refl).
        inversion 1; congruence.
      - f_equiv. by rewrite Heq.
    Qed.


    (* This lemma is unused; it confirms we can lift the other half of
    [pinned_ptr_aligned_divide], but we don't expose this. *)
    Local Lemma pinned_ptr_type_divide_2 {va n σ p ty}
      (Hal : align_of (resolve := σ) ty = Some n) (Hnn : p <> nullptr) :
      pinned_ptr va p ⊢ valid_ptr (p .., o_sub σ ty 1) -∗
      [| (n | va)%N |] -∗ type_ptr (resolve := σ) ty p.
    Proof.
      rewrite /type_ptr Hal /=. iIntros "P #$ %HvaAl"; iFrame (Hnn).
      (* iDestruct (pinned_ptr_valid with "P") as "#$". *)
      iSplit; last admit.
      iExists _; iSplit; first done.
      by iApply (pinned_ptr_aligned_divide with "P").
    Admitted.

    (* XXX move *)
    Axiom align_of_uchar : forall resolve, @align_of resolve T_uchar = Some 1%N.

    (* Requirememnt is too strong, we'd want just [(strict_)valid_ptr p]; see comment
    above on [aligned_ptr] and [mem_inj_own].
    XXX: this assumes that casting to uchar preserves the pointer.
    *)
    Local Lemma valid_type_uchar resolve p (Hnn : p <> nullptr) va :
      pinned_ptr va p ⊢
      valid_ptr (p .., o_sub resolve T_uchar 1) -∗
      type_ptr (resolve := resolve) T_uchar p.
    Proof.
      iIntros "#P #V".
      iApply (pinned_ptr_type_divide_2 (n := 1)) => //. {
        exact: align_of_uchar. }
      iIntros "!%". exact: N.divide_1_l.
    Qed.

    (* todo(gmm): this isn't accurate, but it is sufficient to show that the axioms are
    instantiatable. *)
    Definition identity {σ : genv} (this : globname) (most_derived : option globname)
               (q : Qp) (p : ptr) : mpred := ltrue.

    (** this allows you to forget an object identity, necessary for doing
        placement [new] over an existing object.
     *)
    Theorem identity_forget : forall σ mdc this p,
        @identity σ this (Some mdc) 1 p |-- |={↑pred_ns}=> @identity σ this None 1 p.
    Proof. rewrite /identity. eauto. Qed.

    Definition tptsto {σ:genv} (t : type) (q : Qp) (p : ptr) (v : val) : mpred :=
      [| p <> nullptr |] **
      Exists (oa : option addr),
              type_ptr t p ** (* use the appropriate ghost state instead *)
              mem_inj_own p oa **
              oaddr_encodes σ t q oa p v.
    (* TODO: [tptsto] should not include [type_ptr] wholesale, but its
    pieces in the new model, replacing [mem_inj_own], and [tptsto_type_ptr]
    should be proved properly. *)
    Global Instance tptsto_type_ptr : forall (σ : genv) ty q p v,
      Observe (type_ptr ty p) (tptsto ty q p v) := _.
(*
    Instance tptsto_type_ptr resolve ty q p v align
      (Hal : align_of (resolve := resolve) ty = Some align) :
      Observe (type_ptr (resolve := resolve) ty p)
        (tptsto (σ := resolve) ty q p v).
    Proof.
      apply: observe_intro_persistent.
      rewrite /tptsto /type_ptr.
      f_equiv.
      iDestruct 1 as (oa) "(? & #$ & ?)".
      iSplit; last admit. (* validity of range. *)
      iExists align. iFrame (Hal).
      (* alignment of pointer. *)
    Abort. *)


    Axiom tptsto_live : forall {σ} ty (q : Qp) p v,
      @tptsto σ ty q p v |-- live_ptr p ** True.

    Instance tptsto_nonnull_obs {σ} ty q a :
      Observe False (@tptsto σ ty q nullptr a).
    Proof. iDestruct 1 as (Hne) "_". naive_solver. Qed.
    Theorem tptsto_nonnull {σ} ty q a :
      @tptsto σ ty q nullptr a |-- False.
    Proof. rewrite tptsto_nonnull_obs. iDestruct 1 as "[]". Qed.

    Instance tptsto_mono :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> (⊢)) (@tptsto).
    Proof. rewrite /tptsto /oaddr_encodes /addr_encodes. solve_proper. Qed.

    Instance tptsto_proper :
      Proper (genv_eq ==> eq ==> eq ==> eq ==> eq ==> (≡)) (@tptsto).
    Proof.
      intros σ1 σ2 [Hσ1 Hσ2] ??-> ??-> ??-> ??->.
      by split'; apply tptsto_mono.
    Qed.

    Instance tptsto_fractional {σ} ty p v : Fractional (λ q, @tptsto σ ty q p v) := _.
    Instance tptsto_timeless {σ} ty q p v : Timeless (@tptsto σ ty q p v) := _.

    Global Instance tptsto_nonvoid {σ} ty (q : Qp) p v :
      Observe [| ty <> Tvoid |] (@tptsto σ ty q p v) := _.

    Global Instance tptsto_frac_valid {σ} ty (q : Qp) p v :
      Observe [| q ≤ 1 |]%Qc (@tptsto σ ty q p v) := _.

    Global Instance tptsto_agree σ t q1 q2 p v1 v2 :
      Observe2 [| v1 = v2 |] (@tptsto σ t q1 p v1) (@tptsto σ t q2 p v2).
    Proof.
      apply: observe_2_intro_persistent.
      iDestruct 1 as (Hnn1 oa1) "H1".
      iDestruct 1 as (Hnn2 oa2) "H2".
      iDestruct (observe_2_elim_pure (oa1 = oa2) with "H1 H2") as %->.
      destruct oa2; iApply (observe_2 with "H1 H2").
    Qed.

    Theorem pinned_ptr_borrow {σ} ty p v va :
      @tptsto σ ty 1 p v ** pinned_ptr va p |--
        |={↑pred_ns}=> Exists vs, @encodes σ ty v vs ** vbytes va vs 1 **
                (Forall v' vs', @encodes σ ty v' vs' -* vbytes va vs' 1 -*
                                |={↑pred_ns}=> @tptsto σ ty 1 p v').
    Proof.
      iIntros "(TP & PI)".
      iDestruct "PI" as "[_ [[-> %]|[[%%] MJ]]]"; first by rewrite tptsto_nonnull.
      rewrite /tptsto.
      iDestruct "TP" as (_ ma) "[TP [MJ' OA]]".
      iDestruct (mem_inj_own_agree with "MJ MJ'") as %<-.
      iDestruct "OA" as (vs) "(#EN & Bys & VBys)".
      iIntros "!>".
      iExists vs. iFrame "EN VBys".
      iIntros (v' vs') "#EN' VBys".
      iDestruct (encodes_consistent with "EN EN'") as %Heq.
      iMod (bytes_update vs' Heq with "Bys") as "Bys'".
      iModIntro.
      iSplit; first done. iExists (Some va). iFrame "TP MJ".
      iExists vs'. by iFrame.
    Qed.

    Axiom same_address_eq_type_ptr : forall resolve ty p1 p2 n,
      same_address p1 p2 ->
      size_of resolve ty = Some n ->
      (* if [ty = T_uchar], one of these pointer could provide storage for the other. *)
      ty <> T_uchar ->
      (n > 0)%N ->
      type_ptr ty p1 ∧ type_ptr ty p2 ∧ live_ptr p1 ∧ live_ptr p2 ⊢
        |={↑pred_ns}=> [| p1 = p2 |].

  End with_cpp.

End SimpleCPP.

Module Type SimpleCPP_INTF := SimpleCPP_BASE <+ PTRS_FULL_I <+ CPP_LOGIC.
Module L : SimpleCPP_INTF := SimpleCPP.
