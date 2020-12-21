(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.algebra Require Import list.
From iris.bi Require Import monpred big_op.
From iris.proofmode Require Import tactics.
From bedrock.lang Require Import prelude.numbers bi.observe bi.big_op.
(* From bedrock.auto Require Import cpp. *)
From bedrock.lang.cpp.semantics Require Import types genv.
From bedrock.lang.cpp.logic Require Import pred path_pred heap_pred.
From bedrock.lang.cpp Require Import heap_notations.
From bedrock.lang.cpp.semantics Require Import values.

Local Set Printing Coercions.	(** Readability *)

(** PDS: Mispalced *)
Local Arguments N.of_nat _ : simpl never.
Local Arguments N.to_nat _ : simpl never.

Local Arguments _offsetR {_ _} _ _%bi_scope.

Lemma size_of_array_0_Some σ ty :
  is_Some (size_of σ ty) → size_of σ (Tarray ty 0) = Some 0%N.
Proof. by move=>[]sz /= ->. Qed.
Local Hint Resolve size_of_array_0_Some : core.
Lemma size_of_array_0_None σ ty :
  size_of σ ty = None → size_of σ (Tarray ty 0) = None.
Proof. by move=>/= ->. Qed.
Local Hint Resolve size_of_array_0_None : core.

Section simpl_never.
  Local Arguments N.mul : simpl never.
  Lemma size_of_array_1 σ ty : size_of σ (Tarray ty 1) = size_of σ ty.
  Proof. simpl. case: (size_of _ ty) => //= s. f_equiv. apply: left_id. Qed.
End simpl_never.
Local Hint Resolve size_of_array_1 : core.

(** PDS: Misplaced *)

(** PDS: Misplaced *)
Section offsetR.
  Context `{Σ : cpp_logic, resolve : genv}.

  Lemma monPred_at_offsetR offs R p :
    (_offsetR offs R) p -|- R (p ., offs).
  Proof. by rewrite _offsetR_eq. Qed.
End offsetR.

Implicit Types (p : ptr) (σ : genv).

Section validR.
  Context `{Σ : cpp_logic}.

  Lemma monPred_at_validR p : validR p -|- valid_ptr p.
  Proof. by rewrite validR_eq. Qed.
  Lemma monPred_at_svalidR p : svalidR p -|- strict_valid_ptr p.
  Proof. by rewrite svalidR_eq. Qed.
  Lemma monPred_at_type_ptrR ty σ p : type_ptrR ty p -|- type_ptr ty p.
  Proof. by rewrite type_ptrR_eq. Qed.

  Lemma _at_validR p : p |-> validR -|- valid_ptr p.
  Proof. by rewrite _at_eq validR_eq. Qed.
  Lemma _at_svalidR p : p |-> svalidR -|- strict_valid_ptr p.
  Proof. by rewrite _at_eq svalidR_eq. Qed.
  Lemma _at_type_ptrR σ ty p : p |-> type_ptrR ty -|- type_ptr ty p.
  Proof. by rewrite _at_eq type_ptrR_eq. Qed.

  Lemma type_ptrR_validR_plus_one (ty : type) σ :
    type_ptrR ty ⊢@{RepI (Σ := Σ)} .[ ty ! 1 ] |-> validR .
  Proof.
    constructor => p.
    rewrite monPred_at_offsetR monPred_at_type_ptrR monPred_at_validR.
    exact: type_ptr_valid_plus_one.
  Qed.

  (** [validR] and [_at] *)

  (* Lemma _at_offsetR_validR p (o : offset) :
    _at p (_offsetR o validR) -|- valid_ptr (_offset_ptr p o).
  Proof. by rewrite _at_offsetL_offsetR _at_validR. Qed. *)

  Lemma _sub_inv ty i resolve :
    _offsetR (_sub ty i) validR |-- [| is_Some (size_of resolve ty) |].
  Proof.
    constructor => p.
    rewrite monPred_at_offsetR monPred_at_validR monPred_at_only_provable.
    apply valid_o_sub_size.
  Qed.

  Lemma _sub_0 {resolve : genv} ty R :
    is_Some (size_of resolve ty) ->
    _offsetR (_sub ty 0) R -|- R.
  Proof.
    constructor=>/= p.
    by rewrite monPred_at_offsetR /= o_sub_0 // offset_ptr_id.
  Qed.

  Lemma _sub_offsetR_add {resolve : genv} ty a b R :
    _sub ty a |-> validR ⊢
    _offsetR (_sub ty (a + b)) R ∗-∗
    _offsetR (_sub ty a) (_offsetR (_sub ty b) R).
  Proof.
    constructor=>/= p.
    rewrite Rep_at_wand_iff /as_Rep /=.
    rewrite _offsetR_eq /_offsetR_def validR_eq /validR_def /=.
    iIntros "#V"; iDestruct (o_sub_sub with "V") as %->.
    by iApply bi.wand_iff_refl.
  Qed.
End validR.

Definition arrR_def `{Σ : cpp_logic} (ty : type) {σ : genv} (Rs : list Rep) : Rep :=
  [∗ list] i ↦ Ri ∈ Rs, _offsetR (_sub ty (Z.of_nat i)) (type_ptrR ty ** Ri).
Definition arrR_aux : seal (@arrR_def). Proof. by eexists. Qed.
Definition arrR := arrR_aux.(unseal).
Definition arrR_eq : @arrR = _ := arrR_aux.(seal_eq).
Arguments arrR {_ _} _ {_} _%list_scope : assert.
Instance: Params (@arrR) 4 := {}.	(** TODO: [genv] weakening *)

Definition arrayR_def `{Σ : cpp_logic} {X : Type} {σ : genv} (ty : type) (P : X → Rep) (xs : list X) : Rep :=
  arrR ty (P <$> xs).
Definition arrayR_aux : seal (@arrayR_def). Proof. by eexists. Qed.
Definition arrayR := arrayR_aux.(unseal).
Definition arrayR_eq : @arrayR = _ := arrayR_aux.(seal_eq).
Arguments arrayR {_ _ _ _} _ _%function_scope _%list_scope : assert.
Instance: Params (@arrayR) 5 := {}.	(** TODO: [genv] weakening *)

Section arrR.
  Context `{Σ : cpp_logic, σ : genv}.

  Global Instance arrR_ne ty : NonExpansive (arrR ty).
  Proof.
    intros n l1 l2 Hl. rewrite arrR_eq /arrR_def.
    have Hlen := Forall2_length _ _ _ Hl.
    apply big_sepL_gen_ne; first done.
    move=>k y1 y2 Hl1 Hl2. apply _offsetR_ne, bi.sep_ne, (inj Some); first done.
    rewrite -Hl1 -Hl2. by apply list_dist_lookup.
  Qed.
  Global Instance arrR_proper ty : Proper ((≡) ==> (≡)) (arrR ty).
  Proof.
    intros l1 l2 Hl. rewrite arrR_eq /arrR_def.
    have Hlen : length l1 = length l2 by apply (Forall2_length (≡)), equiv_Forall2.
    apply big_sepL_gen_proper; first done.
    move=>k y1 y2 Hl1 Hl2. apply _offsetR_proper, bi.sep_proper, (inj Some); first done.
    rewrite -Hl1 -Hl2. by apply list_equiv_lookup.
  Qed.
  (** We don't register this as an instance because it doesn't hold in
      arbitrary non-affine BIs. *)
  Remark arrR_timeless_when_mpred_affine ty Rs :
    TCForall Timeless Rs → Timeless (arrR ty Rs).
  Proof.
    rewrite TCForall_Forall Forall_forall=>HR. rewrite arrR_eq /arrR_def.
    apply big_sepL_gen_timeless=>k x Hk.
    apply _offsetR_timeless, (bi.sep_timeless _ _ _), HR. exact: elem_of_list_lookup_2.
  Qed.
  Global Instance arrR_persistent ty Rs :
    TCForall Persistent Rs → Persistent (arrR ty Rs).
  Proof.
    rewrite TCForall_Forall Forall_forall=>HR. rewrite arrR_eq /arrR_def.
    apply big_sepL_gen_persistent=>k x Hk.
    apply _offsetR_persistent, (bi.sep_persistent _ _ _), HR. exact: elem_of_list_lookup_2.
  Qed.
  Global Instance arrR_affine ty Rs :
    TCForall Affine Rs → Affine (arrR ty Rs).
  Proof.
    rewrite TCForall_Forall Forall_forall=>HR. rewrite arrR_eq /arrR_def.
    apply big_sepL_gen_affine=>k x Hk.
    apply _offsetR_affine, (bi.sep_affine _ _ _), HR. exact: elem_of_list_lookup_2.
  Qed.

  Lemma arrR_nil ty : arrR ty [] -|- emp.
  Proof. by rewrite arrR_eq /arrR_def /=. Qed.

  Lemma big_sepL_offsetR (o : offset) {T} (Rs : list T) : forall F,
    (o |-> [∗list] i ↦ x ∈ Rs , F i x) -|- [∗list] i ↦ x ∈ Rs , o |-> F i x.
  Proof.
    induction Rs; simpl; intros.
    - by rewrite _offsetR_emp.
    - by rewrite _offsetR_sep IHRs.
  Qed.

  Global Instance arrR_inv ty R Rs : Observe ([| is_Some (size_of σ ty) |]) (arrR ty (R :: Rs)).
  Proof.
    apply: observe_intro_persistent.
    rewrite arrR_eq /arrR_def /= !_offsetR_sep.
    constructor =>p/=.
    rewrite !monPred_at_sep !monPred_at_offsetR/= !monPred_at_only_provable !monPred_at_type_ptrR.
    rewrite type_ptr_strict_valid strict_valid_relaxed.
    rewrite valid_o_sub_size.
    iIntros "[[$ _] _]".
  Qed.

  Lemma arrR_cons ty R Rs :
    is_Some (size_of σ ty) → (* this side condition is annoying *)
    arrR ty (R :: Rs) -|- type_ptrR ty ** R ** .[ ty ! 1] |-> arrR ty Rs.
  Proof.
    intros. rewrite arrR_eq /arrR_def /=.
    rewrite _offsetR_sep !_sub_0 // (assoc bi_sep); f_equiv.
    rewrite big_sepL_offsetR. f_equiv => i r.
    apply Rep_equiv_at => p.
    rewrite !_at_offsetL_offsetR.
    rewrite Nat2Z.inj_succ -Z.add_1_l.
    rewrite o_sub_sub_nneg //; lia.
  Qed.

  (*
  TODO to drop side-condition: make o_sub_0 unconditional, or deduce side condition from type_ptr.
   *)

  (* Debatable, more than dropping size_of from o_sub_0. *)
  (*
  Axiom type_ptr_size : forall p σ ty,
    type_ptr ty p |-- [| is_Some (size_of σ ty) |].
  Local Instance type_ptr_size_observe ty p :
    Observe [| is_Some (size_of σ ty) |] (type_ptr ty p).
  Proof. rewrite type_ptr_size. exact: observe_intro_persistent. Qed.

  Local Instance type_ptrR_size_observe ty :
    Observe [| is_Some (size_of σ ty) |] (type_ptrR ty).
  Proof.
    (* XXX lifting an observation should be easier. *)
    apply: observe_intro_persistent.
    constructor=>p.
    rewrite monPred_at_type_ptrR monPred_at_only_provable.
    exact: type_ptr_size.
  Qed.

  Lemma arrR_cons ty R Rs :
    arrR ty (R :: Rs) -|- type_ptrR ty ** R ** _offsetR (_sub ty 1) (arrR ty Rs).
  Proof.
    iSplit; iIntros "H";
    iDestruct (observe [| is_Some (size_of σ ty) |] with "H") as %?;
    by rewrite arrR_cons'.
  Qed.
  *)

  (* TODO Same game here: *)
  Lemma arrR_singleton ty R
    (Hsz : is_Some (size_of σ ty)) :
    arrR ty [R] -|-
    type_ptrR ty ** R.
  Proof. by rewrite arrR_eq /arrR_def /= right_id _offsetR_sep !_sub_0. Qed.
End arrR.

Section array.
  Context `{Σ : cpp_logic, resolve : genv}.
  Context {X : Type} (R : X -> Rep) (ty : type).

  Lemma arrayR_nil : arrayR ty R [] -|- emp.
  Proof. by rewrite arrayR_eq /arrayR_def arrR_nil. Qed.

  Section has_size.
  (** Compared to [array'_valid], this is a bientailment *)
    Context (Hsz : is_Some (size_of resolve ty)).
    Set Default Proof Using "Hsz".

  Lemma arrayR_cons x xs :
    arrayR ty R (x :: xs) -|- type_ptrR ty ** R x ** .[ ty ! 1 ] |-> arrayR ty R xs.
  Proof. rewrite arrayR_eq. exact: arrR_cons. Qed.

  Lemma arrayR_sub_type_ptr_nat (i : nat) xs
    (Hlen : i < length xs) :
    Observe (.[ ty ! i ] |-> type_ptrR ty) (arrayR ty R xs).
  Proof.
    apply: observe_intro_persistent.
    elim: xs i Hlen => [|x xs IHxs] [|i] /= Hlen; try lia;
      rewrite arrayR_cons.
    { rewrite o_sub_0 // _offsetR_id. iDestruct 1 as "[$ _]". }
    {
      rewrite (IHxs i); try lia.
      constructor=> p' /=.
      rewrite !monPred_at_sep !monPred_at_offsetR.
      (* XXX can't be done at the Rep level *)
      rewrite o_sub_sub_nneg; try lia.
      rewrite Z.add_1_l Nat2Z.inj_succ.
      iDestruct 1 as "(_ & _ & $)". }
  Qed.

  Lemma arrayR_sub_type_ptr (i : Z) xs :
    (0 ≤ i < Z.of_nat $ length xs)%Z →
    Observe (.[ ty ! i ] |-> type_ptrR ty) (arrayR ty R xs).
  Proof.
    intros []. have := arrayR_sub_type_ptr_nat (Z.to_nat i) xs.
    rewrite Z2Nat.id //. apply. lia.
  Qed.

  Global Instance _at_observe {p} {P Q : Rep} :
    Observe Q P ->
    Observe (_at p Q) (_at p P).
  Proof. rewrite /Observe => ->. by rewrite _at_pers. Qed.

  Lemma _at_arrayR_sub_type_ptrR_nat (i : nat) p xs
    (Hlen : i < length xs) :
    Observe (p .[ ty ! i ] |-> type_ptrR ty) (p |-> arrayR ty R xs).
  Proof.
    rewrite -_at_offsetL_offsetR //. by apply _at_observe, arrayR_sub_type_ptr_nat.
  Qed.

  Lemma _at_arrayR_sub_type_ptrR (i : Z) p xs
    (Hlen : (0 ≤ i < Z.of_nat $ length xs)%Z) :
    Observe (p .[ ty ! i ] |-> type_ptrR ty) (p |-> arrayR ty R xs).
  Proof.
    rewrite -_at_offsetL_offsetR //. by apply _at_observe, arrayR_sub_type_ptr.
  Qed.

  Lemma arrayR_sub_svalidR (i : Z) xs  :
    (0 ≤ i < Z.of_nat $ length xs)%Z →
    Observe (.[ ty ! i ] |-> svalidR) (arrayR ty R xs).
  Proof. intros. rewrite -type_ptrR_svalidR. exact: arrayR_sub_type_ptr. Qed.

  Lemma arrayR_sub_validR (i : Z) xs :
    (0 ≤ i < Z.of_nat $ length xs)%Z →
    Observe (.[ ty ! i ] |-> validR) (arrayR ty R xs).
  Proof. intros. rewrite -svalidR_validR. exact: arrayR_sub_svalidR. Qed.

  (* Unlike [arrayR_type_ptr], we get past-the-end validity, but only for lists of length >= 1. *)
  Lemma arrayR_valid i xs
    (Hlen : 1 <= length xs)
    (Hi : i ≤ length xs) :
    Observe (.[ ty ! i ] |-> validR) (arrayR ty R xs).
  Proof.
    apply: observe_intro_persistent.
    set j := pred i.
    have Hj : j < length xs by simpl; lia.
    rewrite (arrayR_sub_type_ptr j) //; try lia; subst j.
    apply Rep_entails_at => p. rewrite _at_pers.
    iIntros "#H".
    case: i Hi Hj => [|i] /= Hi Him; first
      by rewrite type_ptrR_validR.
    rewrite type_ptrR_validR_plus_one.
    rewrite !_at_offsetL_offsetR o_sub_sub_nneg; try lia.
    by rewrite comm_L Z.add_1_l Nat2Z.inj_succ.
  Qed.

  Lemma _at_arrayR_valid i xs p
    (Hlen : 1 <= length xs)
    (Hi : i ≤ length xs) :
    Observe (p .[ ty ! i ] |-> validR) (p |-> arrayR ty R xs).
  Proof.
    rewrite -_at_offsetL_offsetR.
    by apply _at_observe, arrayR_valid.
  Qed.

  (** Closer to [array'_valid] *)
  Lemma _at_arrayR_valid' i xs p
    (Hlen : 1 <= length xs)
    (Hi : i ≤ length xs) :
    p |-> arrayR ty R xs -|-
    p |-> arrayR ty R xs ** p .[ ty ! i ] |-> validR.
  Proof.
    split'; last exact: bi.sep_elim_l.
    by apply observe_elim, _at_arrayR_valid.
  Qed.

  (* TODO: backfill versions of the following using Observe and on Reps. *)

  (** Compared to [array'_split] this is a bientailment and does not need an index *)
  Lemma _at_arrayR_app' xs ys base :
    arrayR ty R (xs ++ ys) base -|-
    arrayR ty R xs base **
    arrayR ty R ys (base .[ ty ! length xs ]).
  Proof.
    elim: xs ys base => [ |x xs IH] ys base /=.
    - by rewrite o_sub_0 // offset_ptr_id arrayR_nil monPred_at_emp left_id.
    - rewrite !arrayR_cons.
      rewrite !monPred_at_sep -!assoc !monPred_at_offsetR.
      rewrite IH.
      rewrite o_sub_sub_nneg // ?Z.add_1_l ?Nat2Z.inj_succ //.
      lia.
  Qed.

  (** Compared to [array'_split], this takes [i] as first *)
  Lemma _at_arrayR_split i xs base :
    i ≤ length xs →
    arrayR ty R xs base |--
    arrayR ty R (take i xs) base **
    arrayR ty R (drop i xs) (base .[ ty ! i ]).
  Proof.
    intros. by rewrite -{1}(take_drop i xs) _at_arrayR_app' take_length_le.
  Qed.
  (** Compared to [array'_combine], this takes [i] is first *)
  Lemma _at_arrayR_combine i xs base :
    arrayR ty R (take i xs) base **
    arrayR ty R (drop i xs) (base .[ ty ! i ]) |--
    arrayR ty R xs base.
  Proof.
    rewrite -{3}(take_drop i xs). destruct (Nat.le_gt_cases i (length xs)).
    - by rewrite -{3}(take_length_le xs i)// -_at_arrayR_app'.
    - rewrite take_ge ?drop_ge /=; [ |lia|lia].
      by rewrite right_id_L bi.sep_elim_l.
  Qed.

  (* Lemma arrayR_nil {A} ty (R : A → Rep) :
    arrayR ty R [] -|- ∃ sz, [| size_of resolve ty = Some sz |] ** validR.
  Proof.
    constructor=>base /=. rewrite monPred_at_exist. f_equiv=>sz.
    by rewrite monPred_at_sep monPred_at_only_provable.
  Qed. *)

  (** Compared to [arrayR_split], [arrayR_combine], this is a
  bientailment, it omits locations and indices, and it does not
  specialize to take/drop. *)
  Lemma _at_arrayR_app'' xs ys :
    arrayR ty R (xs ++ ys) -|-
    arrayR ty R xs ** .[ ty ! length xs ] |-> arrayR ty R ys.
  Proof.
    constructor=>base /=. rewrite monPred_at_sep monPred_at_offsetR /=.
    apply _at_arrayR_app'.
  Qed.

(*
  (** Compare [arrayR_cell], [array_idx_with_addr] *)
  Lemma arrayR_sub {A} xs i x ty (R : A → Rep) iZ :
    (* is_Some (size_of resolve ty) →	(** PDS: This could be avoided *) *)
    iZ = Z.of_nat i →	(** Ease [eapply] *)
    xs !! i = Some x →	(** We have an [i]th element *)
    arrayR ty R xs -|-
    arrayR ty R (take i xs) **
    _sub ty iZ |-> R x **
    _sub ty (iZ + 1) |-> arrayR ty R (drop (S i) xs).
  Proof.
    intros Hi Hl. constructor=>p /=.
    rewrite !monPred_at_sep /=. rewrite !monPred_at_offsetR /=.
    split'.
    - iDestruct 1 as (sz) "[% A]".

      p .[ ty ! iZ ] |-> R x -*
      p .[ ty ! iZ + 1 ] |-> arrayR ty R (drop (S i) xs) -* Q) →
    p |-> arrayR ty R xs |-- Q.
*)
End has_size.
End array.
