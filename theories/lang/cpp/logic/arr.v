(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.algebra Require Import list.
From iris.bi Require Import monpred big_op.
From NOVA.cpp Require Import observe numbers.
From bedrock.auto Require Import cpp.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Local Set Printing Coercions.	(** Readability *)

(** PDS: Mispalced *)
Arguments N.of_nat _ : simpl never.
Arguments N.to_nat _ : simpl never.

Local Arguments _offsetR {_ _} _ _%bi_scope.

Lemma size_of_array_0_Some σ ty :
  is_Some (size_of σ ty) → size_of σ (Tarray ty 0) = Some 0%N.
Proof. by move=>[]sz /= ->. Qed.
Local Hint Resolve size_of_array_0_Some : core.
Lemma size_of_array_0_None σ ty :
  size_of σ ty = None → size_of σ (Tarray ty 0) = None.
Proof. by move=>/= ->. Qed.
Local Hint Resolve size_of_array_0_None : core.

Lemma size_of_array_1 σ ty : size_of σ (Tarray ty 1) = size_of σ ty.
Proof. simpl. case_match; last done. f_equal. destruct n; lia. Qed.
Local Hint Resolve size_of_array_1 : core.

(** PDS: Misplaced *)
Section big_op.
  Context `{Monoid M o}.
  Implicit Types P : M → Prop.
  Infix "`o`" := o (at level 50, left associativity).

  Section list.
    Context {A : Type}.
    Implicit Types l : list A.
    Implicit Types f : nat → A → M.

    (** Any [P] compatible with the monoid and with [f] is compatible
        with [big_opL o f] *)
    Lemma big_opL_gen (P : M → Prop) f l :
      P monoid_unit → (∀ x y, P x → P y → P (x `o` y)) →
      (∀ k x, l !! k = Some x → P (f k x)) →
      P ([^o list] k↦x ∈ l, f k x).
    Proof.
      intros ? Hop. elim: l f => [ |x l IH] f /= Hf; first done.
      apply Hop; first by apply Hf. apply IH=>k y Hk. by apply Hf.
    Qed.
  End list.
End big_op.

Section big_sepL.
  Context {PROP : bi} {A : Type}.
  Implicit Types l : list A.
  Implicit Types f g : nat → A → PROP.

  (** In contrast with [big_sepL_ne], the lists need not be equal. *)
  Lemma big_sepL_gen_ne f g l1 l2 n :
    length l1 = length l2 →
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → f k y1 ≡{n}≡ g k y2) →
    ([∗ list] k↦y ∈ l1, f k y)%I ≡{n}≡ ([∗ list] k↦y ∈ l2, g k y)%I.
  Proof.
    intros ? Hf. apply big_opL_gen_proper_2; [done|by apply _| ].
    move=>k. destruct (l1 !! k) eqn:Hl1, (l2 !! k) eqn:Hl2.
    - exact: Hf.
    - apply lookup_lt_Some in Hl1. apply lookup_ge_None_1 in Hl2. lia.
    - apply lookup_ge_None_1 in Hl1. apply lookup_lt_Some in Hl2. lia.
    - done.
  Qed.

  (** In contrast with [big_sepL_proper], the lists need not be equal. *)
  Lemma big_sepL_gen_proper `{!Equiv A} f g l1 l2 :
    length l1 = length l2 →
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → f k y1 ≡ g k y2) →
    ([∗ list] k↦y ∈ l1, f k y)%I ≡ ([∗ list] k↦y ∈ l2, g k y)%I.
  Proof.
    intros ? Hf. apply big_opL_gen_proper_2; [done|by apply _| ].
    move=>k. destruct (l1 !! k) eqn:Hl1, (l2 !! k) eqn:Hl2.
    - exact: Hf.
    - apply lookup_lt_Some in Hl1. apply lookup_ge_None_1 in Hl2. lia.
    - apply lookup_ge_None_1 in Hl1. apply lookup_lt_Some in Hl2. lia.
    - done.
  Qed.

  (** In contrast with [big_sepL_timeless], [big_sepL_persistent], and
      [big_sepL_affine], the following offer [l !! k = Some x] in
      their premisses. *)
  Lemma big_sepL_gen_timeless `{!Timeless (emp%I : PROP)} f l :
    (∀ k x, l !! k = Some x → Timeless (f k x)) →
    Timeless ([∗ list] k↦x ∈ l, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
  Lemma big_sepL_gen_persistent f l :
    (∀ k x, l !! k = Some x → Persistent (f k x)) →
    Persistent ([∗ list] k↦x ∈ l, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
  Lemma big_sepL_gen_affine f l :
    (∀ k x, l !! k = Some x → Affine (f k x)) →
    Affine ([∗ list] k↦x ∈ l, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
End big_sepL.

(** PDS: Misplaced *)
Section offsetR.
  Context `{Σ : cpp_logic, resolve : genv}.

  Lemma monPred_at_offsetR offs R p :
    (_offsetR offs R) p -|- Exists to, _offset offs p to ** R to.
  Proof. by rewrite _offsetR_eq. Qed.

  Lemma invalidO_False (R : Rep) : _offsetR path_pred.invalidO R -|- False%I.
  Proof.
    constructor=>p. rewrite monPred_at_pure _offsetR_eq /_offsetR_def /=.
    split'; last by apply bi.False_elim. by iDestruct 1 as (to) "[% ?]".
  Qed.
End offsetR.

Section sub.
  Context `{Σ : cpp_logic, resolve : genv}.

  Lemma _sub_ty ty1 ty2 i :
    size_of resolve ty1 = size_of resolve ty2 → _sub ty1 i = _sub ty2 i.
  Proof. intros Hsz1. by rewrite _sub_eq /_sub_def Hsz1. Qed.

  Lemma _sub_offsetO sz ty i R :
    size_of resolve ty = Some sz →
    _offsetR (_sub ty i) R = _offsetR (offsetO (i * Z.of_N sz)) R.
  Proof. intros Hsz. by rewrite _sub_eq /_sub_def Hsz comm_L. Qed.
  Lemma _sub_False ty i R :
    size_of resolve ty = None → _offsetR (_sub ty i) R -|- False%I.
  Proof.
    intros Hsz. by rewrite _sub_eq /_sub_def Hsz /= invalidO_False.
  Qed.
  Lemma _sub_inv ty i (R : Rep) :
    _offsetR (_sub ty i) R |-- [| is_Some (size_of resolve ty) |].
  Proof.
    destruct (size_of resolve ty) eqn:Hsz.
    - iIntros "?". iPureIntro. by eexists.
    - by rewrite _sub_False// bi.False_elim.
  Qed.
End sub.

(** Represents knowledge of a valid pointer *)
Definition validR_def `{Σ : cpp_logic} : Rep := as_Rep (λ this, valid_ptr this).
Definition validR_aux : seal (@validR_def). Proof. by eexists. Qed.
Definition validR := validR_aux.(unseal).
Definition validR_eq : @validR = _ := validR_aux.(seal_eq).
Arguments validR {_ _} : assert.
Section validR.
  Context `{Σ : cpp_logic}.

  Global Instance validR_timeless : Timeless validR.
  Proof. rewrite validR_eq. apply _. Qed.
  Global Instance validR_persistent : Persistent validR.
  Proof. rewrite validR_eq. apply _. Qed.
  Global Instance validR_affine : Affine validR.
  Proof. rewrite validR_eq. apply _. Qed.

  Lemma monPred_at_validR (p : ptr) : validR p -|- valid_ptr p.
  Proof. by rewrite validR_eq. Qed.

  (** PDS: Revisit and simplify [Offset2] *)
  Lemma _offsetR_valid (offs : Offset) (R : Rep) :
    validR |-- offs |-> R -* offs |-> validR.
  Proof.
    constructor=>p /=. rewrite monPred_at_validR monPred_at_wand.
    iIntros "#V" (? <-%ptr_rel_elim). rewrite !monPred_at_offsetR.
    iDestruct 1 as (to) "[#O R]". iExists to. iFrame "O".
    rewrite monPred_at_validR. iApply (_off_valid with "[$V $O]").
  Qed.

  (** [validR] and [as_ Rep] *)
  Lemma validR_at_emp : validR -|- as_Rep (λ p, _at (_eq p) emp).
  Proof.
    constructor=>p /=. rewrite monPred_at_validR. by rewrite plogic._at_empSP.
  Qed.
  Lemma validR_at_l (R : Rep) : validR ** R -|- as_Rep (λ p, p |-> R).
  Proof.
    rewrite validR_at_emp. constructor=>p/=. rewrite monPred_at_sep/=.
    rewrite !plogic._at_eq_any. by rewrite monPred_at_emp left_id comm.
  Qed.
  Lemma validR_at_r (R : Rep) : R ** validR -|- as_Rep (λ p, p |-> R).
  Proof. by rewrite comm validR_at_l. Qed.

  Lemma validR_at_offsetR (offs : Offset) (R : Rep) :
    validR ** offs |-> R -|- as_Rep (λ p, p |-> offs |-> R).
  Proof. by rewrite validR_at_l. Qed.

  (** [validR] and [_at] *)
  Lemma _at_validR (loc : Loc) : loc |-> validR -|- valid_loc loc.
  Proof.
    rewrite validR_at_emp ptr2loc_ho.as_Rep_at_eq _at_emp.
    by rewrite -bi.persistent_sep_dup.
  Qed.
  Lemma _at_validR_r (loc : Loc) (R : Rep) : loc |-> (R ** validR) -|- loc |-> R.
  Proof. by rewrite _at_sep _at_validR -_at_valid_loc. Qed.
  Lemma _at_validR_l (loc : Loc) (R : Rep) : loc |-> (validR ** R) -|- loc |-> R.
  Proof. by rewrite comm _at_validR_r. Qed.

  Lemma _at_offsetR_validR (loc : Loc) (offs : Offset) :
    _at loc (_offsetR offs validR) -|- valid_loc (_offsetL offs loc).
  Proof. by rewrite _at_offsetL_offsetR _at_validR. Qed.

  (** [validR] and [offsetO] *)
  (** For better or worse, [offsetO] bakes in validity *)
  (** PDS: This is questionable. *)
  Lemma _offsetO_validR i R :
    _offsetR (offsetO i) R |-- _offsetR (offsetO i) validR.
  Proof.
    constructor=>p /=. rewrite !monPred_at_offsetR /offsetO/=.
    setoid_rewrite monPred_at_validR. f_equiv=>to. by iIntros "[[$ #$] ?]".
  Qed.
  Lemma _offsetO_validR_emp i :
    _offsetR (offsetO i) validR -|- _offsetR (offsetO i) emp.
  Proof.
    constructor=>p /=. rewrite !monPred_at_offsetR /offsetO/=.
    setoid_rewrite monPred_at_emp. setoid_rewrite monPred_at_validR.
    f_equiv=>to. by rewrite right_id -assoc -bi.persistent_sep_dup.
  Qed.
  Lemma _offsetO_validR_r i (R : Rep) :
    _offsetR (offsetO i) (R ** validR) -|- _offsetR (offsetO i) R.
  Proof.
    by rewrite _offsetR_sep _offsetO_validR_emp -_offsetR_sep right_id.
  Qed.
  Lemma _offsetO_validR_l i (R : Rep) :
    _offsetR (offsetO i) (validR ** R) -|- _offsetR (offsetO i) R.
  Proof. by rewrite comm _offsetO_validR_r. Qed.
  Lemma _offsetO_0 R : _offsetR (offsetO 0) R -|- validR ** R.
  Proof.
    constructor=>p /=. rewrite monPred_at_offsetR /offsetO/= offset_ptr_0_.
    rewrite monPred_at_sep monPred_at_validR. split'.
    - iDestruct 1 as (?) "[[-> $] $]".
    - iIntros "[V R]". iExists p. by iFrame "V R".
  Qed.
  Lemma _offsetO_add R a b :
    _offsetR (offsetO a) emp **	(** PDS: This is unfortunate *)
    _offsetR (offsetO (a + b)) R -|-
    _offsetR (offsetO a) (_offsetR (offsetO b) R).
  Proof.
    constructor=>p /=. rewrite monPred_at_sep !monPred_at_offsetR.
    setoid_rewrite monPred_at_offsetR.
    rewrite /offsetO/= -offset_ptr_combine_. split'.
    - iDestruct 1 as "[A R]". iDestruct "A" as (?) "[[-> VA] _]".
      iExists _. by iFrame "R VA".
    - iDestruct 1 as (?) "[[-> VA] R]". iFrame "R". iExists _. by iFrame "VA".
  Qed.

  (** [_dot] does not imply validity *)
  (** [_offsetR invalidO] is False, and so does imply validity *)
  (** The following wrap [offsetO] or [invalidO] and so imply validity *)
  (** [_sub_def], [_field_def], [_base_def], [_super := _base],
      [_derived_def], [offset_for] *)

  (** [validR] and [_sub] *)
  (** For better or worse, [_sub] bakes in validity *)
  Lemma sub_validR_emp {resolve : genv} ty i :
    _offsetR (_sub ty i) validR -|- _offsetR (_sub ty i) emp.
  Proof.
    destruct (size_of resolve ty) as [sz| ] eqn:Hsz.
    - by rewrite !(_sub_offsetO sz)// _offsetO_validR_emp.
    - by rewrite !_sub_False.
  Qed.
  Lemma sub_validR_r {resolve : genv} ty i (R : Rep) :
    _offsetR (_sub ty i) (R ** validR) -|- _offsetR (_sub ty i) R.
  Proof.
    by rewrite _offsetR_sep sub_validR_emp -_offsetR_sep right_id.
  Qed.
  Lemma sub_validR_l {resolve : genv} ty i (R : Rep) :
    _offsetR (_sub ty i) (validR ** R) -|- _offsetR (_sub ty i) R.
  Proof. by rewrite comm sub_validR_r. Qed.

  Lemma _sub_0_1 {resolve : genv} ty R :
    _offsetR (_sub ty 0) R |-- validR ** R.
  Proof.
    destruct (size_of resolve ty) as [sz| ] eqn:Hsz.
    - by rewrite (_sub_offsetO sz)// left_absorb_L _offsetO_0.
    - by rewrite _sub_False// bi.False_elim.
  Qed.
  Lemma _sub_0_2 {resolve} ty R :
    is_Some (size_of resolve ty) → validR ** R |-- _offsetR (_sub ty 0) R.
  Proof. intros [sz ?]. by rewrite (_sub_offsetO sz)// _offsetO_0. Qed.
  Lemma _sub_0 {resolve} ty R :
    is_Some (size_of resolve ty) → _offsetR (_sub ty 0) R -|- validR ** R.
  Proof. split'; auto using _sub_0_1, _sub_0_2. Qed.

  Lemma _sub_offsetO_add {resolve : genv} ty a b R :
    _offsetR (_sub ty a) emp **	(** PDS: This is unfortunate *)
    _offsetR (_sub ty (a + b)) R -|-
    _offsetR (_sub ty a) (_offsetR (_sub ty b) R).
  Proof.
    destruct (size_of resolve ty) as [sz| ] eqn:Hsz.
    - rewrite !(_sub_offsetO sz)//.
      by rewrite Z.mul_add_distr_r _offsetO_add.
    - rewrite !_sub_False//. by rewrite left_absorb.
  Qed.
End validR.

(** Validity of the pointer past the end of an object of type [ty] *)
Definition endR_def `{Σ : cpp_logic} (ty : type) {σ : genv} : Rep := 
  (*(□ (validR -* _offsetR (_sub ty 1) validR))%I.*)
  _offsetR (_sub ty 1) validR.
Definition endR_aux : seal (@endR_def). Proof. by eexists. Qed.
Definition endR := endR_aux.(unseal).
Definition endR_eq : @endR = _ := endR_aux.(seal_eq).
Arguments endR {_ _} _ {_} : assert.

Section endR.
  Context `{Σ : cpp_logic, σ : genv}.

  Global Instance endR_timeless ty : Timeless (endR ty).
  Proof. rewrite endR_eq. apply _. Qed.
  Global Instance endR_persistent ty : Persistent (endR ty).
  Proof. rewrite endR_eq. apply _. Qed.
  Global Instance endR_affine ty : Affine (endR ty).
  Proof. rewrite endR_eq. apply _. Qed.

  Lemma endR_ty ty1 ty2 : size_of σ ty1 = size_of σ ty2 → endR ty1 -|- endR ty2.
  Proof. intros. by rewrite endR_eq /endR_def (_sub_ty _ ty2). Qed.

  Lemma endR_sub ty : endR ty -|- _offsetR (_sub ty 1) validR.
  Proof. by rewrite endR_eq. Qed.

  Lemma endR_inv ty : endR ty |-- [| is_Some (size_of σ ty) |].
  Proof. by rewrite endR_sub _sub_inv. Qed.

  Lemma endR_offsetO sz ty :
    size_of σ ty = Some sz → endR ty -|- _offsetR (offsetO sz) validR.
  Proof. intros. by rewrite endR_sub (_sub_offsetO sz)// left_id_L. Qed.
  Lemma endR_False ty : size_of σ ty = None → endR ty -|- False.
  Proof. intros. by rewrite endR_sub _sub_False. Qed.
  Lemma _at_endR (loc : Loc) ty :
    loc |-> endR ty -|- valid_loc (_offsetL (_sub ty 1) loc).
  Proof. by rewrite endR_sub _at_offsetL_offsetR _at_validR. Qed.

End endR.

Definition arrR_def `{Σ : cpp_logic} (ty : type) {σ : genv} (Rs : list Rep) : Rep :=
  endR (Tarray ty $ N.of_nat $ length Rs) **
  ([∗ list] i ↦ R ∈ Rs, _offsetR (_sub ty (Z.of_nat i)) R)%I.
Definition arrR_aux : seal (@arrR_def). Proof. by eexists. Qed.
Definition arrR := arrR_aux.(unseal).
Definition arrR_eq : @arrR = _ := arrR_aux.(seal_eq).
Arguments arrR {_ _} _ {_} _%list_scope : assert.
Instance: Params (@arrR) 4 := {}.	(** TODO: [genv] weakening *)

Module Import internal.
Section internal.
  Context `{Σ : cpp_logic, σ : genv}.

  Definition altR (ty : type) (f : Z → Z) (Rs : list Rep) : Rep :=
    ([∗ list] i ↦ R ∈ Rs, _offsetR (_sub ty $ f $ Z.of_nat i) R)%I.

  _at_valid
  Offset

  Lemma arrR_alt ty Rs :
    arrR ty Rs = endR (Tarray ty $ N.of_nat $ length Rs) ** altR ty id Rs.
  Proof. by rewrite arrR_eq. Qed.

  Lemma altR_add n ty Rs :
    is_Some (size_of σ ty) →
    ([∗ list] i ∈ seq 0 n, _offsetR (_sub ty $ Z.of_nat i) validR) **
    altR ty (Z.add $ Z.of_nat n) Rs -|- _offsetR (_sub ty n) (altR ty id Rs).
  Proof.
    intros [sz Hsz].
    rewrite/altR. elim: Rs n => [ |R Rs IH] n /=.
    - rewrite (_sub_offsetO sz)//.
      constructor=>p.
      rewrite monPred_at_emp monPred_at_offsetR.
      rewrite _sub_eq /_sub_def.
      setoid_rewrite monPred_at_sub.


    ([∗ list] i ↦ R ∈ Rs, _offsetR (_sub ty (base + Z.of_nat i)) R) -|-
    _offsetR (_sub ty base) (arrR' ty Rs).
    
  .[ ty ! 1] |-> ([∗ list] i↦R0 ∈ Rs, .[ ty ! Z.of_nat i] |-> R0)

End internal.
End internal.

Section arrR.
  Context `{Σ : cpp_logic, σ : genv}.

  Global Instance arrR_ne ty : NonExpansive (arrR ty).
  Proof.
    intros n l1 l2 Hl. rewrite arrR_eq /arrR_def.
    have Hlen := Forall2_length _ _ _ Hl.
    apply bi.sep_ne; first by rewrite Hlen.
    apply big_sepL_gen_ne; first done.
    move=>k y1 y2 Hl1 Hl2. apply _offsetR_ne, (inj Some).
    rewrite -Hl1 -Hl2. by apply list_dist_lookup.
  Qed.
  Global Instance arrR_proper ty : Proper ((≡) ==> (≡)) (arrR ty).
  Proof.
    intros l1 l2 Hl. rewrite arrR_eq /arrR_def.
    have Hlen : length l1 = length l2 by apply (Forall2_length (≡)), equiv_Forall2.
    apply bi.sep_proper; first by rewrite Hlen.
    apply big_sepL_gen_proper; first done.
    move=>k y1 y2 Hl1 Hl2. apply _offsetR_proper, (inj Some).
    rewrite -Hl1 -Hl2. by apply list_equiv_lookup.
  Qed.
  (** We don't register this as an instance because it doesn't hold in
      arbitrary non-affine BIs. *)
  Remark arrR_timeless_when_mpred_affine ty Rs :
    TCForall Timeless Rs → Timeless (arrR ty Rs).
  Proof.
    rewrite TCForall_Forall Forall_forall=>HR. rewrite arrR_eq /arrR_def.
    apply bi.sep_timeless; first by apply _.
    apply big_sepL_gen_timeless=>k x Hk.
    apply _offsetR_timeless, HR. exact: elem_of_list_lookup_2.
  Qed.
  Global Instance arrR_persistent ty Rs :
    TCForall Persistent Rs → Persistent (arrR ty Rs).
  Proof.
    rewrite TCForall_Forall Forall_forall=>HR. rewrite arrR_eq /arrR_def.
    apply bi.sep_persistent; first by apply _.
    apply big_sepL_gen_persistent=>k x Hk.
    apply _offsetR_persistent, HR. exact: elem_of_list_lookup_2.
  Qed.
  Global Instance arrR_affine ty Rs :
    TCForall Affine Rs → Affine (arrR ty Rs).
  Proof.
    rewrite TCForall_Forall Forall_forall=>HR. rewrite arrR_eq /arrR_def.
    apply bi.sep_affine; first by apply _.
    apply big_sepL_gen_affine=>k x Hk.
    apply _offsetR_affine, HR. exact: elem_of_list_lookup_2.
  Qed.

  Lemma arrR_inv ty Rs : arrR ty Rs |-- [| is_Some (size_of σ ty) |].
  Proof.
    rewrite arrR_eq /arrR_def. rewrite endR_inv/=.
    iIntros "[% ?]". iPureIntro. case_match. by eexists. done.
  Qed.

  Lemma arrR_nil ty : is_Some (size_of σ ty) → arrR ty nil -|- validR.
  Proof.
    intros ?%size_of_array_0_Some. rewrite arrR_eq /arrR_def /= right_id.
    by rewrite (endR_offsetO 0)// _offsetO_0 -bi.persistent_sep_dup.
  Qed.

  Lemma arrR_cons ty R Rs :
    is_Some (size_of σ ty) →
    arrR ty (R :: Rs) -|- validR ** R ** _offsetR (_sub ty 1) (arrR ty Rs).
  Proof.
    intros. rewrite arrR_eq /arrR_def/=.
    rewrite _offsetR_sep _sub_0//. split'.
    - iIntros "(E & [$ $] & Rs)".
      rewrite Nat2N.inj_succ -N.add_1_r.
      setoid_rewrite Nat2Z.inj_succ; setoid_rewrite <-Z.add_1_r.

  .[ ty ! 1] |-> endR (Tarray ty (N.of_nat (length Rs))) **
  .[ ty ! 1] |-> ([∗ list] i↦R0 ∈ Rs, .[ ty ! Z.of_nat i] |-> R0)
  Lemma arrR_singleton_cases ty R :
    arrR ty [R] -|-
    endR ty **
    if size_of σ ty is Some _
    then validR ** R
    else False.
  Proof.
    rewrite arrR_eq/arrR_def /=. rewrite right_id.
    rewrite (endR_ty (Tarray ty 1) ty)//. f_equiv.
    rewrite _sub_cases. case_match.
    - by rewrite left_absorb_L _offsetO_0.
    - by rewrite invalidO_False.
  Qed.
  Lemma arrR_singleton ty R sz :
    size_of σ ty = Some sz →
    arrR ty [R] -|- endR ty ** validR ** R.
  Proof. intros Hty. by rewrite arrR_singleton_cases Hty. Qed.
End arrR.

Section array.
  Local Transparent arrayR.
  Context `{Σ : cpp_logic, resolve : genv}.

  Lemma arrayR_sub_valid {A} (loc : Loc) ty (R : A → Rep) l (i : Z) :
    (0 ≤ i < Z.of_nat $ length l)%Z →
    Observe (valid_loc (loc .[ ty ! i ])) (loc |-> arrayR ty R l).
  Proof.
    intros []. set P := _at _ _. set Q := valid_loc _. suff Hsuff : P |-- Q.
    { rewrite /P/Q. rewrite /Observe. iIntros "A".
      iDestruct (Hsuff with "A") as "#$". iFrame "A". }
    rewrite/P/Q {P Q}. iIntros "A". rewrite /arrayR plogic._at_as_Rep.
    iDestruct "A" as (p) "[#Addr A]". iDestruct "A" as (sz) "[% A]".
    iDestruct (array'_valid _ _ _ _ _ (Z.to_nat i) with "A") as "[A #V]";
      first lia.
    rewrite Z2Nat.id//. set pi := offset_ptr_ _ _.
    rewrite (sub_offsetO sz)// valid_loc_equiv. iExists pi.
    rewrite addr_of_eq /addr_of_def _offsetL_eq /_offsetL_def/=.
    iExists p. by iFrame "Addr V".
  Qed.

  (** Compared to [array'_valid], this is a bientailment *)
  Lemma array'_valid {A} i l sz (R : A → Rep) base :
    i ≤ length l →
    array' sz R l base -|-
    array' sz R l base ** valid_ptr (offset_ptr_ (Z.of_nat i * sz) base).
  Proof. split'. by apply array'_valid. by rewrite bi.sep_elim_l. Qed.

  (** Nothing to compare to *)
  Lemma array'_cons {A} x l sz (R : A → Rep) base :
    array' sz R (x :: l) base -|-
    base |-> R x ** array' sz R l (offset_ptr_ sz base).
  Proof. done. Qed.
  (** Compared to [array'_split] this is a bientailment and does not need an index *)
  Lemma array'_app {A} l k sz (R : A → Rep) base :
    array' sz R (l ++ k) base -|-
    array' sz R l base **
    array' sz R k (offset_ptr_ (Z.of_nat (length l) * sz) base).
  Proof.
    elim: l k base=>[ |x l IH] k base /=.
    - rewrite {1}(array'_valid 0); last lia.
      by rewrite left_absorb_L offset_ptr_0_ comm.
    - rewrite -assoc IH offset_ptr_combine_. repeat f_equiv. lia.
  Qed.
  (** Compared to [array'_split], this takes [i] is first *)
  Lemma array'_split {A} i l sz (R : A → Rep) base :
    i ≤ length l →
    array' sz R l base |--
    array' sz R (take i l) base **
    array' sz R (drop i l) (offset_ptr_ (Z.of_nat i * sz) base).
  Proof.
    intros. by rewrite -{1}(take_drop i l) array'_app take_length_le.
  Qed.
  (** Compared to [array'_combine], this takes [i] is first *)
  Lemma array'_combine {A} i l sz (R : A → Rep) base :
    array' sz R (take i l) base **
    array' sz R (drop i l) (offset_ptr_ (Z.of_nat i * sz) base) |--
    array' sz R l base.
  Proof.
    rewrite -{3}(take_drop i l). destruct (Nat.le_gt_cases i (length l)).
    - by rewrite -{3}(take_length_le l i)// -array'_app.
    - rewrite take_ge ?drop_ge /=; [ |lia|lia].
      by rewrite right_id_L bi.sep_elim_l.
  Qed.


  Lemma arrayR_nil {A} ty (R : A → Rep) :
    arrayR ty R [] -|- ∃ sz, [| size_of resolve ty = Some sz |] ** validR.
  Proof.
    constructor=>base /=. rewrite monPred_at_exist. f_equiv=>sz.
    by rewrite monPred_at_sep monPred_at_only_provable.
  Qed.

  (** Compared to [arrayR_split], [arrayR_combine], this is a
  bientailment, it omits locations and indices, and it does not
  specialize to take/drop. *)
  Lemma arrayR_app {A} l k ty (R : A → Rep) :
    arrayR ty R (l ++ k) -|-
    arrayR ty R l ** _sub ty (length l) |-> arrayR ty R k.
  Proof.
    constructor=>base /=. rewrite monPred_at_sep monPred_at_offsetR /=. split'.
    - iDestruct 1 as (sz) "[% A]".
      rewrite array'_app. iDestruct "A" as "[L K]".
      rewrite (array'_valid (length l) l)//. iDestruct "L" as "[L #V]".
      iSplitL "L"; first by iExists _; iFrame "L".
      iExists _. iSplitR "K"; last by iExists _; iFrame "K".
      by rewrite _offset_sub_1.
    - iIntros "[L O]". iDestruct "L" as (sz1) "[% L]".
      iDestruct "O" as (to) "[O K]". iDestruct "K" as (sz2) "[% K]". simplify_eq.
      iExists _. iSplitR; first done. rewrite array'_app. iFrame "L".
      rewrite _offset_sub_2//. iDestruct "O" as "[-> _]". iFrame "K".
  Qed.

(*
  (** Compare [arrayR_cell], [array_idx_with_addr] *)
  Lemma arrayR_sub {A} l i x ty (R : A → Rep) iZ :
    (* is_Some (size_of resolve ty) →	(** PDS: This could be avoided *) *)
    iZ = Z.of_nat i →	(** Ease [eapply] *)
    l !! i = Some x →	(** We have an [i]th element *)
    arrayR ty R l -|-
    arrayR ty R (take i l) **
    _sub ty iZ |-> R x **
    _sub ty (iZ + 1) |-> arrayR ty R (drop (S i) l).
  Proof.
    intros Hi Hl. constructor=>p /=.
    rewrite !monPred_at_sep /=. rewrite !monPred_at_offsetR /=.
    split'.
    - iDestruct 1 as (sz) "[% A]".
      

    
    

      loc .[ ty ! iZ ] |-> R x -*
      loc .[ ty ! iZ + 1 ] |-> arrayR ty R (drop (S i) l) -* Q) →
    loc |-> arrayR ty R l |-- Q.
*)
End array.
