(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.algebra Require Import list.
From iris.bi Require Import monpred big_op.
From iris.proofmode Require Import tactics.
From bedrock.lang Require Import prelude.numbers bi.observe.
(* From bedrock.auto Require Import cpp. *)
From bedrock.lang Require Import cpp.

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

Section simpl_never.
  Local Arguments N.mul : simpl never.
  Lemma size_of_array_1 σ ty : size_of σ (Tarray ty 1) = size_of σ ty.
  Proof. simpl. case: (size_of _ ty) => //= s. f_equiv. apply: left_id. Qed.
End simpl_never.
Local Hint Resolve size_of_array_1 : core.

(** PDS: Misplaced *)
Section big_op.
  Context `{Monoid M o}.
  Implicit Types P : M → Prop.
  Infix "`o`" := o (at level 50, left associativity).

  Section list.
    Context {A : Type}.
    Implicit Types xs : list A.
    Implicit Types f : nat → A → M.

    (** Any [P] compatible with the monoid and with [f] is compatible
        with [big_opL o f] *)
    Lemma big_opL_gen (P : M → Prop) f xs :
      P monoid_unit → (∀ x y, P x → P y → P (x `o` y)) →
      (∀ k x, xs !! k = Some x → P (f k x)) →
      P ([^o list] k↦x ∈ xs, f k x).
    Proof.
      intros ? Hop. elim: xs f => [ |x xs IH] f /= Hf; first done.
      apply Hop; first by apply Hf. apply IH=>k y Hk. by apply Hf.
    Qed.
  End list.
End big_op.

Section big_sepL.
  Context {PROP : bi} {A : Type}.
  Implicit Types xs : list A.
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
      [big_sepL_affine], the following offer [xs !! k = Some x] in
      their premisses. *)
  Lemma big_sepL_gen_timeless `{!Timeless (emp%I : PROP)} f xs :
    (∀ k x, xs !! k = Some x → Timeless (f k x)) →
    Timeless ([∗ list] k↦x ∈ xs, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
  Lemma big_sepL_gen_persistent f xs :
    (∀ k x, xs !! k = Some x → Persistent (f k x)) →
    Persistent ([∗ list] k↦x ∈ xs, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
  Lemma big_sepL_gen_affine f xs :
    (∀ k x, xs !! k = Some x → Affine (f k x)) →
    Affine ([∗ list] k↦x ∈ xs, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
End big_sepL.

(** PDS: Misplaced *)
Section offsetR.
  Context `{Σ : cpp_logic, resolve : genv}.

  Lemma monPred_at_offsetR offs R p :
    (_offsetR offs R) p -|- R (p ., offs).
  Proof. by rewrite _offsetR_eq. Qed.

  (* Lemma invalidO_False (R : Rep) : _offsetR path_pred.invalidO R -|- False%I.
  Proof.
    constructor=>p. rewrite monPred_at_pure _offsetR_eq /_offsetR_def /=.
    split'; last by apply bi.False_elim. by iDestruct 1 as (to) "[% ?]".
  Qed. *)
End offsetR.

Section sub.
  Context `{Σ : cpp_logic, resolve : genv}.

  (* Lemma _sub_ty ty1 ty2 i :
    size_of resolve ty1 = size_of resolve ty2 → _sub ty1 i = _sub ty2 i.
  Proof. intros Hsz1. rewrite _sub_eq /_sub_def. Hsz1. Qed. *)

  (* Lemma _sub_offsetO sz ty i R :
    size_of resolve ty = Some sz →
    _offsetR (_sub ty i) R = _offsetR (offsetO (i * Z.of_N sz)) R.
  Proof. intros Hsz. by rewrite _sub_eq /_sub_def Hsz comm_L. Qed. *)

  (* Lemma _sub_False ty i R :
    size_of resolve ty = None → _offsetR (_sub ty i) R -|- False%I.
  Proof.
    intros Hsz.
    rewrite  Hsz /= invalidO_False.
  Qed. *)
End sub.

Implicit Types (p : ptr) (σ : genv).

Section validR.
  Context `{Σ : cpp_logic}.

  (** PDS: Revisit and simplify [Offset2] *)
  (* Lemma _offsetR_valid (offs : Offset) (R : Rep) :
    validR |-- offs |-> R -* offs |-> validR.
  Proof.
    constructor=>p /=. rewrite monPred_at_validR monPred_at_wand.
    iIntros "#V" (? <-%ptr_rel_elim). rewrite !monPred_at_offsetR.
    rewrite monPred_at_validR. iApply (_off_valid with "[$V $O]").
  Qed. *)

  (** [validR] and [as_ Rep] *)
  (* Lemma validR_at_emp : validR -|- as_Rep (λ p, _at (_eq p) emp).
  Proof.
    constructor=>p /=. rewrite monPred_at_validR. by rewrite plogic._at_empSP.
  Qed. *)
  (* Lemma validR_at_l (R : Rep) : validR ** R -|- as_Rep (λ p, p |-> R).
  Proof.
    rewrite validR_at_emp. constructor=>p/=. rewrite monPred_at_sep/=.
    rewrite !plogic._at_eq_any. by rewrite monPred_at_emp left_id comm.
  Qed.
  Lemma validR_at_r (R : Rep) : R ** validR -|- as_Rep (λ p, p |-> R).
  Proof. by rewrite comm validR_at_l. Qed. *)

  (* Lemma validR_at_offsetR (offs : Offset) (R : Rep) :
    validR ** offs |-> R -|- as_Rep (λ p, p |-> offs |-> R).
  Proof. by rewrite validR_at_l. Qed. *)

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
  Lemma _at_type_ptrR ty σ p : p |-> type_ptrR ty -|- type_ptr ty p.
  Proof. by rewrite _at_eq type_ptrR_eq. Qed.

  Lemma type_ptrR_validR_plus_one (ty : type) σ :
    type_ptrR ty ⊢@{RepI (Σ := Σ)} (.[ ty ! 1 ]) |-> validR .
  Proof.
    constructor => p.
    rewrite monPred_at_offsetR monPred_at_type_ptrR monPred_at_validR.
    exact: type_ptr_valid_plus_one.
  Qed.

  (** [validR] and [_at] *)

  Lemma _sub_inv ty i resolve :
    _offsetR (_sub ty i) validR |-- [| is_Some (size_of resolve ty) |].
  Proof.
    constructor => p.
    rewrite monPred_at_offsetR monPred_at_validR monPred_at_only_provable.
    apply valid_o_sub_size.
  Qed.

  (* Lemma _at_validR_r p (R : Rep) : p |-> (R ** validR) -|- p |-> R.
  Proof. by rewrite _at_sep _at_validR -_at_valid_loc. Qed.
  Lemma _at_validR_l p (R : Rep) : p |-> (validR ** R) -|- p |-> R.
  Proof. by rewrite comm _at_validR_r. Qed. *)

  Lemma _at_offsetR_validR p (offs : offset) :
    _at p (_offsetR offs validR) -|- valid_ptr (_offset_ptr p offs).
  Proof. by rewrite _at_offsetL_offsetR _at_validR. Qed.

  (** [validR] and [offsetO] *)
  (** For better or worse, [offsetO] bakes in validity *)
  (** PDS: This is questionable. *)
  (* Lemma _offsetO_validR i R :
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
  Qed. *)
  (* Lemma _offsetO_add R a b :
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
  Qed. *)

  (** [_dot] does not imply validity *)
  (** [_offsetR invalidO] is False, and so does imply validity *)
  (** The following wrap [offsetO] or [invalidO] and so imply validity *)
  (** [_sub_def], [_field_def], [_base_def], [_super := _base],
      [_derived_def], [offset_for] *)

  (** [validR] and [_sub] *)
  (** For better or worse, [_sub] bakes in validity *)
  (* Lemma sub_validR_emp {resolve : genv} ty i :
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
  Proof. by rewrite comm sub_validR_r. Qed. *)

  Lemma _sub_0 {resolve : genv} ty R :
    is_Some (size_of resolve ty) ->
    _offsetR (_sub ty 0) R -|- R.
  Proof.
    constructor=>/= p.
    by rewrite monPred_at_offsetR /= o_sub_0 // offset_ptr_id.
  Qed.

  (* PG: Misplaced *)
  Lemma Rep_at_wand_iff (P Q : Rep) p :
    (P ∗-∗ Q) p ⊣⊢ (P p ∗-∗ Q p).
  Proof. by rewrite /bi_wand_iff monPred_at_and !Rep_wand_force. Qed.

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

  (* PG : misplaced *)
  Lemma _offsetR_emp o : _offsetR o emp ⊣⊢ emp.
  Proof.
    rewrite _offsetR_eq /_offsetR_def.
    constructor=>/= p.
    by rewrite !monPred_at_emp.
  Qed.
  (* From plogic, misplaced. *)
  Lemma _offsetR_id (R : Rep) :
      _offsetR o_id R -|- R.
  Proof.
    rewrite _offsetR_eq /_offsetR_def.
    constructor=>/= p.
    by rewrite offset_ptr_id.
  Qed.

  Lemma big_sepL_offsetR_add (f g : nat -> Z) ty (Rs : list Rep) (h : Rep -> Rep) :
    ([∗ list] i ↦ Ri ∈ Rs, .[ ty ! f i + g i ] |-> h Ri) ⊣⊢
    [∗ list] i ↦ Ri ∈ Rs, .[ ty ! f i ] |-> .[ ty ! g i ] |-> h Ri.
  Proof.
    elim: Rs => /= [//|R' Rs IHRs].
    (* constructor=> p/=.
    rewrite _offsetR_eq /_offsetR_def /=.
    rewrite !monPred_at_sep /=. *)
    f_equiv.
    iIntros.
    (* TODO: observe that the whole range is valid. and restrict f and g. *)
    iApply _sub_offsetR_add.
    admit.
    (* iApply "H". *)
    (* rewrite (_offsetR_sep _). (bi_sep _ _)). *)
  Admitted.


  Lemma arrR_cons ty R Rs :
    is_Some (size_of σ ty) →
    arrR ty (R :: Rs) -|- type_ptrR ty ** R ** _offsetR (_sub ty 1) (arrR ty Rs).
  Proof.
    intros. rewrite arrR_eq /arrR_def /=.
    rewrite _offsetR_sep !_sub_0 // (assoc bi_sep); f_equiv.
    setoid_rewrite Nat2Z.inj_succ; setoid_rewrite <-Z.add_1_l.
    rewrite big_sepL_offsetR_add.
    elim: Rs => /= [|R' Rs IHRs]; first by rewrite _offsetR_emp.
    (* rewrite !right_id o_sub_0 //. *)
    (* rewrite _offsetR_id.
    rewrite (_offsetR_sep _ (bi_sep _ _)).
    f_equiv.
    rewrite -IHRs.
    split'.
    - iIntros "E".
    iDestruct (_sub_offsetR_add with "[] E") as "H".
    _offsetR *)
  Admitted.

  Lemma arrR_inv ty R Rs : arrR ty (R :: Rs) |-- [| is_Some (size_of σ ty) |].
  Proof.
    rewrite arrR_eq /arrR_def.
    (* iIntros "[% ?]". iPureIntro. case_match. by eexists. done. *)
  Admitted.


  (* .[ ty ! 1] |-> endR (Tarray ty (N.of_nat (length Rs))) **
  .[ ty ! 1] |-> ([∗ list] i↦R0 ∈ Rs, .[ ty ! Z.of_nat i] |-> R0) *)
  Lemma arrR_singleton ty R
    (Hsz : is_Some (size_of σ ty)) :
    arrR ty [R] -|-
    type_ptrR ty ** R.
  Proof. by rewrite arrR_eq /arrR_def /= right_id _offsetR_sep !_sub_0. Qed.
End arrR.

Section array.
  Context `{Σ : cpp_logic, resolve : genv}.

  Lemma arrayR_sub_type_ptr {A} p ty (R : A → Rep) l (i : Z) :
    (0 ≤ i < Z.of_nat $ length l)%Z →
    Observe (type_ptr ty (p .[ ty ! i ])) (p |-> arrayR ty R l).
  Proof.
    intros []. set P := _at _ _. set Q := type_ptr _ _. suff Hsuff : P |-- Q.
    { rewrite /P/Q. rewrite /Observe. iIntros "A".
      iDestruct (Hsuff with "A") as "#$". }
    rewrite/P/Q {P Q}. iIntros "A". rewrite arrayR_eq /arrayR_def.
  Admitted.

  Lemma arrayR_sub_svalid {A} p ty (R : A → Rep) l (i : Z) :
    (0 ≤ i < Z.of_nat $ length l)%Z →
    Observe (strict_valid_ptr (p .[ ty ! i ])) (p |-> arrayR ty R l).
  Proof. intros. rewrite -type_ptr_strict_valid. exact: arrayR_sub_type_ptr. Qed.

  Lemma arrayR_sub_valid {A} p ty (R : A → Rep) l (i : Z) :
    (0 ≤ i < Z.of_nat $ length l)%Z →
    Observe (valid_ptr (p .[ ty ! i ])) (p |-> arrayR ty R l).
  Proof. intros. rewrite -strict_valid_relaxed. exact: arrayR_sub_svalid. Qed.

Section nested.
  Context {X : Type} (R : X -> Rep) (T : type).

  Lemma arrayR_nil : arrayR T R [] -|- emp.
  Proof. by rewrite arrayR_eq /arrayR_def arrR_nil. Qed.

  Section has_size.
  (** Compared to [array'_valid], this is a bientailment *)
    Context (Hsz : is_Some (size_of resolve T)).
    Set Default Proof Using "Hsz".

    Lemma arrayR_cons x xs :
      arrayR T R (x :: xs) -|- type_ptrR T ** R x ** _offsetR (.[ T ! 1 ]) (arrayR T R xs).
    Proof. rewrite arrayR_eq. exact: arrR_cons. Qed.

  Lemma arrayR_valid i xs base :
    i ≤ length xs →
    arrayR T R xs base -|-
    arrayR T R xs base ** valid_ptr (base .[ T ! i ]).
  Proof. Admitted.

  (** Nothing to compare to *)
  (* Lemma arrayR_cons x xs base :
    arrayR T R (x :: xs) base -|-
    base |-> R x ** arrayR T R xs (base .[T ! 1]).
  Proof. Admitted. *)
  (** Compared to [array'_split] this is a bientailment and does not need an index *)

  Lemma arrayR_app xs ys base :
    arrayR T R (xs ++ ys) base -|-
    arrayR T R xs base **
    arrayR T R ys (base .[ T ! length xs ]).
  Proof using Hsz.
    elim: xs ys base => [ |x xs IH] ys base /=.
    - by rewrite o_sub_0 // offset_ptr_id arrayR_nil monPred_at_emp left_id.
    - rewrite !arrayR_cons.
      rewrite !monPred_at_sep -!assoc !monPred_at_offsetR.
      rewrite IH.
      rewrite o_sub_sub_nneg /id // ?Z.add_1_l ?Nat2Z.inj_succ //.
      lia.
  Qed.

  (** Compared to [array'_split], this takes [i] as first *)
  Lemma arrayR_split i xs base :
    i ≤ length xs →
    arrayR T R xs base |--
    arrayR T R (take i xs) base **
    arrayR T R (drop i xs) (base .[ T ! i ]).
  Proof.
    intros. by rewrite -{1}(take_drop i xs) arrayR_app take_length_le.
  Qed.
  (** Compared to [array'_combine], this takes [i] is first *)
  Lemma arrayR_combine i xs base :
    arrayR T R (take i xs) base **
    arrayR T R (drop i xs) (base .[ T ! i ]) |--
    arrayR T R xs base.
  Proof.
    rewrite -{3}(take_drop i xs). destruct (Nat.le_gt_cases i (length xs)).
    - by rewrite -{3}(take_length_le xs i)// -arrayR_app.
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
  Lemma arrayR_app' l k :
    arrayR T R (l ++ k) -|-
    arrayR T R l ** .[ T ! length l ] |-> arrayR T R k.
  Proof.
    constructor=>base /=. rewrite monPred_at_sep monPred_at_offsetR /=.
    apply arrayR_app.
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





      p .[ ty ! iZ ] |-> R x -*
      p .[ ty ! iZ + 1 ] |-> arrayR ty R (drop (S i) l) -* Q) →
    p |-> arrayR ty R l |-- Q.
*)
End array.
