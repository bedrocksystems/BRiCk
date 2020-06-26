(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Classes.Morphisms.

Require Import iris.proofmode.tactics.
From bedrock.lang.cpp Require Import semantics logic.pred ast.

Set Default Proof Using "Type".

Section with_Σ.
  Context `{has_cpp : cpp_logic}.

  (* locations are computations that produce an address.
   *)
  Record Loc : Type :=
    { _location : ptr -> mpred
    ; _loc_unique : forall p1 p2, _location p1 ** _location p2 |-- bi_pure (p1 = p2)
    ; _loc_valid : forall p1, _location p1 |-- valid_ptr p1
    ; _loc_persist : forall p, Persistent (_location p)
    ; _loc_affine : forall p, Affine (_location p)
    ; _loc_timeless : forall p, Timeless (_location p)
    }.

  Global Existing Instances _loc_persist _loc_affine _loc_timeless.

  Global Instance Loc_Equiv : Equiv Loc :=
    fun l r => forall p, @_location l p -|- @_location r p.

  Global Instance Loc_Equivalence : Equivalence (≡@{Loc}).
  Proof.
    split.
    - done.
    - do 3 red. intros. by symmetry.
    - do 3 red. intros. etrans; eauto.
  Qed.

  Global Instance _location_proper : Proper ((≡) ==> eq ==> (≡)) _location.
  Proof. repeat intro. by subst. Qed.

  (* [mpred] implication between [Loc] *)
  Definition Loc_impl (l1 l2 : Loc) : mpred :=
    □ (Forall p, l1.(_location) p -* l2.(_location) p).

  (* [mpred] equivalence of [Loc] *)
  Definition Loc_equiv (l1 l2 : Loc) : mpred :=
    □ (Forall l, (l1.(_location) l ∗-∗ l2.(_location) l)).

  Lemma Loc_equiv_impl l1 l2 :
    Loc_equiv l1 l2 -|- Loc_impl l1 l2 ** Loc_impl l2 l1.
  Proof.
    iSplit.
    - iIntros "#EQ".
      iSplit; iIntros "!>"; iIntros (p) "Hp"; iApply ("EQ" with "Hp").
    - iIntros "#[H1 H2] !>". iIntros (p).
      iSplit; iIntros "Hp"; [by iApply "H1"|by iApply "H2"].
  Qed.

  Lemma Loc_equiv_sym l1 l2 : Loc_equiv l1 l2 |-- Loc_equiv l2 l1.
  Proof.
    iIntros "#H !>". iIntros (p).
    iSplit; iIntros "Hp"; iApply ("H" with "Hp").
  Qed.

  (** absolute locations *)
  Definition invalid : Loc.
  refine {| _location _ := lfalse |}.
  abstract (intros; iIntros "[[] _]").
  abstract (intros; iIntros "[]").
  Defined.

  Definition _eq_def (p : ptr) : Loc.
  refine
    {| _location p' := [| p = p' |] ** valid_ptr p' |}.
  abstract (intros; iIntros "[[-> _] [% _]]"; iFrame "#"; eauto).
  abstract (intros; iIntros "[-> #H]"; iFrame "#").
  Defined.
  Definition _eq_aux : seal (@_eq_def). by eexists. Qed.
  Definition _eq := _eq_aux.(unseal).
  Definition _eq_eq : @_eq = _ := _eq_aux.(seal_eq).

  Definition _eqv (a : val) : Loc :=
    match a with
    | Vptr p => _eq p
    | _ => invalid
    end.

  Lemma _eqv_eq : forall p, _eqv (Vptr p) = _eq p.
  Proof. reflexivity. Qed.

  Definition _global_def (resolve : genv) (x : obj_name) : Loc :=
    match glob_addr resolve x with
    | Some p => _eq p
    | _ => invalid
    end.
  Definition _global_aux : seal (@_global_def). by eexists. Qed.
  Definition _global := _global_aux.(unseal).
  Definition _global_eq : @_global = _ := _global_aux.(seal_eq).

  Definition _local (ρ : region) (b : ident) : Loc :=
    match get_location ρ b with
    | Some p => _eq p
    | _ => invalid
    end.

  Definition _this (ρ : region) : Loc :=
    match get_this ρ with
    | Some p => _eq p
    | _ => invalid
    end.

  Definition _result (ρ : region) : Loc :=
    match get_result ρ with
    | Some p => _eq p
    | _ => invalid
    end.

  (** [addr_of] *)
  Definition addr_of_def (a : Loc) (b : ptr) : mpred :=
    a.(_location) b.
  Definition addr_of_aux : seal (@addr_of_def). by eexists. Qed.
  Definition addr_of := addr_of_aux.(unseal).
  Definition addr_of_eq : @addr_of = _ := addr_of_aux.(seal_eq).
  Arguments addr_of : simpl never.
  Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).

  Global Instance addr_of_persistent : Persistent (addr_of o l).
  Proof.
    intros. rewrite addr_of_eq /addr_of_def. apply _loc_persist.
  Qed.

  Global Instance addr_of_affine : Affine (addr_of o l).
  Proof.
    intros. rewrite addr_of_eq /addr_of_def. apply _loc_affine.
  Qed.

  Global Instance addr_of_timeless : Timeless (addr_of o l).
  Proof.
    intros. rewrite addr_of_eq /addr_of_def. apply _loc_timeless.
  Qed.

  Lemma addr_of_Loc_eq : forall l p, l &~ p |-- Loc_equiv l (_eq p).
  Proof.
    intros. rewrite /Loc_equiv addr_of_eq /addr_of_def _eq_eq /_eq_def /=.
    iIntros "#L". iIntros (ll). iModIntro.
    iSplit.
    - iIntros "#H".
      iSplit.
      { iDestruct (_loc_unique with "[L H]") as %H; [ | eauto ]; iSplit; iAssumption. }
      { iApply _loc_valid; iAssumption. }
    - iIntros "[% #H]".
      subst. iAssumption.
  Qed.

  Lemma addr_of_Loc_impl : forall l p, l &~ p |-- Loc_impl l (_eq p).
  Proof. intros. by rewrite addr_of_Loc_eq Loc_equiv_impl bi.sep_elim_l. Qed.

  Lemma addr_of_precise : forall a b c,
      addr_of a b ** addr_of a c |-- bi_pure (b = c).
  Proof.
    intros.
    rewrite addr_of_eq /addr_of_def.
    iIntros "[#A #B]".
    iFrame "#".
    iDestruct (_loc_unique with "[A B]") as %H; [ | eauto ]; eauto.
  Qed.



  (** [valid_loc]
      - same as [addr_of] except that it hides the existential quantifier
   *)
  Definition valid_loc_def (l : Loc) : mpred := Exists p, addr_of l p.
  Definition valid_loc_aux : seal (@valid_loc_def). Proof. by eexists. Qed.
  Definition valid_loc := valid_loc_aux.(unseal).
  Definition valid_loc_eq : valid_loc = @valid_loc_def := valid_loc_aux.(seal_eq).

  Global Instance valid_loc_persistent : Persistent (valid_loc l).
  Proof. rewrite valid_loc_eq /valid_loc_def; refine _. Qed.
  Global Instance valid_loc_affine : Affine (valid_loc l).
  Proof. rewrite valid_loc_eq /valid_loc_def; refine _. Qed.
  Global Instance valid_loc_timeless : Timeless (valid_loc l).
  Proof. rewrite valid_loc_eq /valid_loc_def;
         destruct l; simpl; refine _.
  Qed.


  (** offsets *)
  Record Offset : Type :=
  { _offset : ptr -> ptr -> mpred
  ; _off_functional : forall p p1 p2, _offset p p1 ** _offset p p2 |-- [| p1 = p2 |]
  ; _off_valid : forall p1 p2, valid_ptr p1 ** _offset p1 p2 |-- valid_ptr p2
  ; _off_persist :> forall p1 p2, Persistent (_offset p1 p2)
  ; _off_affine :> forall p1 p2, Affine (_offset p1 p2)
  ; _off_timeless :> forall p1 p2, Timeless (_offset p1 p2)
  }.

  Global Existing Instances _off_persist _off_affine.

  Global Instance Offset_Equiv : Equiv Offset :=
    fun l r => forall p q, @_offset l p q -|- @_offset r p q.

  Global Instance Offset_Equivalence : Equivalence (≡@{Offset}).
  Proof.
    split.
    - done.
    - do 3 red. intros. by symmetry.
    - do 3 red. intros. etrans; eauto.
  Qed.


  Local Definition invalidO : Offset.
  refine {| _offset _ _ := lfalse |}.
  abstract (intros; iIntros "[_ []]").
  abstract (intros; iIntros "[_ []]").
  Defined.

  Definition offsetO (o : Z) : Offset.
  refine {| _offset from to := [| to = offset_ptr_ o from |] ** valid_ptr to |}.
  abstract (intros; iIntros "[[#H _] [-> _]]"; iFrame "#").
  abstract (intros; iIntros "[A [B C]]"; iFrame).
  Defined.

  Definition offsetO_opt (o : option Z) : Offset :=
    match o with
    | None => invalidO
    | Some o => offsetO o
    end.

  (** the identity [Offset] *)
  Definition _id_def : Offset.
   refine {| _offset from to := [| from = to |] |}.
   abstract (intros; iIntros "[-> #H]"; iFrame "#").
   abstract (intros; iIntros "[H <-]"; iFrame).
  Defined.
  Definition _id_aux : seal (@_id_def). by eexists. Qed.
  Definition _id := _id_aux.(unseal).
  Definition _id_eq : @_id = _ := _id_aux.(seal_eq).

  (** path composition *)
  Definition _dot_def (o1 o2 : Offset) : Offset.
  refine {| _offset from to :=
              Exists mid, _offset o1 from mid ** _offset o2 mid to |}.
  { intros.
    iIntros "[H1 H2]".
    iDestruct "H1" as (m1) "[A A']".
    iDestruct "H2" as (m2) "[B B']".
    iDestruct (_off_functional with "[A B]") as %X. iFrame.
    subst.
    iDestruct ((_off_functional o2) with "[A' B']") as %Y. iFrame.
    by iPureIntro. }
  { intros.
    iIntros "[H H']".
    iDestruct "H'" as (m) "[H1 H2]".
    iApply _off_valid. iFrame.
    iApply _off_valid. iFrame. }
  { intros.
    eapply bi.exist_timeless; intros; eapply bi.sep_timeless;
      [ eapply o1 | eapply o2 ]. }
  Defined.
  Definition _dot_aux : seal (@_dot_def). by eexists. Qed.
  Definition _dot := _dot_aux.(unseal).
  Definition _dot_eq : @_dot = _ := _dot_aux.(seal_eq).


  (** access a field *)
  Definition _field_def (resolve: genv) (f : field) : Offset :=
    offsetO_opt (offset_of resolve f.(f_type) f.(f_name)).
  Definition _field_aux : seal (@_field_def). Proof using. by eexists. Qed.
  Definition _field := _field_aux.(unseal).
  Definition _field_eq : @_field = _ := _field_aux.(seal_eq).

  (** subscript an array *)
  Definition _sub_def (resolve:genv) (t : type) (i : Z) : Offset :=
    offsetO_opt (match size_of resolve t with
                 | Some o => Some (Z.of_N o * i)%Z
                 | _ => None
                 end).
  Definition _sub_aux : seal (@_sub_def). by eexists. Qed.
  Definition _sub := _sub_aux.(unseal).
  Definition _sub_eq : @_sub = _ := _sub_aux.(seal_eq).

  (** [_base derived base] is a cast from derived to base.
   *)
  Definition _base_def (resolve:genv) (derived base : globname) : Offset :=
    offsetO_opt (parent_offset resolve derived base).
  Definition _base_aux : seal (@_base_def). by eexists. Qed.
  Definition _base := _base_aux.(unseal).
  Definition _base_eq : @_base = _ := _base_aux.(seal_eq).
  Definition _super := _base.

  (** [_derived base derived] is a cast from base to derived
   *)
  Definition _derived_def (resolve:genv) (base derived : globname) : Offset :=
    offsetO_opt match parent_offset resolve derived base with
                | Some o => Some (0 - o)%Z
                | None => None
                end.
  Definition _derived_aux : seal (@_derived_def). by eexists. Qed.
  Definition _derived := _derived_aux.(unseal).
  Definition _derived_eq : @_derived = _ := _derived_aux.(seal_eq).

  (** offset from a location
   *)
  Definition _offsetL_def (o : Offset) (l : Loc) : Loc.
  refine
    {| _location p := Exists from, _offset o from p ** _location l from |}.
  { intros. iIntros "[L R]".
    iDestruct "L" as (pl) "[Lo Ll]".
    iDestruct "R" as (pr) "[Ro Rl]".
    iDestruct ((@_loc_unique l pl pr) with "[Ll Rl]") as %H; [ iFrame | subst ].
    iDestruct (_off_functional with "[Lo Ro]") as %H'; [ | eauto ]. eauto. }
  { intros.
    iIntros "H".
    iDestruct "H" as (p) "[O L]".
    iApply _off_valid. iFrame.
    iApply _loc_valid. iFrame. }
  { intros.
    eapply bi.exist_timeless; intros; eapply bi.sep_timeless;
      [ eapply o | eapply l ]. }
  Defined.
  Definition _offsetL_aux : seal (@_offsetL_def). by eexists. Qed.
  Definition _offsetL := _offsetL_aux.(unseal).
  Definition _offsetL_eq : @_offsetL = _ := _offsetL_aux.(seal_eq).

  Lemma _offsetL_dot : forall (o1 o2 : Offset) (l : Loc),
      (_offsetL o2 (_offsetL o1 l) ≡ _offsetL (_dot o1 o2) l)%stdpp.
  Proof.
    rewrite /equiv /Loc_Equiv _offsetL_eq _dot_eq. simpl.
    split'.
    { iIntros "X". iDestruct "X" as (from) "[X Y]".
      iDestruct "Y" as (from0) "[Y Z]".
      iExists from0. iFrame. iExists _. iFrame. }
    { iIntros "X". iDestruct "X" as (from) "[X Y]".
      iDestruct "X" as (from0) "[X Z]".
      iExists _. iFrame. iExists _. iFrame. }
  Qed.

  Lemma _dot_dot : forall (o1 o2 l: Offset),
      (_dot o2 (_dot o1 l) ≡ _dot (_dot o2 o1) l)%stdpp.
  Proof.
    rewrite /equiv /Offset_Equiv _dot_eq. simpl.
    split'.
    { iIntros "X". iDestruct "X" as (from) "[X Y]".
      iDestruct "Y" as (from0) "[Y Z]".
      iExists from0. iFrame. iExists _. iFrame. }
    { iIntros "X". iDestruct "X" as (from) "[X Y]".
      iDestruct "X" as (from0) "[X Z]".
      iExists _. iFrame. iExists _. iFrame. }
  Qed.

  Global Instance addr_of_proper : Proper ((≡) ==> eq ==> (≡)) addr_of.
  Proof. rewrite addr_of_eq. solve_proper. Qed.

  Lemma _offsetL_Loc_impl : forall l1 l2 o,
      Loc_equiv l1 l2 |-- Loc_equiv (_offsetL o l1) (_offsetL o l2).
  Proof.
    intros. rewrite /Loc_equiv _offsetL_eq /_offsetL_def /=.
    iIntros "#A"; iModIntro. iIntros (p); iSplit.
    - iIntros "X". iDestruct "X" as (p') "[X #Y]".
      iExists p'. iFrame. iApply "A"; iAssumption.
    - iIntros "X". iDestruct "X" as (p') "[X #Y]".
      iExists p'. iFrame. iApply "A"; iAssumption.
  Qed.


  (* this is for `Indirect` field references *)
  Fixpoint path_to_Offset (resolve:genv) (from : globname) (final : ident)
           (ls : list (ident * globname))
    : Offset :=
    match ls with
    | nil => @_field resolve {| f_type := from ; f_name := final |}
    | cons (i,c) ls =>
      _dot (@_field resolve {| f_type := from ; f_name := i |}) (path_to_Offset resolve c final ls)
    end.

  Definition offset_for (resolve:genv) (cls : globname) (f : FieldOrBase) : Offset :=
    match f with
    | Base parent => _super resolve cls parent
    | Field i => _field resolve {| f_type := cls ; f_name := i |}
    | Indirect ls final =>
      path_to_Offset resolve cls final ls
    | This => _id
    end.

End with_Σ.

Arguments addr_of : simpl never.
Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).

Global Opaque _sub _field _offsetL _dot addr_of.

Arguments _super {_ Σ} {resolve} _ _ : rename.
Arguments _field {_ Σ} {resolve} _ : rename.
Arguments _sub {_ Σ} {resolve} _ : rename.
Arguments _global {_ Σ} {resolve} _ : rename.
