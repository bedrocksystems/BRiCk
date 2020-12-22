(*
 * Copyright (C) BedRock Systems Inc. 2019-2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import bedrock.lang.prelude.base.

Require Import iris.proofmode.tactics.
From bedrock.lang.cpp Require Import semantics logic.pred ast.

Notation Loc := ptr (only parsing).

Section with_Σ.
  Context `{has_cpp : cpp_logic}.

  (** absolute locations *)
  #[local] Notation invalid := invalid_ptr.

  #[deprecated(since="2020-12-07",note="no longer needed")]
  Notation _eq := (@id ptr) (only parsing).

  (** [_eqv v] represents the pointer of a [val]. The resulting pointer
      is invalid if [v] is not a [ptr].

      NOTE this does *not* do things like converting integers to pointers.
   *)
  Definition _eqv (a : val) : Loc :=
    match a with
    | Vptr p => p
    | _ => invalid
    end.

  Lemma _eqv_eq : forall p, _eqv (Vptr p) = p.
  Proof. reflexivity. Qed.

  Definition _global_def (resolve : genv) (x : obj_name) : Loc :=
    global_ptr resolve.(genv_tu) x.
  Definition _global_aux : seal (@_global_def). Proof. by eexists. Qed.
  Definition _global := _global_aux.(unseal).
  Definition _global_eq : @_global = _ := _global_aux.(seal_eq).


  (** [addr_of]: [addr_of l p] says that pointer [p] "matches" location [l]. *)
  Definition addr_of_def (a : Loc) (b : ptr) : mpred := [| a = b |].
  Definition addr_of_aux : seal (@addr_of_def). Proof. by eexists. Qed.
  Definition addr_of := addr_of_aux.(unseal).
  Definition addr_of_eq : @addr_of = _ := addr_of_aux.(seal_eq).
  Arguments addr_of : simpl never.
  Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).

  (*
  Global Instance addr_of_proper : Proper ((≡) ==> eq ==> (≡)) addr_of.
  Proof. rewrite addr_of_eq. solve_proper. Qed.
  Global Instance addr_of_mono : Proper ((≡) ==> eq ==> (⊢)) addr_of.
  Proof. rewrite addr_of_eq. solve_proper. Qed.
  Global Instance addr_of_flip_mono : Proper ((≡) ==> eq ==> flip (⊢)) addr_of.
  Proof. rewrite addr_of_eq=>l1 l2 HL p1 p2->/=. by rewrite HL. Qed.
   *)

  Global Instance addr_of_persistent : Persistent (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.
  Global Instance addr_of_affine : Affine (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.
  Global Instance addr_of_timeless : Timeless (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.

  Global Instance addr_of_observe_precise loc a1 a2 :
    Observe2 [| a1 = a2 |] (addr_of loc a1) (addr_of loc a2).
  Proof. rewrite !addr_of_eq/addr_of_def. iIntros "-> %"; iModIntro; iFrame "%". Qed.

  Lemma addr_of_precise : forall a b c,
      addr_of a b ** addr_of a c |-- [| b = c |].
  Proof. intros. iIntros "[A B]". iApply (observe_2 with "A B"). Qed.

  (** [valid_loc]
      - same as [addr_of] except that it hides the existential quantifier
   *)
  Notation valid_loc := valid_ptr (only parsing).
  (*
  Definition valid_loc_def (l : Loc) : mpred := valid_ptr l.
  Definition valid_loc_aux : seal (@valid_loc_def). Proof. by eexists. Qed.
  Definition valid_loc := valid_loc_aux.(unseal).
  Definition valid_loc_eq : valid_loc = @valid_loc_def := valid_loc_aux.(seal_eq).
   *)

  (*
  Lemma valid_loc_rew l l' : l ≡ l' |-- valid_loc l -* valid_loc l'.
  Proof.
    rewrite valid_loc_eq /valid_loc_def addr_of_eq /addr_of_def /Loc_equiv.
    iIntros "#A". iDestruct 1 as (p) "L"; iExists p. by iApply "A".
  Qed.
  *)

  (** offsets *)
  Notation Offset := offset (only parsing).
(*
  Record Offset : Type :=
  { _offset : ptr -> ptr -> mpred
  ; _off_functional : forall p p1 p2, _offset p p1 ** _offset p p2 |-- [| p1 = p2 |]
  ; _off_valid : forall p1 p2, valid_ptr p1 ** _offset p1 p2 |-- valid_ptr p2
  ; _off_persist : forall p1 p2, Persistent (_offset p1 p2)
  ; _off_affine : forall p1 p2, Affine (_offset p1 p2)
  ; _off_timeless : forall p1 p2, Timeless (_offset p1 p2)
  }.

  Global Existing Instances _off_persist _off_affine _off_timeless.
 *)

  (*
  Local Definition invalidO : Offset.
  refine {| _offset _ _ := lfalse |}.
  abstract (intros; iIntros "[_ []]").
  abstract (intros; iIntros "[_ []]").
  Defined.

  Program Definition offset2Offset (o : offset) : Offset :=
    {| _offset from to := [| to = from .., o |]%ptr ** □ (valid_ptr from -∗ valid_ptr to) |}.
  Next Obligation. by iIntros (????) "[[#H _] [-> _]]". Qed.
  Next Obligation. iIntros (???) "[A [-> #C]]". by iApply "C". Qed.
*)
End with_Σ.

#[deprecated(since="2020-12-08",note="use 'offset'")]
Notation Offset := offset (only parsing).
#[deprecated(since="2020-12-07",note="no longer needed")]
 Notation _eq := (@id ptr) (only parsing).
#[deprecated(since="2020-12-07",note="no longer needed, use equality on ptr")]
Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).


(*
Program Definition _offsetO `{has_cpp : cpp_logic} (o : Z) : Offset :=
  {| _offset from to := [| to = offset_ptr_ o from |] ** valid_ptr to |}.
Next Obligation. intros. by iIntros "[[#H _] [-> _]]". Qed.
Next Obligation. intros. by iIntros "[_ [_ $]]". Qed.

#[deprecated(since="2020-11-17",
note="Use higher-level APIs, or _sub on arrays of unsigned char.")]
Notation offsetO := _offsetO.
 *)

Notation _id := o_id (only parsing).
Notation _dot := (o_dot) (only parsing).
Notation _field := (@o_field _) (only parsing).
Notation _sub z := (@o_sub _ z) (only parsing).
Notation _base := (@o_base _) (only parsing).
Notation _derived := (@o_derived _) (only parsing).
#[deprecated(since="2020-12-08",note="use heap notations")]
Notation _offsetL o p := (_offset_ptr p o) (only parsing).

Section with_Σ.
  Context `{has_cpp : cpp_logic}.

(*
  (* TODO easy to switch next? *)
  (** the identity [Offset] *)
  Notation _id := o_id (only parsing).
(*
  Definition _id_def : Offset.
   refine {| _offset from to := [| from = to |] |}.
   abstract (intros; iIntros "[-> #H]"; iFrame "#").
   abstract (intros; iIntros "[H <-]"; iFrame).
  Defined.
  Definition _id_aux : seal (@_id_def). Proof. by eexists. Qed.
  Definition _id := _id_aux.(unseal).
  Definition _id_eq : @_id = _ := _id_aux.(seal_eq).
 *)

  (** path composition *)
  Notation _dot := o_dot (only parsing).
  (*(o1 o2 : Offset) : Offset.
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
  Defined.
  Definition _dot_aux : seal (@_dot_def). Proof. by eexists. Qed.
  Definition _dot := _dot_aux.(unseal).
  Definition _dot_eq : @_dot = _ := _dot_aux.(seal_eq).
*)

  (** access a field *)
  Notation _field := o_field (only parsing).
(*
  Definition _field_def (resolve: genv) (f : field) : offset :=
    o_field resolve f.
  Definition _field_aux : seal (@_field_def). Proof. by eexists. Qed.
  Definition _field := _field_aux.(unseal).
  Definition _field_eq : @_field = _ := _field_aux.(seal_eq).
 *)

  (** subscript an array *)
  Notation _sub := o_sub (only parsing).
(*
  Definition _sub_def (resolve:genv) (t : type) (i : Z) : Offset :=
    match size_of resolve t with
    | Some o => offsetO (Z.of_N o * i)%Z
    | _ => invalidO
    end.

  Definition _sub_aux : seal (@_sub_def). Proof. by eexists. Qed.
  Definition _sub := _sub_aux.(unseal).
  Definition _sub_eq : @_sub = _ := _sub_aux.(seal_eq).
 *)

  (** [_base derived base] is a cast from derived to base.
   *)
  Notation _base := o_base (only parsing).
  (*
  Definition _base_def {resolve:genv} (derived base : globname) : Offset :=
    offset2Offset (o_base resolve derived base).
  Definition _base_aux : seal (@_base_def). Proof. by eexists. Qed.
  Definition _base := _base_aux.(unseal).
  Definition _base_eq : @_base = _ := _base_aux.(seal_eq).
*)
  (** [_derived base derived] is a cast from base to derived
   *)
  Notation _derived := o_derived (only parsing).
  (*
  Definition _derived_def (resolve:genv) (base derived : globname) : Offset :=
    offset2Offset (o_derived resolve base derived).
  Definition _derived_aux : seal (@_derived_def). Proof. by eexists. Qed.
  Definition _derived := _derived_aux.(unseal).
  Definition _derived_eq : @_derived = _ := _derived_aux.(seal_eq).
   *)

  (** offset from a location
   *)
  Definition _offsetL_def (o : offset) (l : Loc) : Loc := _offset_ptr l o.
  Definition _offsetL_aux : seal (@_offsetL_def). Proof. by eexists. Qed.
  Definition _offsetL := _offsetL_aux.(unseal).
  Definition _offsetL_eq : @_offsetL = _ := _offsetL_aux.(seal_eq).
 *)

  Lemma _offsetL_dot : forall (o1 o2 : offset) (l : Loc),
      _offsetL o2 (_offsetL o1 l) = _offsetL (_dot o1 o2) l.
  Proof.
    intros; by rewrite /flip offset_ptr_dot.
  Qed.

  #[deprecated(since="2020-12-08",note="use 'assoc'")]
  Lemma _dot_dot : forall (o1 o2 l: offset),
      _dot o2 (_dot o1 l) = _dot (_dot o2 o1) l.
  Proof.
    intros; by rewrite assoc.
  Qed.

End with_Σ.

Arguments addr_of : simpl never.
Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).

(*
Arguments _base {_ Σ} {resolve} _ _ : rename.
Arguments _derived {_ Σ} {resolve} _ _ : rename.
Arguments _field {_ Σ} {resolve} _ : rename.
Arguments _sub {_ Σ} {resolve} _ : rename.
*)
Arguments _global {resolve} _ : rename.


#[deprecated(since="2020-12-03",note="use _base instead")]
Notation _super := _base (only parsing).

(** [_local ρ b] returns the [ptr] that stores the local variable [b].
 *)
Definition _local (ρ : region) (b : ident) : ptr :=
  match get_location ρ b with
  | Some p => p
  | _ => invalid_ptr
  end.

(** [_this ρ] returns the [ptr] that [this] is bound to.

    NOTE because [this] is [const], we actually store the value directly
    rather than indirectly representing it in memory.
 *)
Definition _this (ρ : region) : ptr :=
  match get_this ρ with
  | Some p => p
  | _ => invalid_ptr
  end.

(** [_result ρ] is the location that the return value should be returned.
    This is currently only used for aggregates.
 *)
Definition _result (ρ : region) : ptr :=
  match get_result ρ with
  | Some p => p
  | _ => invalid_ptr
  end.


(* this is for `Indirect` field references *)
Fixpoint path_to_Offset (resolve:genv) (from : globname) (final : ident)
         (ls : list (ident * globname))
  : offset :=
  match ls with
  | nil => o_field resolve {| f_type := from ; f_name := final |}
  | cons (i,c) ls =>
    o_dot (o_field resolve {| f_type := from ; f_name := i |}) (path_to_Offset resolve c final ls)
  end.

(** [offset_for cls f] returns the [offset] of [f] where the base is [this] and has type
    [Tnamed cls].

    NOTE this function assumes that [f] is well-typed.
 *)
Definition offset_for (resolve:genv) (cls : globname) (f : FieldOrBase) : offset :=
  match f with
  | Base parent => o_base resolve cls parent
  | Field i => o_field resolve {| f_type := cls ; f_name := i |}
  | Indirect ls final =>
    path_to_Offset resolve cls final ls
  | This => o_id
  end.

#[deprecated(since="2020-12-07",note="use 'valid_ptr' instead")]
Notation valid_loc := valid_ptr (only parsing).
