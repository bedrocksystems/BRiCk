(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.prelude.base.

Require Import iris.proofmode.tactics.
From bedrock.lang.cpp Require Import semantics logic.pred ast.

Notation Loc := ptr (only parsing).

Section with_Σ.
  Context `{has_cpp : cpp_logic}.

  (** absolute locations *)
  #[local] Notation invalid := invalid_ptr.

  (** [_eqv v] represents the pointer of a [val]. The resulting pointer
      is invalid if [v] is not a [ptr].

      NOTE this does *not* do things like converting integers to pointers.
   *)
  Definition _eqv (a : val) : ptr :=
    match a with
    | Vptr p => p
    | _ => invalid
    end.

  Lemma _eqv_eq : forall p, _eqv (Vptr p) = p.
  Proof. reflexivity. Qed.

  Definition _global_def (resolve : genv) (x : obj_name) : ptr :=
    global_ptr resolve.(genv_tu) x.
  Definition _global_aux : seal (@_global_def). Proof. by eexists. Qed.
  Definition _global := _global_aux.(unseal).
  Definition _global_eq : @_global = _ := _global_aux.(seal_eq).


  (** [addr_of]: [addr_of l p] says that pointer [p] "matches" location [l]. *)
  Definition addr_of_def (a : ptr) (b : ptr) : mpred := [| a = b |].
  Definition addr_of_aux : seal (@addr_of_def). Proof. by eexists. Qed.
  Definition addr_of := addr_of_aux.(unseal).
  Definition addr_of_eq : @addr_of = _ := addr_of_aux.(seal_eq).
  Arguments addr_of : simpl never.
  Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).

  Global Instance addr_of_persistent {o l} : Persistent (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.
  Global Instance addr_of_affine {o l} : Affine (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.
  Global Instance addr_of_timeless {o l} : Timeless (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.

  Global Instance addr_of_observe_precise loc a1 a2 :
    Observe2 [| a1 = a2 |] (addr_of loc a1) (addr_of loc a2).
  Proof. rewrite !addr_of_eq/addr_of_def. iIntros "-> %"; iModIntro; iFrame "%". Qed.

  Lemma addr_of_precise : forall a b c,
      addr_of a b ** addr_of a c |-- [| b = c |].
  Proof. intros. iIntros "[A B]". iApply (observe_2 with "A B"). Qed.
End with_Σ.

(** offsets *)
#[deprecated(since="2020-12-07",note="no longer needed")]
Notation _eq := (@id ptr) (only parsing).
#[deprecated(since="2020-12-07",note="no longer needed, use equality on ptr")]
Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).
#[deprecated(since="2020-12-07",note="use 'valid_ptr' instead")]
Notation valid_loc := valid_ptr (only parsing).

#[deprecated(since="2020-12-08",note="use heap notations")]
Notation _offsetL o p := (_offset_ptr p o) (only parsing).

Arguments addr_of : simpl never.
Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).

Arguments _global {resolve} _ : rename.



(** [_local ρ b] returns the [ptr] that stores the local variable [b].
 *)
Definition _local (ρ : region) (b : ident) : ptr :=
  match get_location ρ b with
  | Some p => p
  | _ => invalid_ptr
  end.
Arguments _local !_ !_ / : simpl nomatch, assert.

(** [_this ρ] returns the [ptr] that [this] is bound to.

    NOTE because [this] is [const], we actually store the value directly
    rather than indirectly representing it in memory.
 *)
Definition _this (ρ : region) : ptr :=
  match get_this ρ with
  | Some p => p
  | _ => invalid_ptr
  end.
Arguments _this !_ / : assert.

(** [_result ρ] is the location that the return value should be returned.
    This is currently only used for aggregates.
 *)
Definition _result (ρ : region) : ptr :=
  match get_result ρ with
  | Some p => p
  | _ => invalid_ptr
  end.
Arguments _result !_ / : assert.


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
