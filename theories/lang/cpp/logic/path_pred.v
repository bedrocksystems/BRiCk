(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.

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

  #[global] Instance _global_inj {resolve : genv} : Inj (=) (=) (_global resolve).
  Proof. rewrite _global_eq. apply _. Qed.

  Lemma _global_nonnull resolve n : _global resolve n <> nullptr.
  Proof. rewrite _global_eq /_global_def. apply global_ptr_nonnull. Qed.
End with_Σ.

(** offsets *)
#[deprecated(since="2020-12-08",note="use heap notations")]
Notation _offsetL o p := (_offset_ptr p o) (only parsing).

Arguments _global {resolve} _ : rename.


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
Definition offset_for {resolve:genv} (cls : globname) (f : InitPath) : offset :=
  match f with
  | InitBase parent => o_base resolve cls parent
  | InitField i => o_field resolve {| f_type := cls ; f_name := i |}
  | InitIndirect ls final =>
    path_to_Offset resolve cls final ls
  | InitThis => o_id
  end.
