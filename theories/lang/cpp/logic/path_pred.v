(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

From iris.bi Require Export monpred.

From bedrock.lang.cpp Require Import semantics logic.pred ast.

Local Open Scope string_scope.

Lemma monPred_at_persistent_inv {V bi} (P : monPred V bi) :
  (∀ i, Persistent (P i)) → Persistent P.
Proof. intros HP. constructor=> i. MonPred.unseal. apply HP. Qed.

Lemma monPred_at_timeless_inv {V sbi} (P : monPredSI V sbi) :
  (∀ i, Timeless (P i)) → Timeless P.
Proof. intros HP. constructor=> i. MonPred.unseal. apply HP. Qed.

Section with_Σ.
  Context `{has_cpp : cpp_logic ti}.

  (* locations are computations that produce an address.
   * - note(gmm): they are always computable from the program except.
   *)
  Definition Loc : Type := option ptr.

  Definition Offset : Type := option (ptr -> option ptr).

  Local Ltac solve_Loc_persistent X :=
    intros;
    rewrite X;
    constructor; apply monPred_at_persistent_inv;
    apply _.
  Local Ltac solve_Offset_persistent X :=
    intros;
    rewrite X;
    constructor; apply monPred_at_persistent_inv;
    constructor; apply monPred_at_persistent_inv;
    apply _.

  Local Ltac solve_Loc_timeless X :=
    intros;
    rewrite X;
    constructor; apply monPred_at_timeless_inv;
    apply _.
  Local Ltac solve_Offset_timeless X :=
    intros;
    rewrite X;
    constructor; apply monPred_at_timeless_inv;
    constructor; apply monPred_at_timeless_inv;
    apply _.

  Definition LocEq (l1 l2 : Loc) : Prop :=
    l1 = l2.

  (* ^ these two could be duplicable because regions don't need to be
   * reused. the reason that local variables need to be tracked is that
   * they could go out of scope.
   * - an alternative, and (sound) solution is to generate a fresh region
   *   each time that we create a new scope. To do this, we need to track in
   *   the AST the debruijn index of the binder.
   * - yet another alternative is to inline regions explicitly into the WP.
   *   essentially region := list (list (string * ptr)). this essentially makes
   *   _local persistent.
   *)

  (* absolute locations *)
  Definition _eq_def (p : ptr) : Loc :=
    Some p.
  Definition _eq_aux : seal (@_eq_def). by eexists. Qed.
  Definition _eq := _eq_aux.(unseal).
  Definition _eq_eq : @_eq = _ := _eq_aux.(seal_eq).

  Definition _eqv (a : val) : Loc :=
    match a with
    | Vptr p => _eq p
    | _ => None
    end.

  Lemma _eqv_eq : forall p, _eqv (Vptr p) = _eq p.
  Proof. reflexivity. Qed.

  Definition _global_def (resolve : genv) (x : obj_name) : Loc :=
    match glob_addr resolve x with
    | None => None
    | Some p => Some p
    end.
  Definition _global_aux : seal (@_global_def). by eexists. Qed.
  Definition _global := _global_aux.(unseal).
  Definition _global_eq : @_global = _ := _global_aux.(seal_eq).

  Definition _local (ρ : region) (b : ident) : Loc :=
    match get_location ρ b with
    | Some p => _eq p
    | _ => None
    end.

  Definition _this (ρ : region) : Loc :=
    match get_this ρ with
    | Some p => _eq p
    | _ => None
    end.

  Definition _result (ρ : region) : Loc :=
    match get_result ρ with
    | Some p => _eq p
    | _ => None
    end.

  (* offsets *)
  Definition _field_def (resolve: genv) (f : field) : Offset :=
    match offset_of resolve f.(f_type) f.(f_name) with
    | Some o => Some (fun p => Some (offset_ptr_ o p))
    | _ => None
    end.
  Definition _field_aux : seal (@_field_def). Proof using. by eexists. Qed.
  Definition _field := _field_aux.(unseal).
  Definition _field_eq : @_field = _ := _field_aux.(seal_eq).

  Definition _sub_def (resolve:genv) (t : type) (i : Z) : Offset :=
    match size_of resolve t with
    | Some n => Some (fun p => Some (offset_ptr_ (i * Z.of_N n) p))
    | _ => None
    end.
  Definition _sub_aux : seal (@_sub_def). by eexists. Qed.
  Definition _sub := _sub_aux.(unseal).
  Definition _sub_eq : @_sub = _ := _sub_aux.(seal_eq).

  (* this represents a derived-to-base cast
     todo: determine if this needs to handle a chain.
   *)
  Definition _super_def (resolve:genv) (sub super : globname) : Offset :=
    match parent_offset resolve sub super with
    | Some o => Some (fun p => Some (offset_ptr_ o p))
    | _ => None
    end.
  Definition _super_aux : seal (@_super_def). by eexists. Qed.
  Definition _super := _super_aux.(unseal).
  Definition _super_eq : @_super = _ := _super_aux.(seal_eq).

  Definition _id_def : Offset := Some (fun x => Some x).
  Definition _id_aux : seal (@_id_def). by eexists. Qed.
  Definition _id := _id_aux.(unseal).
  Definition _id_eq : @_id = _ := _id_aux.(seal_eq).

  Definition _dot_def (o1 o2 : Offset) : Offset :=
    match o1 , o2 with
    | Some o1 , Some o2 => Some (fun x => match o1 x with
                                      | None => None
                                      | Some p => o2 p
                                      end)
    | _ , _ => None
    end.
  Definition _dot_aux : seal (@_dot_def). by eexists. Qed.
  Definition _dot := _dot_aux.(unseal).
  Definition _dot_eq : @_dot = _ := _dot_aux.(seal_eq).

  Definition _offsetL_def (o : Offset) (l : Loc) : Loc :=
    match o , l with
    | Some o , Some l => match o l with
                        | None => None
                        | Some p => Some p
                        end
    | _ , _ => None
    end.
  Definition _offsetL_aux : seal (@_offsetL_def). by eexists. Qed.
  Definition _offsetL := _offsetL_aux.(unseal).
  Definition _offsetL_eq : @_offsetL = _ := _offsetL_aux.(seal_eq).


  Definition addr_of_def (a : Loc) (b : ptr) : mpred :=
    [| a = Some b |].
  Definition addr_of_aux : seal (@addr_of_def). by eexists. Qed.
  Definition addr_of := addr_of_aux.(unseal).
  Definition addr_of_eq : @addr_of = _ := addr_of_aux.(seal_eq).
  Arguments addr_of : simpl never.
  Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).

  Global Instance addr_of_persistent : Persistent (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.

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

Arguments _super {resolve} _ _ : rename.
Arguments _field {resolve} _ : rename.
Arguments _sub {resolve} _ : rename.
Arguments _global {resolve} _ : rename.
