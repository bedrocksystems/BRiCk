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

From bedrock.lang.cpp Require Import
     semantics logic.pred logic.path_pred ast.

Local Open Scope string_scope.

Lemma monPred_at_persistent_inv {V bi} (P : monPred V bi) :
  (∀ i, Persistent (P i)) → Persistent P.
Proof. intros HP. constructor=> i. MonPred.unseal. apply HP. Qed.

Lemma monPred_at_timeless_inv {V sbi} (P : monPredSI V sbi) :
  (∀ i, Timeless (P i)) → Timeless P.
Proof. intros HP. constructor=> i. MonPred.unseal. apply HP. Qed.


Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* representations are predicates over a location, they should be used to
   * assert properties of the heap
   *)
  Global Instance val_inhabited : Inhabited val.
  Proof. constructor. apply (Vint 0). Qed.
  Global Instance ptr_inhabited : Inhabited ptr.
  Proof. constructor. apply nullptr. Qed.

  Local Instance ptr_rel : SqSubsetEq ptr.
  Proof.
    unfold SqSubsetEq.
    unfold relation.
    apply eq.
  Defined.

  Local Instance ptr_rel_preorder : PreOrder (⊑@{ptr}).
  Proof.
    unfold sqsubseteq. unfold ptr_rel.
    apply base.PreOrder_instance_0.
  Qed.

  Canonical Structure ptr_bi_index : biIndex :=
    BiIndex ptr ptr_inhabited ptr_rel ptr_rel_preorder.

  Definition Rep := monPred ptr_bi_index mpredI.
  Definition RepI := monPredI ptr_bi_index mpredI.
  Definition RepSI := monPredSI ptr_bi_index mpredSI.


  Lemma Rep_lequiv : forall (P Q : Rep),
      (forall p, P p -|- Q p) ->
      P -|- Q.
  Proof. intros. split'; constructor; intro; rewrite H; reflexivity. Qed.

  Local Ltac solve_Rep_persistent X :=
    intros;
    rewrite X;
    constructor; apply monPred_at_persistent_inv;
    apply _.

  Local Ltac solve_Rep_timeless X :=
    intros;
    rewrite X;
    constructor; apply monPred_at_timeless_inv;
    apply _.

  Definition as_Rep (P : ptr -> mpred) : Rep := MonPred P _.

  Lemma Rep_equiv_ext_equiv : forall P Q : Rep,
      (forall x, P x -|- Q x) ->
      P -|- Q.
  Proof.
    split; red; simpl; eapply H.
  Qed.

  Definition _offsetR_def (o : Offset) (r : Rep) : Rep :=
    as_Rep (fun a => match o with
                  | Some o => match o a with
                             | None => lfalse
                             | Some p => r p
                             end
                  | None => lfalse
                  end).
  Definition _offsetR_aux : seal (@_offsetR_def). by eexists. Qed.
  Definition _offsetR := _offsetR_aux.(unseal).
  Definition _offsetR_eq : @_offsetR = _ := _offsetR_aux.(seal_eq).

  Global Instance _offsetR_persistent o r :
    Persistent r -> Persistent (_offsetR o r).
  Proof. solve_Rep_persistent _offsetR_eq. Qed.
  Global Instance Proper__offsetR_entails
    : Proper (eq ==> lentails ==> lentails) _offsetR.
  Proof.
    rewrite _offsetR_eq. unfold _offsetR_def.
    constructor. simpl. intros.
    subst. destruct y; auto. destruct (o i); auto. apply H0.
  Qed.

  Global Instance Proper__offsetR_equiv
    : Proper (eq ==> lequiv ==> lequiv) _offsetR.
  Proof.
    rewrite _offsetR_eq.
    intros ?? H1 ?? H2.
    constructor. simpl.
    intros. subst. split'; destruct y; try rewrite H2; eauto.
    all: destruct (o i); eauto; rewrite H2; reflexivity.
  Qed.

  Definition _at_def (base : Loc) (P : Rep) : mpred :=
    Exists a, base &~ a ** P a.
  Definition _at_aux : seal (@_at_def). by eexists. Qed.
  Definition _at := _at_aux.(unseal).
  Definition _at_eq : @_at = _ := _at_aux.(seal_eq).

  Global Instance _at_persistent : Persistent P -> Persistent (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.

  Global Instance Proper__at_entails
    : Proper (eq ==> lentails ==> lentails) _at.
  Proof.
    rewrite _at_eq. unfold _at_def. red. red. red.
    intros. simpl in *. subst. setoid_rewrite H0.
    reflexivity.
  Qed.

  Global Instance Proper__at_lequiv
    : Proper (eq ==> lequiv ==> lequiv) _at.
  Proof.
    intros x y H1 ?? H2.
    rewrite _at_eq /_at_def. subst.
    setoid_rewrite H2.
    reflexivity.
  Qed.

  (** Values
   * These `Rep` predicates wrap `ptsto` facts
   *)
  (* todo(gmm): make opaque *)
  Definition pureR (P : mpred) : Rep :=
    as_Rep (fun _ => P).

  Global Instance pureR_persistent (P : mpred) :
    Persistent P -> Persistent (pureR P).
  Proof. intros. apply monPred_at_persistent_inv. apply  _. Qed.

  (* this is the primitive *)
  Definition primR_def {resolve:genv} (ty : type) q (v : val) : Rep :=
    as_Rep (fun addr => @tptsto _ _ resolve ty q addr v ** [| has_type v (drop_qualifiers ty) |]).
  Definition primR_aux : seal (@primR_def). by eexists. Qed.
  Definition primR := primR_aux.(unseal).
  Definition primR_eq : @primR = _ := primR_aux.(seal_eq).
  Arguments primR {resolve} ty q v : rename.

  Global Instance primR_timeless resolve ty q p : Timeless (primR (resolve:=resolve) ty q p).
  Proof. solve_Rep_timeless primR_eq. Qed.

  Global Instance Proper_primR_entails
    : Proper (genv_leq ==> (=) ==> (=) ==> (=) ==> lentails) (@primR).
  Proof.
    do 5 red; intros; subst.
    rewrite primR_eq /primR_def. constructor; simpl.
    intros. setoid_rewrite H. reflexivity.
  Qed.
  Global Instance Proper_primR_equiv
    : Proper (genv_eq ==> (=) ==> (=) ==> (=) ==> lequiv) (@primR).
  Proof.
    do 5 red; intros; subst.
    rewrite primR_eq /primR_def. constructor; simpl.
    intros. setoid_rewrite H. reflexivity.
  Qed.

  Definition uninit_def {resolve:genv} (ty : type) q : Rep :=
    as_Rep (fun addr => Exists v : val, (primR (resolve:=resolve) ty q v) addr ).
  (* todo(gmm): this isn't exactly correct, I need a Vundef *)
  Definition uninit_aux : seal (@uninit_def). by eexists. Qed.
  Definition uninitR := uninit_aux.(unseal).
  Definition uninit_eq : @uninitR = _ := uninit_aux.(seal_eq).
  Arguments uninitR {resolve} ty q : rename.

  Global Instance uninit_timeless resolve ty q : Timeless (uninitR (resolve:=resolve) ty q).
  Proof. solve_Rep_timeless uninit_eq. Qed.

  (* this means "anything, including uninitialized" *)
  Definition anyR_def {resolve} (ty : type) q : Rep :=
    as_Rep (fun addr => (Exists v, (primR (resolve:=resolve) ty q v) addr) \\//
                                                                        (uninitR (resolve:=resolve) ty q) addr).
  Definition anyR_aux : seal (@anyR_def). by eexists. Qed.
  Definition anyR := anyR_aux.(unseal).
  Definition anyR_eq : @anyR = _ := anyR_aux.(seal_eq).
  Arguments anyR {resolve} ty q : rename.

  Global Instance anyR_timeless resolve ty q : Timeless (anyR (resolve:=resolve) ty q).
  Proof. solve_Rep_timeless anyR_eq. Qed.

  Definition tref_def (ty : type) (p : ptr) : Rep :=
    as_Rep (fun addr => [| addr = p |]).
  Definition tref_aux : seal (@tref_def). by eexists. Qed.
  Definition refR := tref_aux.(unseal).
  Definition tref_eq : @refR = _ := tref_aux.(seal_eq).

  Global Instance tref_timeless ty p : Timeless (refR ty p).
  Proof. solve_Rep_timeless tref_eq. Qed.


  (********************* DERIVED CONCEPTS ****************************)

  Definition is_null_def : Rep :=
    as_Rep (fun addr => [| addr = nullptr |]).
  Definition is_null_aux : seal (@is_null_def). by eexists. Qed.
  Definition is_null := is_null_aux.(unseal).
  Definition is_null_eq : @is_null = _ := is_null_aux.(seal_eq).

  Global Instance is_null_persistent : Persistent (is_null).
  Proof. solve_Rep_persistent is_null_eq. Qed.

  Definition is_nonnull_def : Rep :=
    as_Rep (fun addr => [| addr <> nullptr |]).
  Definition is_nonnull_aux : seal (@is_nonnull_def). by eexists. Qed.
  Definition is_nonnull := is_nonnull_aux.(unseal).
  Definition is_nonnull_eq : @is_nonnull = _ := is_nonnull_aux.(seal_eq).

  Global Instance is_nonnull_persistent : Persistent (is_nonnull).
  Proof. solve_Rep_persistent is_nonnull_eq. Qed.

  Definition tlocal_at_def (r : region) (l : ident) (p : ptr) (v : Rep) : mpred :=
    local_addr r l p ** _at (_eq p) v.
  Definition tlocal_at_aux : seal (@tlocal_at_def). by eexists. Qed.
  Definition tlocal_at := tlocal_at_aux.(unseal).
  Definition tlocal_at_eq : @tlocal_at = _ := tlocal_at_aux.(seal_eq).

End with_cpp.

Global Opaque _at _offsetR primR.

Arguments anyR {_ Σ resolve} ty q : rename.
Arguments uninitR {_ Σ resolve} ty q : rename.
Arguments primR {_ Σ resolve} ty q v : rename.
Arguments refR {_ Σ} ty v : rename.
