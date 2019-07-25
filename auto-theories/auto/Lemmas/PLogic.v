(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Strings.String.

From Cpp Require Import
     Ast Sem Util.
From Cpp.Auto Require Import
     Definitions Discharge type.

Local Ltac t :=
  discharge fail idtac fail fail eauto.

(* with_addr definitions *)
Definition with_addr (l : Loc) (p : val -> mpred) : mpred :=
  Exists a, (l &~ a ** ltrue) //\\ p a.

Theorem with_addr_defn : forall l p,
    with_addr l p -|- Exists a, (l &~ a ** ltrue) //\\ p a.
Proof.
  reflexivity.
Qed.

Global Opaque with_addr.


(* there is a problem with using `tat_field` for uninitialized because
 * `tat_field` says that the data has the appropriate type.
 *)
Definition find_struct (nm : globname) (m : compilation_unit) : option Struct :=
  match CompilationUnit.lookup_global m nm with
  | Some (Gstruct s) => Some s
  | _ => None
  end.

Lemma uninit_class_fwd
: forall cls base m st F Q,
    F |-- denoteModule m ** ltrue ->
    find_struct cls m = Some st ->
    _at (_eq base)
        (sepSPs (List.map (fun gn =>
                             _offsetR (_super cls gn) (uninit (Tref gn))) st.(s_bases) ++
                 List.map (fun '(n,t,_) =>
                        (* todo(gmm): there is a problem with references in this code.
                         *)
                             _offsetR
                               (_field {| f_name := n ; f_type := cls |})
                               (uninit (drop_qualifiers t))) st.(s_fields))) ** F |-- Q ->
    _at (_eq base) (uninit (Tref cls)) ** F |-- Q.
Proof.
  intros.
Admitted.

Lemma tany_class_bwd
: forall cls base m st F Q,
    F |-- denoteModule m ** ltrue ->
    find_struct cls m = Some st ->
    F |-- _at (_eq base)
              (sepSPs (List.map (fun gn =>
                                   _offsetR (_super cls gn) (tany (Tref gn))) st.(s_bases) ++
                       List.map (fun '(n,t,_) =>
                                   _offsetR (_field {| f_name := n ; f_type := cls |})
                                            (tany (drop_qualifiers t))) st.(s_fields))) ** Q ->
    F |-- _at (_eq base) (tany (Tref cls)) ** Q.
Proof.
  intros.
Admitted.

(* Learning Lemmas *)
Lemma learn_bounds_at_int_val : forall (s : bool) (w : option nat) p v P Q,
    (forall z, Vint z = v -> has_type (Vint z) (Tint w s) -> _at p (tprim (Tint w s) (Vint z)) ** P |-- Q) ->
    _at p (tprim (Tint w s) v) ** P |-- Q.
Proof.
  Local Transparent _at tprim.
  unfold _at, tprim; simpl.
  intros.
  t. simpl in *.
  eapply has_type_int_is_Vint in H0. destruct H0 as [ ? [ ? ? ] ].
  subst.
  rewrite <- H. t. auto. auto.
  Opaque _at tprim.
Qed.

Lemma learn_bounds_at_int_Vint : forall (s : bool) (w : option nat) p v P Q,
    (has_type (Vint v) (Tint w s) -> _at p (tprim (Tint w s) (Vint v)) ** P |-- Q) ->
    _at p (tprim (Tint w s) (Vint v)) ** P |-- Q.
Proof.
  Local Transparent _at tprim.
  unfold _at, tprim; simpl.
  intros.
  t. simpl in *.
  rewrite <- H. t. auto.
  Opaque _at tprim.
Qed.

Lemma learn_bounds_at_tuint : forall bits p v P Q,
    (has_type (Vint v) (Tint (Some bits) false) -> _at p (tuint bits v) ** P |-- Q) ->
    _at p (tuint bits v) ** P |-- Q.
Proof.
  Local Transparent _at tuint tprim.
  unfold _at, tuint, tprim; simpl.
  intros.
  t. simpl in *.
  rewrite <- H. t. auto.
  Opaque _at tprim tuint.
Qed.

Lemma learn_bounds_tlocal_val : forall (s : bool) (w : option nat) v P Q r x,
    (forall a vv, Vint vv = v -> has_type (Vint vv) (Tint w s) ->
             tlocal_at r x a (tprim (Tint w s) (Vint vv)) ** P |-- Q) ->
    tlocal r x (tprim (Tint w s) v) ** P |-- Q.
Proof.
  Local Transparent _at tprim.
  unfold tlocal, tlocal_at, _at, tprim; simpl.
  intros.
  t.
  eapply has_type_int_is_Vint in H1. destruct H1 as [ ? [ ? ? ] ].
  rewrite <- H; [ | eauto | eassumption ]. subst. t.
  Opaque _at tprim.
Qed.

Lemma learn_bounds_tlocal_Vint : forall (s : bool) (w : option nat) v P Q r x,
    (forall a, has_type (Vint v) (Tint w s) -> tlocal_at r x a (tprim (Tint w s) (Vint v)) ** P |-- Q) ->
    tlocal r x (tprim (Tint w s) (Vint v)) ** P |-- Q.
Proof.
  Local Transparent _at tprim.
  unfold tlocal, tlocal_at, _at, tprim; simpl.
  intros.
  t.
  rewrite <- H. t. auto.
  Opaque _at tprim.
Qed.

Lemma learn_bounds_tlocal_at_val : forall (s : bool) (w : option nat) v P Q r x a,
    (forall vv, Vint vv = v -> has_type (Vint vv) (Tint w s) -> tlocal_at r x a (tprim (Tint w s) (Vint vv)) ** P |-- Q) ->
    tlocal_at r x a (tprim (Tint w s) v) ** P |-- Q.
Proof.
  Local Transparent _at tprim.
  unfold tlocal, tlocal_at, _at, tprim; simpl.
  intros.
  t. simpl in *.
  eapply has_type_int_is_Vint in H1. destruct H1 as [ ? [ ? ? ] ].
  subst.
  rewrite <- H. t. auto. auto.
  Opaque _at tprim.
Qed.

Lemma learn_bounds_tlocal_at_Vint : forall (s : bool) (w : option nat) v P Q r x a,
    (has_type (Vint v) (Tint w s) -> tlocal_at r x a (tprim (Tint w s) (Vint v)) ** P |-- Q) ->
    tlocal_at r x a (tprim (Tint w s) (Vint v)) ** P |-- Q.
Proof.
  Local Transparent _at tprim.
  unfold tlocal, tlocal_at, _at, tprim; simpl.
  intros.
  t. simpl in *.
  rewrite <- H. t. auto.
  Opaque _at tprim.
Qed.


(* For manipulating _at *)
Lemma _at_eq_fwd : forall l r P Q,
    (forall a, l &~ a ** _at (_eq a) r ** P |-- Q) ->
    _at l r ** P |-- Q.
Proof.
  intros. rewrite _at_eq. t. rewrite <- H. t.
Qed.
Lemma _at_eq_bwd : forall l r P Q,
    (exists a, P |-- l &~ a ** _at (_eq a) r ** Q) ->
    P |-- _at l r ** Q.
Proof.
  intros. rewrite _at_eq. destruct H. rewrite H. t.
Qed.

Lemma _at_empSP_fwd : forall x P Q,
    P |-- Q ->
    _at (_eq x) empSP ** P |-- Q.
Proof. intros. rewrite _at_empSP. rewrite H. t. Qed.

Lemma _at_empSP_bwd : forall x P Q,
    P |-- Q ->
    P |-- _at (_eq x) empSP ** Q.
Proof. intros. rewrite PLogic._at_empSP. rewrite H. t. Qed.
Lemma _at_lexists_fwd: forall (x : Loc) (T : Type) (P : T -> Rep) F F',
    Exists v : T, _at x (P v) ** F |-- F' ->
    _at x (Exists x : _, P x) ** F |-- F'.
Proof. intros. rewrite _at_lexists. rewrite <- H. t. Qed.
Lemma _at_lexists_bwd: forall (x : Loc) (T : Type) (P : T -> Rep) F F',
    F |-- Exists v : T, _at x (P v) ** F' ->
    F |-- _at x (Exists x : _, P x) ** F'.
Proof. intros. rewrite PLogic._at_lexists. rewrite H. t. Qed.
Lemma _at_pureR_fwd: forall (x : val) (P : mpred) F F',
    P ** F |-- F' ->
    _at (_eq x) P ** F |-- F'.
Proof. intros. rewrite _at_pureR. assumption. Qed.
Lemma _at_pureR_bwd: forall (x : val) (P : mpred) F F',
    F |-- P ** F' ->
    F |-- _at (_eq x) P ** F'.
Proof. intros. rewrite PLogic._at_pureR. assumption. Qed.

Lemma _at_sepSP_bwd : forall x P Q F F',
    F |-- _at (_eq x) P ** _at (_eq x) Q ** F' ->
    F |-- _at (_eq x) (P ** Q) ** F'.
Proof.
  intros. rewrite H. rewrite PLogic._at_sepSP. t.
Qed.
Lemma _at_sepSP_fwd : forall x P Q F F',
    _at (_eq x) P ** _at (_eq x) Q ** F' |-- F ->
    _at (_eq x) (P ** Q) ** F' |-- F.
Proof.
  intros. rewrite <- H. rewrite PLogic._at_sepSP. t.
Qed.
Lemma _at_offsetR_fwd : forall base o r P Q,
    _at (_offsetL o base) r ** P |-- Q ->
    _at base (_offsetR o r) ** P |-- Q.
Proof.
  intros. rewrite _at_offsetL_offsetR. assumption.
Qed.
Lemma _at_offsetR_bwd : forall base o r P Q,
    P |-- _at (_offsetL o base) r ** Q ->
    P |-- _at base (_offsetR o r) ** Q.
Proof.
  intros. rewrite _at_offsetL_offsetR. assumption.
Qed.
Lemma _at_is_null_fwd : forall x P Q,
    [| x = Vptr nullptr |] ** P |-- Q ->
    _at (_eq x) is_null ** P |-- Q.
Proof.
  intros. rewrite _at_eq_is_null. assumption.
Qed.
Lemma _at_is_null_bwd : forall x P Q,
    P |-- [| x = Vptr nullptr |] ** Q ->
    P |-- _at (_eq x) is_null ** Q.
Proof.
  intros. rewrite _at_eq_is_null. assumption.
Qed.
Lemma _at_is_nonnull_fwd : forall x P Q,
    (Exists p, [| p <> nullptr |] ** [| x = Vptr p |]) ** P |-- Q ->
    _at (_eq x) is_nonnull ** P |-- Q.
Proof.
  intros. rewrite _at_eq_is_nonnull. assumption.
Qed.
Lemma _at_is_nonnull_bwd : forall x P Q,
    P |-- (Exists p, [| p <> nullptr |] ** [| x = Vptr p |]) ** Q ->
    P |-- _at (_eq x) is_nonnull ** Q.
Proof.
  intros. rewrite _at_eq_is_nonnull. assumption.
Qed.


Theorem with_addr_local_at : forall r x addr rep F P,
    tlocal_at r x addr rep ** F |-- P addr ->
    tlocal_at r x addr rep ** F |-- with_addr (_local r x) P.
Proof.
  intros. rewrite with_addr_defn.
  unfold tlocal_at in *.
  t.
  assumption.
Qed.

Theorem with_addr_offsetL : forall loc addr F P,
  loc &~ addr ** F |-- P addr ->
  loc &~ addr ** F |-- with_addr loc P.
Proof.
  intros. rewrite with_addr_defn.
  t. assumption.
Qed.

Lemma tlocal_at__local : forall r x a rep P Q,
    _at (_eq a) rep ** P |-- Q ->
    tlocal_at r x a rep ** P |-- _local r x &~ a ** Q.
Proof.
  unfold tlocal_at. intros.
  t. assumption.
Qed.

Lemma _at_eq_tref_fwd : forall x ty v P Q,
    (x = v -> P |-- Q) ->
    _at (_eq x) (tref ty v) ** P |-- Q.
Proof.
  intros.
  rewrite _at_eq_tref.
  t.
  intuition.
Qed.

Lemma _at_eq_tref_bwd : forall x ty P Q,
    P |-- Q ->
    P |-- _at (_eq x) (tref ty x) ** Q.
Proof.
  intros.
  rewrite _at_eq_tref.
  t.
  assumption.
Qed.

Lemma tlocal_at__at:
  forall (r : region) (x : ident) (a : val) (rep rep' : Rep) (P Q : mpred),
    rep |-- rep' ->
    _local r x &~ a ** P |-- Q ->
    tlocal_at r x a rep ** P |-- _at (_eq a) rep' ** Q.
Proof.
  unfold tlocal_at. intros.
  rewrite H. rewrite <- H0. t.
Qed.

Lemma _local_tlocal : forall r x a rep P Q,
    P |-- _at (_eq a) rep ** Q ->
    _local r x &~ a ** P |-- tlocal r x rep ** Q.
Proof.
  intros. rewrite H. t. unfold tlocal, tlocal_at. t.
Qed.

Lemma _local_tlocal_at : forall (r : region) (x : ident) (a : val) (rep : Rep) (P Q : mpred),
    P |-- _at (_eq a) rep ** Q ->
    _local r x &~ a ** P |-- tlocal_at r x a rep ** Q.
Proof.
  unfold tlocal_at. intros.
  t. assumption.
Qed.

Lemma tlocal_at_tlocal_fwd:
  forall (r : region) (x : ident) (v : Rep) (F F' : mpred),
  (forall a, tlocal_at r x a v ** F |-- F') ->
  tlocal r x v ** F |-- F'.
Proof.
  unfold tlocal. intros.
  t.
  rewrite <- H.
  t.
Qed.
