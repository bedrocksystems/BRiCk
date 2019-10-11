(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Coq.Classes Require Import
     RelationClasses Morphisms.

Require Import Coq.Lists.List.
From iris Require Import bi.bi.
From iris.proofmode Require Import tactics.
From Cpp Require Import IrisBridge.
Import ChargeNotation.

From Cpp Require Import ChargeCompat.

Local Set Universe Polymorphism.

Fixpoint arrowFrom {t} u (ls : list t) (T : Type)
: Type :=
  match ls with
  | nil => T
  | cons l ls => u -> arrowFrom u ls T
  end.

Section zip.
  Context {A B C : Type} (f : A -> B -> C).
  Fixpoint zip (x : list A) (y : list B) : list C :=
    match x , y with
    | nil , _
    | _ , nil => nil
    | x :: xs , y :: ys => f x y :: zip xs ys
    end.
End zip.

Section withLogic.
  Context `{!PROP : bi}.

  Fixpoint applyEach {t u T} (ls : list t) (vals : list u)
    : forall (v : arrowFrom u ls T)
        (P : T -> list (t * u) -> PROP), PROP :=
    match ls , vals with
    | nil , nil => fun v P => P v nil
    | l :: ls , x :: xs => fun v P =>
      applyEach ls xs (v x) (fun z xs => P z (cons (l, x) xs))
    | _ , _ => fun _ _ => lfalse
    end.

  Fixpoint ForallEach {t u T} (ls : list t)
    : forall (v : arrowFrom u ls T)
        (P : T -> list (t * u) -> PROP), PROP :=
    match ls with
    | nil => fun v P => P v nil
    | l :: ls => fun v P => Forall x,
      ForallEach ls (v x) (fun z xs => P z (cons (l, x) xs))
    end.

  Fixpoint Forall2Each {t u T U} (ls : list t)
    : forall (v : arrowFrom u ls T) (v' : arrowFrom u ls U)
        (P : T -> U -> list (t * u) -> PROP), PROP :=
    match ls with
    | nil => fun v v' P => P v v' nil
    | l :: ls => fun v v' P => Forall x,
      Forall2Each ls (v x) (v' x) (fun z z' xs => P z z' (cons (l, x) xs))
    end.

  Fixpoint ExistsEach {t u T} (ls : list t)
    : forall (v : arrowFrom u ls T)
        (P : T -> list (t * u) -> PROP), PROP :=
    match ls with
    | nil => fun v P => P v nil
    | l :: ls => fun v P => Exists x,
      ExistsEach ls (v x) (fun z xs => P z (cons (l, x) xs))
    end.

End withLogic.

Section arrowFrom_map.
  Context {t u : Type}.
  Context {T U : Type} (f : T -> U).

  Fixpoint arrowFrom_map {ls : list t} : arrowFrom u ls T -> arrowFrom u ls U :=
    match ls as ls return arrowFrom u ls T -> arrowFrom u ls U with
    | nil => f
    | l :: ls => fun X X0 => arrowFrom_map (X X0)
    end.
End arrowFrom_map.

(* telescopes *)
(* todo: Use the ones from stdpp instead *)
Inductive tele : Type :=
| tdone
| tcons {t : Type} (_ : t -> tele).

Fixpoint teleF (T : Type) (t : tele) : Type :=
  match t with
  | tdone => T
  | @tcons t ts => forall (x : t), teleF T (ts x)
  end.

Fixpoint teleF_map {T U : Type} (f : T -> U) {t : tele}
  : teleF T t -> teleF U t :=
  match t as t return teleF T t -> teleF U t with
  | tdone => fun x => f x
  | tcons t => fun g x => @teleF_map T U f (t x) (g x)
  end.

Definition tsingle (t : Type) : tele := tcons (fun _ : t => tdone).
Coercion tsingle : Sortclass >-> tele.
Notation "[ ]" := (tdone) : tele_scope.
Notation "[ a , .. , b ]" :=
  (@tcons a%type (fun _ => .. (@tcons b%type (fun _ => tdone)) ..))
  (at level 0) : tele_scope.
Bind Scope tele_scope with tele.
Delimit Scope tele_scope with tele.

From Cpp.Syntax Require Import Types.
From Cpp.Sem Require Import Semantics.
Section with_PROP.
Context {PROP : bi}.

Lemma wandSP_only_provableL : forall (P : Prop) (Q R : PROP),
    P ->
    Q |-- R ->
    [| P |] -* Q |-- R.
Proof.
  intros.
  rewrite <- H0; clear H0.
  iIntros "H". iApply "H". eauto.
Qed.

Lemma wandSP_only_provableR : forall (A : Prop) (B C : PROP),
    (A -> B |-- C) ->
    B |-- [| A |] -* C.
Proof.
  intros.
  iIntros "HB %".
  iApply H; eauto.
Qed.

Lemma forallEach_primes :
  forall (ts : list type)
    (fs' : arrowFrom val ts ((val -> PROP) -> PROP)) Z,
    Forall vs : list val,
  [| Datatypes.length vs = Datatypes.length ts |] -*
  (Forall Q : val -> PROP,
     applyEach ts vs fs'
               (fun (k : (val -> PROP) -> PROP) (_ : list (type * val)) => k Q) -*
               Z vs Q) -|-
  ForallEach ts fs'
  (fun (PQ : (val -> PROP) -> PROP) (args : list (type * val)) =>
     Forall Q : val -> PROP, PQ Q -* Z (map snd args) Q).
Proof.
  induction ts.
  { simpl. intros.
    split'.
    { eapply lforallR; intro Q.
      eapply (lforallL nil).
      eapply wandSP_only_provableL; [ reflexivity | ].
      eapply lforallL. reflexivity. }
    { eapply lforallR. intros.
      destruct x.
      { eapply wandSP_only_provableR. reflexivity. }
      { eapply wandSP_only_provableR. intros.
        inversion H. } } }
  { simpl. intros.
    split'.
    { eapply lforallR.
      intros.
      specialize (IHts (fs' x) (fun a b => Z (x :: a) b)).
      rewrite <- IHts.
      eapply lforallR. intros.
      eapply (lforallL (x :: x0)).
      eapply wandSP_only_provableR; intros.
      eapply wandSP_only_provableL; [ simpl; f_equal; eassumption | ].
      reflexivity. }
    { eapply lforallR; intros.
      eapply wandSP_only_provableR; intros.
      destruct x.
      { eapply lforallR; intro.
        eapply wandSPAdj'.
        rewrite -> sepSP_falseL.
        eapply lfalseL. }
      { eapply (lforallL v).
        rewrite <- (IHts (fs' v) (fun xs => Z (v :: xs))).
        eapply (lforallL x).
        eapply wandSP_only_provableL.
        simpl in H.
        inversion H. reflexivity. reflexivity. } } }
Qed.

End with_PROP.

Arguments ForallEach {_ _ _ _} [_] _ _.
