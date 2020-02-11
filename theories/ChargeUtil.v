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
Require Import bedrock.IrisBridge.
Import ChargeNotation.

(* From Cpp Require Import ChargeCompat. *)

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

  (* Fixpoint ForallEach {t u T} (ls : list t) *)
  (*   : forall (v : arrowFrom u ls T) *)
  (*       (P : T -> list (t * u) -> PROP), PROP := *)
  (*   match ls with *)
  (*   | nil => fun v P => P v nil *)
  (*   | l :: ls => fun v P => Forall x, *)
  (*     ForallEach ls (v x) (fun z xs => P z (cons (l, x) xs)) *)
  (*   end. *)

  (* Fixpoint Forall2Each {t u T U} (ls : list t) *)
  (*   : forall (v : arrowFrom u ls T) (v' : arrowFrom u ls U) *)
  (*       (P : T -> U -> list (t * u) -> PROP), PROP := *)
  (*   match ls with *)
  (*   | nil => fun v v' P => P v v' nil *)
  (*   | l :: ls => fun v v' P => Forall x, *)
  (*     Forall2Each ls (v x) (v' x) (fun z z' xs => P z z' (cons (l, x) xs)) *)
  (*   end. *)

  (* Fixpoint ExistsEach {t u T} (ls : list t) *)
  (*   : forall (v : arrowFrom u ls T) *)
  (*       (P : T -> list (t * u) -> PROP), PROP := *)
  (*   match ls with *)
  (*   | nil => fun v P => P v nil *)
  (*   | l :: ls => fun v P => Exists x, *)
  (*     ExistsEach ls (v x) (fun z xs => P z (cons (l, x) xs)) *)
  (*   end. *)

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

End with_PROP.
