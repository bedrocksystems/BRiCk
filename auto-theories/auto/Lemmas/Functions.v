(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Cpp Require Import
     Ast Sem Util.
From Cpp.Auto Require Import
     Definitions.

(* ways to find function specifications *)
Lemma cglob'_by_cglob'_gen : forall resolve g ti s s' P,
    s = s' ->
    cglob' (resolve:=resolve) g ti s ** P
    |-- (|> cglob' (resolve:=resolve) g ti s') ** ltrue.
Proof. Admitted.
Lemma cglob'_by_ti_cglob'_gen : forall resolve g ti s s' P,
    s = s' ->
    ti_cglob' (resolve:=resolve) g s ** P
    |-- (|> cglob' (resolve:=resolve) g ti s') ** ltrue.
Proof. Admitted.
Lemma cglob'_by_later_cglob'_gen : forall resolve g ti s s' P,
    s = s' ->
    (|> cglob' (resolve:=resolve) g ti s) ** P
    |-- (|> cglob' (resolve:=resolve) g ti s') ** ltrue.
Proof. Admitted.
Lemma cglob'_by_later_ti_cglob'_gen : forall resolve g ti s s' P,
    s = s' ->
    (|> ti_cglob' (resolve:=resolve) g s) ** P
    |-- (|> cglob' (resolve:=resolve) g ti s') ** ltrue.
Proof. Admitted.
Lemma unify_SFunction : forall a b c a' b' c',
    a = a' ->
    forall pf : b' = b,
      c = match pf with eq_refl => c' end ->
    SFunction a b c = SFunction a' b' c'.
Proof. intros; subst. reflexivity. Qed.

Lemma ti_cglob'_cglob' : forall resolve g ti s,
    ti_cglob' (resolve:=resolve) g s |-- cglob' (resolve:=resolve) g ti s.
Proof.
  intros.
  eapply lforallL. reflexivity.
Qed.

Lemma ti_cglob'_cglob'_sepSP :
  forall (resolve : genv) (g : globname) (ti : thread_info)
    (s : function_spec') P Q,
    cglob' (resolve:=resolve) g ti s ** P |-- Q ->
    ti_cglob' (resolve:=resolve) g s ** P |-- Q.
Proof. intros. rewrite ti_cglob'_cglob'. eassumption. Qed.

Lemma ti_cglob'_cglob'_cancel :
  forall (resolve : genv) (g : globname) (ti : thread_info)
    (s : function_spec') P Q,
    ti_cglob' (resolve:=resolve) g s ** P |-- Q ->
    ti_cglob' (resolve:=resolve) g s ** P |-- cglob' (resolve:=resolve) g ti s ** Q.
Proof. intros. rewrite <- H. Admitted.

Lemma ti_cglob'_later_cglob'_cancel :
  forall (resolve : genv) (g : globname) (ti : thread_info)
    (s : function_spec') P Q,
    ti_cglob' (resolve:=resolve) g s ** P |-- Q ->
    ti_cglob' (resolve:=resolve) g s ** P |-- (|> cglob' (resolve:=resolve) g ti s) ** Q.
Proof. intros. rewrite <- H. Admitted.
