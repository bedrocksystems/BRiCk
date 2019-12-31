(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
From bedrock.lang.cpp Require Import ast logic.

Record specification Σ : Type := { s_name : obj_name ; s_spec : Rep Σ }.
Arguments s_name {_} _.
Arguments s_spec {_} _.

Definition signature Σ : Type := mpred Σ.

Section with_Σ.
Context {Σ : gFunctors}.

Local Notation mpred := (mpred Σ) (only parsing).
Local Notation Rep := (Rep Σ) (only parsing).
Local Notation specification := (specification Σ) (only parsing).
Local Notation signature := (signature Σ) (only parsing).
Local Notation empSP := (empSP:mpred) (only parsing).

Definition make_signature (ss : list specification) : signature :=
  sepSPs (List.map (fun s => _at (_global s.(s_name)) s.(s_spec)) ss).

Fixpoint find_spec (s : obj_name) (ss : list specification) : option Rep :=
  match ss with
  | nil => None
  | x :: xs => if decide (s = x.(s_name)) then Some x.(s_spec) else find_spec s xs
  end.

Fixpoint drop_spec (s : obj_name) (ss : list specification) : list specification :=
  match ss with
  | nil => nil
  | x :: xs => if decide (s = x.(s_name)) then xs else x :: drop_spec s xs
  end.

Lemma make_signature_nil : make_signature nil -|- empSP.
Proof. split; eauto. Qed.

Hint Rewrite -> make_signature_nil : done_proof.

End with_Σ.
