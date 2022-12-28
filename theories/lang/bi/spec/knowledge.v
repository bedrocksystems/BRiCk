(*
 * Copyright (C) BedRock Systems Inc. 2020-2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.bi.prelude.

#[local] Set Primitive Projections.

(** Spec building block: knowledge *)

Class Knowledge {PROP : bi} (P : PROP) : Prop := {
  knowledge_persistent :> Persistent P;
  knowledge_affine     :> Affine P;
}.
Arguments Knowledge {_} _%I.

Ltac solve_knowledge := solve [intros; split; apply _].

Section knowledge.
  Context {PROP : bi}.

  #[global] Instance knowledge_proper : Proper (equiv ==> iff) (@Knowledge PROP).
  Proof.
    intros P1 P2 HP. split; intros []. by split; rewrite -HP. by split; rewrite HP.
  Qed.

  #[global] Instance emp_knowledge : @Knowledge PROP emp.
  Proof. solve_knowledge. Qed.
End knowledge.

(** [KnowledgeN] states that predicate [P] taking [N] arguments is [Knowledge] *)
Notation Knowledge1 P := (∀ a, Knowledge (P a)).
Notation Knowledge2 P := (∀ a, Knowledge1 (P a)).
Notation Knowledge3 P := (∀ a, Knowledge2 (P a)).
Notation Knowledge4 P := (∀ a, Knowledge3 (P a)).
Notation Knowledge5 P := (∀ a, Knowledge4 (P a)).
