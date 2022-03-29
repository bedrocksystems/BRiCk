(*
 * Copyright (c) 2021-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export iris.bi.monpred.
Require Import bedrock.lang.bi.prelude.
Require Import iris.proofmode.monpred.

Notation "A -mon> B" := (monPred A B%bi_type) : stdpp_scope.
Notation "A -mon> B" := (monPredI A B) : bi_type_scope.

#[global] Instance: Params (@Objective) 2 := {}.

#[global] Instance Objective_proper {I PROP} :
  Proper ((≡) ==> (↔)) (@Objective I PROP).
Proof.
  intros P1 P2 HP. split=>? i j.
  - by rewrite -HP.
  - rewrite HP. exact: objective_at.
Qed.

Section proofmode_monpred.
  Context {I : biIndex} {PROP : bi}.
  Implicit Types (P : PROP) (i : I).
  #[local] Notation MakeMonPredAt := (MakeMonPredAt (PROP:=PROP)).

  #[global] Instance make_monPred_at_only_provable φ i :
    MakeMonPredAt i [|φ|] [|φ|].
  Proof. rewrite /MakeMonPredAt. by rewrite monPred_at_only_provable. Qed.
End proofmode_monpred.
