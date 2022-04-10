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

(** ** Discrete BI indices and discrete BI index elements *)
(**
We might eventually need to generalize from Leibniz equality to setoid
equivalence. Should that happen, we might want to (in stdpp),
generalize so as to use the same typeclasses for these things and
Iris' [Discrete], [OfeDiscrete].
*)

Class BiIndexElementDiscrete {I : biIndex} (i : I) : Prop :=
  bi_index_element_discrete i' : i ⊑ i' → i = i'.
#[global] Hint Mode BiIndexElementDiscrete + ! : typeclass_instances.
#[global] Hint Opaque BiIndexElementDiscrete : typeclass_instances.
#[global] Instance: Params (@BiIndexElementDiscrete) 1 := {}.
#[global] Instance: Params (@bi_index_element_discrete) 4 := {}.
#[global] Arguments bi_index_element_discrete {_} _ {_} _ _ : assert.

Class BiIndexDiscrete (I : biIndex) : Prop :=
  bi_index_discrete (i : I) :> BiIndexElementDiscrete i.
#[global] Hint Mode BiIndexDiscrete ! : typelcass_instances.

Section bi_index_discrete.
  Context {I : biIndex}.
  Implicit Type i : I.

  #[global] Instance BiIndexElementDiscrete_mono :
    Proper ((⊑) ==> impl) (@BiIndexElementDiscrete I).
  Proof.
    intros i1 i2 Hi ? i' Hi'.
    generalize (bi_index_element_discrete _ _ Hi). intros ->.
    by apply bi_index_element_discrete.
  Qed.
  #[global] Instance BiIndexElementDiscrete_flip_mono :
    Proper (flip (⊑) ==> flip impl) (@BiIndexElementDiscrete I).
  Proof. repeat intro. exact: BiIndexElementDiscrete_mono. Qed.

  Lemma bi_index_element_discrete_iff i `{!BiIndexElementDiscrete i} i' :
    i ⊑ i' ↔ i = i'.
  Proof. split. by apply bi_index_element_discrete. by move=>->. Qed.

  (**
  Setting aside typeclass resolution hints, these two are equivalent.
  *)
  Lemma subrelation_bi_index_discrete :
    @subrelation I (⊑) (=) ↔ BiIndexDiscrete I.
  Proof. done. Qed.
End bi_index_discrete.
