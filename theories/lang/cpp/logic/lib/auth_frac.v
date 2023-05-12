(**
 * Copyright (C) 2022 BedRock Systems, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import iris.algebra.agree.
Require Import iris.proofmode.proofmode.
Require Import bedrock.lang.bi.spec.frac_splittable.
Require Import bedrock.lang.cpp.logic.
Require Import bedrock.lang.algebra.frac_auth.
Require Import bedrock.lang.cpp.logic.own_instances.
Require Import bedrock.lang.proofmode.own_obs.

Set Printing Coercions.

(**
Well-typed ghost resources:

- [afrac.auth (g : afrac.gname A) (q : Qp) (x : A) : mpred]
represents fractional ownership of ghost cell [g] currently containing
the authoritative state [x]

- [afrac.frag (g : afrac.gname A) (q : Qp) (x : A) : mpred]
represents fractional ownership of ghost cell [g] currently containing
the fragmentative state [x]
*)
Module Type AUTH_FRAC.

  (** CMRA *)

  Parameter G : ∀ (A : Type) (Σ : gFunctors), Set.
  Existing Class G.
  Parameter Σ : ∀ (A : Type), gFunctors.
  #[global] Declare Instance subG {A Σ} : subG (AUTH_FRAC.Σ A) Σ -> G A Σ.

  (** Ghosts *)

  Parameter gname : ∀ (A : Type), Set.

  #[global] Declare Instance gname_inhabited A : Inhabited (gname A).
  #[global] Declare Instance gname_eq_dec A : EqDecision (gname A).
  #[global] Declare Instance gname_countable A : Countable (gname A).

  (** Predicates *)

  Parameter auth : ∀ {A} `{Σ : cpp_logic, !AUTH_FRAC.G A Σ}
    (g : gname A) (q : Qp) (x : A), mpred.
  Parameter frag : ∀ {A} `{Σ : cpp_logic, !AUTH_FRAC.G A Σ}
    (g : gname A) (q : Qp) (x : A), mpred.

  Section properties.
    Context {A} `{Σ : cpp_logic, !AUTH_FRAC.G A Σ}.

    (** Structure *)

    #[global] Declare Instance auth_objective : Objective3 auth.
    #[global] Declare Instance auth_frac g : FracSplittable_1 (auth g).
    #[global] Declare Instance auth_agree g : AgreeF1 (auth g).

    #[global] Declare Instance frag_objective : Objective3 frag.
    #[global] Declare Instance frag_frac g : FracSplittable_1 (frag g).
    #[global] Declare Instance frag_agree g : AgreeF1 (frag g).

    #[global] Declare Instance auth_frag_agree g q1 q2 x1 x2 :
      Observe2 [| x1 = x2 |] (auth g q1 x1) (frag g q2 x2).

    (** Allocation *)

    #[local] Notation OWN g x := (auth g 1 x ** frag g 1 x) (only parsing).

(*  (* Stronger allocation rules may not be needed for now. *)
    Axiom alloc_strong_dep : ∀ (f : gname A -> A) (P : gname A -> Prop),
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** OWN g (f g).

    Axiom alloc_cofinite_dep : ∀ (f : gname A -> A) (G : gset (gname A)),
      |-- |==> Exists g, [| g ∉ G |] ** OWN g (f g).

    Axiom alloc_dep : ∀ (f : gname A -> A),
      |-- |==> Exists g, OWN g (f g).

    Axiom alloc_strong : ∀ (P : gname A -> Prop) x,
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** OWN g x.

    Axiom alloc_cofinite : ∀ (G : gset (gname A)) x,
      |-- |==> Exists g, [| g ∉ G |] ** OWN g x.
*)

    Axiom alloc : ∀ x, |-- |==> Exists g, OWN g x.

    (** Updates *)

    Axiom update : ∀ g x y, |-- auth g 1 x -* frag g 1 x -* |==> OWN g y.

    (** TODO: Automation (generically derivable) *)

  End properties.

End AUTH_FRAC.

(**
TODO: unify with [bedrock.algebra.frac_auth_agree].
*)
Module afrac : AUTH_FRAC.

  (** CMRA *)

  #[local] Notation RA A := (frac_authR (agreeR (leibnizO A))).
  Class G (A : Type) (Σ : gFunctors) : Set := G_inG : inG Σ (RA A).
  #[global] Existing Instance G_inG.
  Definition Σ (A : Type) : gFunctors := #[ GFunctor (RA A) ].
  Lemma subG {A Σ} : subG (afrac.Σ A) Σ -> G A Σ.
  Proof. solve_inG. Qed.

  (** Ghosts *)

  Definition gname (A : Type) : Set := iprop.gname.
  #[local] Instance gname_inhabited A : Inhabited (gname A) := _.
  #[local] Instance gname_eq_dec A : EqDecision (gname A) := _.
  #[local] Instance gname_countable A : Countable (gname A) := _.

  (** Predicates *)

  Section defs.
    Context {A} `{Σ : cpp_logic, !afrac.G A Σ}.

    #[local] Notation to_agree := (to_agree (A:=leibnizO A)).

    Definition auth (g : gname A) (q : Qp) (x : A) : mpred :=
      own g (●F{q} (to_agree x)).

    Definition frag (g : gname A) (q : Qp) (x : A) : mpred :=
      own g (◯F{q} (to_agree x)).

    #[local] Instance auth_objective : Objective3 auth := _.
    #[local] Instance auth_frac g : FracSplittable_1 (auth g).
    Proof. solve_frac. Qed.
    #[local] Instance auth_agree g : AgreeF1 (auth g).
    Proof.
      (**
      TODO (PDS): Shouldn't need to expose [to_agree].
      *)
      intros. rewrite -(inj_iff to_agree). apply _.
    Qed.

    #[local] Instance frag_objective : Objective3 frag := _.
    #[local] Instance frag_frac g : FracSplittable_1 (frag g).
    Proof. solve_frac. Qed.
    #[local] Instance frag_agree g : AgreeF1 (frag g).
    Proof.
      (**
      TODO (PDS): own_frac_auth_frag_frac_agree_L missing in
      bedrock.lang.proofmode.own_obs
      *)
      intros. iIntros "F1 F2".
      iDestruct (own_valid_2 with "F1 F2") as %Hv. iModIntro. iPureIntro.
      move: Hv. rewrite -frac_auth_frag_op frac_auth_frag_valid=>-[] _.
      by rewrite to_agree_op_valid_L.
    Qed.

    #[local] Instance auth_frag_agree g q1 q2 x1 x2 :
      Observe2 [| x1 = x2 |] (auth g q1 x1) (frag g q2 x2).
    Proof.
      (**
      TODO (PDS): Problem with [own_frac_auth_agree_L]
      *)
      intros. iIntros "A F".
      iDestruct (observe_2 [| _ ≼ _ |] with "A F") as %Hinc.
      iModIntro. iPureIntro. move: Hinc.
      move/to_agree_included. by fold_leibniz.
    Qed.

    #[local] Notation OWN g x := (auth g 1 x ** frag g 1 x) (only parsing).

    Lemma alloc x : |-- |==> Exists g, OWN g x.
    Proof.
      iMod (own_alloc (●F{1} (to_agree x) ⋅ ◯F{1} (to_agree x))) as (g) "[A F]".
      { by apply frac_auth_valid. }
      iExists g. by iFrame "A F".
    Qed.

    Lemma update g x y :
      |-- auth g 1 x -* frag g 1 x -* |==> OWN g y.
    Proof.
      iIntros "A F". iMod (own_update_2 with "A F") as "[$$]"; last done.
      by apply frac_auth_update_1.
    Qed.
  End defs.

End afrac.
