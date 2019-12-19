(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Coq.Classes Require Import
     RelationClasses Morphisms.

From iris.base_logic.lib Require Export iprop.
From iris.bi.lib Require Import fractional.
From Cpp Require Export IrisBridge.
Export ChargeNotation.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Semantics Operator.

Module Type logic.

  Section with_Σ.
    Context {Σ : gFunctors}.

    Definition mpred := iProp Σ.
    Canonical Structure mpredI : bi :=
      {| bi_car := mpred
       ; bi_ofe_mixin := (iPropI Σ).(bi_ofe_mixin)
       ; bi_bi_mixin := (iPropI Σ).(bi_bi_mixin) |}.
    (* todo: Fix the warning generated from this definition *)
    Canonical Structure mpredSI : sbi :=
      {| sbi_car := mpred
       ; sbi_ofe_mixin := (iPropI Σ).(bi_ofe_mixin)
       ; sbi_bi_mixin := (iPropI Σ).(bi_bi_mixin)
       ; sbi_sbi_mixin := (iPropSI Σ).(sbi_sbi_mixin) |}.

    Global Instance later_entails : Proper ((lentails) ==> (lentails)) (@sbi_later mpredSI).
    Proof.
      intros H H1 Hent.
      f_equiv. eauto.
    Qed.

    Parameter with_genv : (genv -> mpred) -> mpred.
    Axiom with_genv_single : forall f g,
        with_genv f //\\ with_genv g -|- with_genv (fun r => f r //\\ g r).
    Axiom with_genv_single_sep : forall f g,
        with_genv f ** with_genv g -|- with_genv (fun r => f r ** g r).

    Axiom with_genv_mono : forall (P Q : genv -> mpred),
        (forall x, P x |-- Q x) ->
        with_genv P |-- with_genv Q.

    Axiom with_genv_ignore_pred : forall P,
        Forall x, P x |-- with_genv P.
    Lemma with_genv_ignore_only_provable : forall (P : _ -> Prop),
        [| forall x, P x |] |-- with_genv (λ x, [| P x |]).
    Proof. intros. rewrite <- with_genv_ignore_pred. eauto. Qed.

    Axiom with_genv_ignore1 : forall P,
        with_genv (fun _ => P) |-- P.
    Lemma with_genv_ignore2 P :
        P |-- with_genv (fun _ => P).
    Proof. rewrite <- with_genv_ignore_pred. eauto. Qed.
    Lemma with_genv_ignore P :
        with_genv (fun _ => P) -|- P.
    Proof. split'. apply with_genv_ignore1. apply with_genv_ignore2. Qed.

    Instance Proper_with_genv_lentails :
      Proper (pointwise_relation _ lentails ==> lentails) with_genv.
    Proof. intros P Q HPQ. by apply with_genv_mono. Qed.

    Instance Proper_with_genv_lequiv :
      Proper (pointwise_relation _ lequiv ==> lequiv) with_genv.
    Proof. intros P Q HPQ. split'; apply with_genv_mono; intros; by rewrite HPQ. Qed.

    Global Declare Instance with_genv_persistent P :
      (forall resolve, Persistent (P resolve)) -> Persistent (with_genv P).

    (* heap points to *)
    (* note(gmm): this needs to support fractional permissions and other features *)
    Parameter tptsto : type -> Qp -> forall addr value : val, mpred.

    Global Declare Instance tptsto_timeless ty q a v : Timeless (tptsto ty q a v).
    Global Declare Instance tptsto_fractional ty a v : Fractional (λ q, tptsto ty q a v).
    Global Declare Instance tptsto_as_fractional ty q a v :
      AsFractional (tptsto ty q a v) (λ q, tptsto ty q a v)%I q.

    Axiom tptsto_has_type : forall t q a v,
        tptsto t q a v |-- tptsto t q a v ** [| has_type v t |].

    Lemma tptsto_split t q1 q2 a v :
        tptsto t (q1+q2) a v -|- tptsto t q1 a v ** tptsto t q2 a v.
    Proof. apply tptsto_fractional. Qed.

    Axiom tptsto_same_val : forall t q1 q2 a v1 v2,
        let p :=
            tptsto t q1 a v1 ** tptsto t q2 a v2 in
        p |-- p ** [| v1=v2 |] ** ([| ((q1+q2)%Qp ≤ 1)%Qc |]).

    (* this is like a "points to" where the location is (region * ident).
     *)
    Parameter local_addr : region -> ident -> ptr -> mpred.

    (* the pointer contains the code *)
    Parameter code_at : Func -> ptr -> mpred.
    (* code_at is freely duplicable *)
    Global Declare Instance code_at_persistent f p : Persistent (code_at f p).
    Lemma code_at_dup f p : code_at f p -|- code_at f p ** code_at f p.
    Proof. apply bi.persistent_sep_dup; apply _. Qed.

    Lemma code_at_drop f p : code_at f p |-- empSP.
    Proof. auto. Qed.

    Parameter ctor_at : ptr -> Ctor -> mpred.
    Parameter dtor_at : ptr -> Dtor -> mpred.

    Definition eval_unop (u : UnOp) (argT resT : type) (arg res : val)
      : mpred :=
      with_genv (fun resolve =>
                   [| eval_unop (resolve:=resolve) u argT resT arg res |]).
    Global Instance Persistent_eval_unop : forall u t t' v v', Persistent (eval_unop u t t' v v').
    Proof. Admitted.
    Global Instance Affine_eval_unop : forall u t t' v v', Affine (eval_unop u t t' v v').
    Proof. Admitted.

    Definition eval_binop (b :BinOp) (lhsT rhsT resT : type) (lhs rhs res : val)
      : mpred :=
      with_genv (fun resolve =>
                   [| eval_binop (resolve:=resolve) b lhsT rhsT resT lhs rhs res |]).
    Global Instance Persistent_eval_binop : forall u t t' t'' v v' v'', Persistent (eval_binop u t t' t'' v v' v'').
    Proof. Admitted.
    Global Instance Affine_eval_binop : forall u t t' t'' v v' v'', Affine (eval_binop u t t' t'' v v' v'').
    Proof. Admitted.


    Definition sizeof (t : type) (sz : N) : mpred :=
      with_genv (fun resolve => [| size_of resolve t sz |]).

    Global Instance Persistent_sizeof : forall t s, Persistent (sizeof t s).
    Proof. Admitted.
    Global Instance Affine_sizeof : forall t s, Affine (sizeof t s).
    Proof. Admitted.

    Definition alignof (t : type) (sz : N) : mpred :=
      with_genv (fun resolve => [| align_of (resolve:=resolve) t sz |]).

    Global Instance Persistent_alignof : forall t s, Persistent (alignof t s).
    Proof. Admitted.
    Global Instance Affine_alignof : forall t s, Affine (alignof t s).
    Proof. Admitted.

  End with_Σ.
  Arguments mpred _ : clear implicits.
  Arguments mpredI _ : clear implicits.
  Arguments mpredSI _ : clear implicits.

  Existing Instance tptsto_timeless.

End logic.


Declare Module L : logic.

Export L.
