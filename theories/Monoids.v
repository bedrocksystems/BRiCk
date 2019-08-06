Require Import Coq.Classes.DecidableClass.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qcanon.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.micromega.Lqa.

Require Import Cpp.Sem.CCLogic.

Module Ex.
  Variant _Ex (A : Type) : Type :=
  | ExElem (x : A)
  | ExEmpty
  | ExUndef
  .

  Arguments ExElem {_} _.
  Arguments ExEmpty {_}.
  Arguments ExUndef {_}.

  Definition ex_compose {A} (x y : _Ex A) :=
    match x, y with
    | ExUndef, _ => ExUndef
    | _, ExUndef => ExUndef
    | ExElem _, ExElem _ => ExUndef
    | ExEmpty, ExEmpty => ExEmpty
    | ExElem x', ExEmpty => ExElem x'
    | ExEmpty, ExElem y' => ExElem y'
    end.

  Local Obligation Tactic :=
    intros;
      repeat match goal with x : _Ex _ |- _ => destruct x end;
      cbn in *;
      auto || congruence.

  Program Definition t (A : Type) : PCM :=
    {| p_type := _Ex A;
       p_bot := ExEmpty;
       p_undef := ExUndef;
       p_compose := ex_compose;
    |}.
End Ex.
Definition Ex := Ex.t.

Module Ag.
  Variant _Ag (A : Type) : Type :=
  | AgElem (x : A)
  | AgEmpty
  | AgUndef
  .

  Arguments AgElem {_} _.
  Arguments AgEmpty {_}.
  Arguments AgUndef {_}.

  Definition ag_compose {A} `{forall x y : A, Decidable (x = y)} (x y : _Ag A) :=
    match x, y with
    | AgUndef, _ => AgUndef
    | _, AgUndef => AgUndef
    | AgEmpty, AgEmpty => AgEmpty
    | AgElem x', AgEmpty => AgElem x'
    | AgEmpty, AgElem y' => AgElem y'
    | AgElem x', AgElem y' =>
      if decide (x' = y')
      then AgElem x'
      else AgUndef
    end.

  Local Obligation Tactic :=
    unfold ag_compose;
      intros;
      repeat match goal with x : _Ag _ |- _ => destruct x end;
      auto;
      cbn;
      repeat match goal with
             | |- context[decide ?P] =>
               let H := fresh in
               destruct (decide P) eqn:H;
                 [ apply Decidable_sound in H | apply Decidable_complete_alt in H ]
             | _ : context[decide ?P] |- _ =>
               let H := fresh in
               destruct (decide P) eqn:H;
                 [ apply Decidable_sound in H | apply Decidable_complete_alt in H ]
             end;
      subst;
      cbn;
      congruence.

  Program Definition t (A : Type) `{forall x y : A, Decidable (x = y)} : PCM :=
    {| p_type := _Ag A;
       p_bot := AgEmpty;
       p_undef := AgUndef;
       p_compose := ag_compose;
    |}.
End Ag.
Definition Ag := Ag.t.

Notation "x < y <= z" := (x < y /\ y <= z) : Qc_scope.

Module Frac.
  Local Definition ok (q : Qc) : Prop :=
    match Qccompare 0 q, Qccompare q 1 with
    | Gt, _
    | Eq, _
    | _, Gt => False
    | _, _ => True
    end.

  Variant _Frac (A : Type) : Type :=
  | FracElem (q : Qc) (bound : ok q) (x : A)
  | FracUnit
  | FracUndef
  .

  Arguments FracElem {_} _ _ _.
  Arguments FracUnit {_}.
  Arguments FracUndef {_}.

  Local Ltac qify :=
    repeat match goal with
           | [ q : Qc |- _ ] => destruct q as [q ?]
           end;
    cbv [Qcle Qclt Q2Qc Qcanon.this Qcplus] in *;
    rewrite ?Qred_correct in *.

  Lemma ok_prop : forall q, ok q <-> 0 < q <= 1.
  Proof.
    intros q.
    unfold ok, Qccompare.
    destruct (Qcompare_spec 0%Qc q), (Qcompare_spec q 1%Qc);
      intuition (qify; lra).
  Qed.

  Definition is_ok q : {ok q} + {~ok q}.
    unfold ok.
    destruct (0 ?= q), (q ?= 1);
      solve [ left; trivial | right; tauto ].
  Defined.

  Lemma ok_irr : forall q (pf1 pf2 : ok q), pf1 = pf2.
  Proof.
    unfold ok. intros.
    destruct (0 ?= q), (q ?= 1);
      intuition;
      destruct pf1;
      destruct pf2;
      auto.
  Qed.

  Definition Frac_full {A} (x : A) : _Frac A :=
    FracElem 1 ltac:(cbv; auto) x.

  Lemma FracElem_eq : forall A p q pok qok (x y : A),
      p = q ->
      x = y ->
      FracElem p pok x = FracElem q qok y.
  Proof.
    intros * -> ->.
    f_equal.
    apply ok_irr.
  Qed.

  Definition Frac_compose {A} `{forall x y : A, Decidable (x = y)} f g :=
    match f, g with
    | FracUndef, _ => FracUndef
    | _, FracUndef => FracUndef
    | FracUnit, _ => g
    | _, FracUnit => f
    | FracElem p _ x, FracElem q _ y =>
      if decide (x = y)
      then match is_ok (p + q) with
           | left pf => FracElem (p + q) pf x
           | right _ => FracUndef
           end
      else FracUndef
    end.

  Lemma decide_eq_same : forall A (x y : A) `(Decidable (x = y)) `(Decidable (y = x)),
      decide (x = y) = decide (y = x).
  Proof.
    intros ??? [[] ?] [[] ?];
      cbn;
      intuition.
  Qed.

  Lemma decide_spec : forall P `(Decidable P), reflect P (decide P).
    intros ? [[] ?];
      [ apply ReflectT | apply ReflectF ];
      intuition.
  Defined.

  Lemma Frac_compose_com : forall A `{forall x y : A, Decidable (x = y)} s1 s2,
      Frac_compose s1 s2 = Frac_compose s2 s1.
  Proof.
    destruct s1, s2; cbn; auto.
    rewrite (decide_eq_same _ x x0 (H x x0) (H x0 x)), Qcplus_comm.
    destruct (decide_spec (x0 = x) (H x0 x)); subst; auto.
  Qed.

  Lemma Frac_compose_assoc : forall A `{forall x y : A, Decidable (x = y)} s1 s2 s3,
      Frac_compose (Frac_compose s1 s2) s3 = Frac_compose s1 (Frac_compose s2 s3).
  Proof.
    destruct s1, s2, s3; cbn; auto;
      repeat match goal with
             | |- _ => eapply FracElem_eq
             | |- FracElem _ _ _ = FracUndef => exfalso
             | |- FracUndef = FracElem _ _ _ => exfalso
             | |- context [ decide (?x = ?y) ] => destruct (decide_spec (x = y) (H x y)); subst
             | |- context [ is_ok ?q ] => destruct (is_ok q)
             | H : ok _ |- _ => eapply ok_prop in H
             | H : ~ok _ |- False => eapply H; eapply ok_prop; qify; lra
             | |- _ => ring
             | |- _ => progress cbn
             | |- _ => progress intuition
             end.
  Qed.

  Lemma Frac_compose_bot : forall A `{forall x y : A, Decidable (x = y)} s1 s2,
      Frac_compose s1 s2 = FracUnit ->
      s1 = FracUnit /\ s2 = FracUnit.
  Proof.
    destruct s1, s2; cbn; intuition;
      repeat match goal with
             | _ : context[match ?E with _ => _ end] |- _ => destruct E
             end;
      discriminate.
  Qed.

  Lemma Frac_compose_w_bot : forall A `{forall x y : A, Decidable (x = y)} s,
      Frac_compose s FracUnit = s.
  Proof.
    destruct s; auto.
  Qed.

  Lemma Frac_compose_w_undef : forall A `{forall x y : A, Decidable (x = y)} s,
      Frac_compose s FracUndef = FracUndef.
  Proof.
    destruct s; auto.
  Qed.

  Definition t (A : Type) `{forall x y : A, Decidable (x = y)} : PCM :=
    {| p_type := _Frac A
     ; p_bot := FracUnit
     ; p_undef := FracUndef
     ; p_compose := Frac_compose
     ; p_compose_com := Frac_compose_com A
     ; p_compose_assoc := Frac_compose_assoc A
     ; p_compose_bot := Frac_compose_bot A
     ; p_compose_w_bot := Frac_compose_w_bot A
     ; p_compose_w_undef := Frac_compose_w_undef A
    |}.
End Frac.
Definition Frac := Frac.t.
