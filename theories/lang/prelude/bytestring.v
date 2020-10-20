(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From stdpp Require Import countable strings.

Set Primitive Projections.
Set Default Proof Using "Type".

(** bytes *)
Instance byte_inhabited : Inhabited Byte.byte := populate Byte.x00.
Instance byte_dec : EqDecision Byte.byte := Byte.byte_eq_dec.

Instance byte_countable : Countable Byte.byte.
Proof.
  apply (inj_countable Byte.to_N Byte.of_N).
  abstract (by intros []).
Defined.


Definition byte_parse (b : Byte.byte) : Byte.byte := b.
Definition byte_print (b : Byte.byte) : Byte.byte := b.

Delimit Scope byte_scope with byte.
String Notation Byte.byte byte_parse byte_print : byte_scope.

Bind Scope byte_scope with Byte.byte.

(** bytestrings *)
(** Many functions on byte strings are meant to be always used
qualified, as they conflict with similar functions from [List] or [String].

All such functions are collected in a module [BS], which is not meant
to be imported, as it defines names like [t].
*)
Module Import BS.
  Inductive t : Set :=
  | EmptyString
  | String (_ : Byte.byte) (_ : t).

  Fixpoint print (b : t) : list Byte.byte :=
    match b with
    | EmptyString => nil
    | String b bs => b :: print bs
    end.

  Fixpoint parse (b : list Byte.byte) : t :=
    match b with
    | nil => EmptyString
    | b :: bs => String b (parse bs)
    end.

  Lemma print_parse_inv:
    ∀ x : BS.t, BS.parse (BS.print x) = x.
  Proof.
    induction x; simpl; intros; auto.
    f_equal; auto.
  Qed.

  Instance t_dec : EqDecision t.
  Proof. solve_decision. Defined.

  (** Module [Bytestring_notations] is exported below, and contains
  definitions that can be safely exported. *)
  Module Import Bytestring_notations.
    Definition bs := BS.t.

    Declare Scope bs_scope.
    Delimit Scope bs_scope with bs.
    Bind Scope bs_scope with bs.

    Local Fixpoint append (x y : bs) : bs :=
      match x with
      | BS.EmptyString => y
      | BS.String x xs => BS.String x (append xs y)
      end.

    Notation "x ++ y" := (append x y) : bs_scope.

    String Notation BS.t BS.parse BS.print : bs_scope.

    Instance bytestring_inhabited : Inhabited bs := populate ""%bs.
    Instance bytestring_countable : Countable bs.
    Proof.
      apply (inj_countable' BS.print BS.parse),
        BS.print_parse_inv.
    Defined.
  End Bytestring_notations.
  Notation append := Bytestring_notations.append.

  Fixpoint to_string (b : bs) : string :=
    match b with
    | EmptyString => String.EmptyString
    | String x xs => String.String (Ascii.ascii_of_byte x) (to_string xs)
    end.

  Fixpoint of_string (b : string) : bs :=
    match b with
    | String.EmptyString => ""
    | String.String x xs => String (Ascii.byte_of_ascii x) (of_string xs)
    end%bs.

  Fixpoint rev (acc s : bs) : bs :=
    match s with
    | EmptyString => acc
    | String s ss => rev (String s acc) ss
    end.

  Fixpoint prefix (s1 s2 : bs) {struct s1} : bool :=
    match s1 with
    | EmptyString => true
    | String x xs =>
      match s2 with
      | EmptyString => false
      | String y ys =>
        if decide (x = y) then prefix xs ys
        else false
      end
    end%bs.

  Fixpoint index (n : nat) (s1 s2 : bs) {struct s2} : option nat :=
    match s2 with
    | EmptyString =>
        match n with
        | 0 => match s1 with
              | "" => Some 0
              | String _ _ => None
              end
        | S _ => None
        end
    | String _ s2' =>
        match n with
        | 0 =>
            if prefix s1 s2
            then Some 0
            else match index 0 s1 s2' with
                | Some n0 => Some (S n0)
                | None => None
                end
        | S n' => match index n' s1 s2' with
                  | Some n0 => Some (S n0)
                  | None => None
                  end
        end
    end%bs.

  Fixpoint length (l : bs) : nat :=
    match l with
    | EmptyString => 0
    | String _ l => S (length l)
    end.

  Fixpoint contains (start: nat) (keys: list bs) (fullname: bs) :bool :=
    match keys with
    | kh::ktl =>
      match index start kh fullname with
      | Some n => contains (n + length kh) ktl fullname
      | None => false
      end
    | [] => true
    end.

  Definition eqb (a b : bs) : bool :=
    if decide (a = b) then true else false.

  Definition byte_cmp (a b : Byte.byte) : comparison :=
    N.compare (Byte.to_N a) (Byte.to_N b).

  Lemma to_N_inj : forall x y, Byte.to_N x = Byte.to_N y <-> x = y.
  Proof.
    split.
    2: destruct 1; reflexivity.
    intros.
    assert (Some x = Some y).
    { do 2 rewrite <- Byte.of_to_N.
      destruct H. reflexivity. }
    injection H0. auto.
  Qed.
End BS.
Export Bytestring_notations.

(** comparison *)
Require Import Coq.Structures.OrderedType.

Module OT_byte <: OrderedType.OrderedType with Definition t := Byte.byte.
  Definition t := Byte.byte.
  Definition eq := fun l r => byte_cmp l r = Eq.
  Definition lt := fun l r => byte_cmp l r = Lt.
  Theorem eq_refl : ∀ x : t, eq x x.
  Proof.
    intros; apply N.compare_refl.
  Qed.
  Theorem eq_sym : ∀ x y : t, eq x y → eq y x.
  Proof.
    intros. eapply N.compare_eq in H. red. unfold byte_cmp.
    destruct H. apply eq_refl.
  Qed.
  Theorem eq_trans : ∀ x y z : t, eq x y → eq y z → eq x z.
  Proof.
    intros. eapply N.compare_eq in H. eapply N.compare_eq in H0.
    red. unfold byte_cmp.
    destruct H. destruct H0. apply eq_refl.
  Qed.
  Theorem lt_trans : ∀ x y z : t, lt x y → lt y z → lt x z.
  Proof.
    unfold lt, byte_cmp.
    intros.
    rewrite ->N.compare_lt_iff in H.
    rewrite ->N.compare_lt_iff in H0.
    rewrite N.compare_lt_iff.
    lia.
  Qed.
  Theorem lt_not_eq : ∀ x y : t, lt x y → ¬ eq x y.
  Proof.
    unfold lt, eq, byte_cmp; intros.
    rewrite ->N.compare_lt_iff in H.
    rewrite N.compare_eq_iff.
    lia.
  Qed.
  Definition compare (x y : t) : OrderedType.Compare lt eq x y.
    refine  (
    match byte_cmp x y as X return byte_cmp x y = X -> OrderedType.Compare lt eq x y  with
    | Eq => fun pf => OrderedType.EQ pf
    | Lt => fun pf => OrderedType.LT pf
    | Gt => fun pf => OrderedType.GT _
    end (Logic.eq_refl)).
    unfold lt, byte_cmp.
    abstract (rewrite N.compare_antisym; apply CompOpp_iff, pf).
  Defined.

  Definition eq_dec : ∀ x y : t, {eq x y} + {¬ eq x y}.
  Proof.
  unfold eq.
  refine (fun x y =>
      match byte_cmp x y as Z return byte_cmp x y = Z -> _ with
      | Eq => fun pf => left pf
      | _ => fun _ => right _
      end Logic.eq_refl);
  abstract congruence.
  Defined.

End OT_byte.

Fixpoint bs_cmp (xs ys : bs) : comparison :=
  match xs , ys with
  | BS.EmptyString , BS.EmptyString => Eq
  | BS.EmptyString , _ => Lt
  | _ , BS.EmptyString => Gt
  | BS.String x xs , BS.String y ys =>
    match byte_cmp x y with
    | Eq => bs_cmp xs ys
    | x => x
    end
  end%bs.

Lemma byte_cmp_refl : forall a, byte_cmp a a = Eq.
Proof. intros. apply N.compare_refl. Qed.

Theorem byte_cmp_spec : forall x y, CompareSpec (x = y) (OT_byte.lt x y) (OT_byte.lt y x) (byte_cmp x y).
Proof.
  intros. unfold byte_cmp.
  unfold OT_byte.lt, byte_cmp.
  destruct (N.compare_spec (Byte.to_N x) (Byte.to_N y)); constructor; auto.
  apply to_N_inj. assumption.
Qed.


Module OT_bs <: OrderedType.OrderedType with Definition t := bs.
  Definition t := bs.
  Definition eq := @eq bs.
  Definition lt := fun l r => bs_cmp l r = Lt.

  Theorem lm : forall x y, CompareSpec (x = y) (lt x y) (lt y x) (bs_cmp x y).
  Proof.
    induction x; destruct y; simpl.
    - constructor; reflexivity.
    - constructor. reflexivity.
    - constructor. reflexivity.
    - unfold lt; simpl.
      destruct (byte_cmp_spec b b0); simpl.
      + subst. destruct (IHx y); constructor; eauto.
        congruence.
        destruct (byte_cmp_spec b0 b0); try congruence.
        red in H0. rewrite OT_byte.eq_refl in H0. congruence.
      + constructor; auto.
      + red in H. rewrite H. constructor; auto.
  Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y.
  Proof.
    refine  (
    match bs_cmp x y as X return bs_cmp x y = X -> OrderedType.Compare lt eq x y  with
    | Eq => fun pf => OrderedType.EQ _
    | Lt => fun pf => OrderedType.LT pf
    | Gt => fun pf => OrderedType.GT _
    end (Logic.eq_refl));
    abstract (generalize (lm x y); rewrite pf; inversion 1; auto).
  Defined.

  Theorem eq_refl : ∀ x : t, eq x x.
  Proof.
    reflexivity.
  Qed.
  Theorem eq_sym : ∀ x y : t, eq x y → eq y x.
  Proof.
    eapply eq_sym.
  Qed.
  Theorem eq_trans : ∀ x y z : t, eq x y → eq y z → eq x z.
  Proof.
    eapply eq_trans.
  Qed.
  Theorem lt_trans : ∀ x y z : t, lt x y → lt y z → lt x z.
  Proof.
    unfold lt.
    induction x; destruct y; simpl; try congruence.
    - destruct z; congruence.
    - destruct (byte_cmp_spec b b0); subst.
      + destruct z; auto.
        destruct (byte_cmp b0 b); auto.
        eauto.
      + destruct z; auto.
        red in H.
        destruct (byte_cmp b0 b1) eqn:?.
        * generalize (byte_cmp_spec b0 b1).
          rewrite Heqc. inversion 1.
          subst. rewrite H. auto.
        * generalize (OT_byte.lt_trans _ _ _ H Heqc). unfold OT_byte.lt.
          intro X; rewrite X. auto.
        * congruence.
      + congruence.
  Qed.
  Theorem lt_not_eq : ∀ x y : t, lt x y → ¬ eq x y.
  Proof.
    unfold lt, eq.
    intros. intro. subst.
    induction y; simpl in *; try congruence.
    rewrite ->byte_cmp_refl in *. auto.
  Qed.

  Definition eq_dec : ∀ x y : t, {eq x y} + {¬ eq x y}.
  refine (fun x y =>
      match bs_cmp x y as Z return CompareSpec _ _ _ Z -> _ with
      | Eq => fun pf => left _
      | _ => fun pf => right _
      end (lm x y)).
  - abstract (inversion pf; auto).
  - abstract (apply lt_not_eq; inversion pf; auto).
  - abstract (inversion_clear pf as [ | |?%lt_not_eq]; naive_solver).
  Defined.

End OT_bs.
