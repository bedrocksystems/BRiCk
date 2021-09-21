(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From Coq Require Import Lists.List NArith Structures.OrderedType micromega.Lia.
From Coq Require Strings.Byte.
Import ListNotations.

(** Bytestring core definitions. Depends only on the stdlib, and could in
principle be upstreamed. *)
#[local] Set Default Proof Using "Type".

Definition byte_parse (b : Byte.byte) : Byte.byte := b.
Definition byte_print (b : Byte.byte) : Byte.byte := b.

(** comparison *)
Definition byte_cmp (a b : Byte.byte) : comparison :=
  N.compare (Byte.to_N a) (Byte.to_N b).

Delimit Scope byte_scope with byte.
String Notation Byte.byte byte_parse byte_print : byte_scope.

Bind Scope byte_scope with Byte.byte.

Lemma byte_cmp_refl a : byte_cmp a a = Eq.
Proof. intros. apply N.compare_refl. Qed.

Lemma byte_to_N_inj x y : Byte.to_N x = Byte.to_N y <-> x = y.
Proof.
  split. 2: now intros ->.
  intros Heq.
  enough (Some x = Some y) as [= ->] by easy.
  do 2 rewrite <- Byte.of_to_N.
  now rewrite Heq.
Qed.

Module OT_byte <: OrderedType.OrderedType with Definition t := Byte.byte.
  Definition t := Byte.byte.
  Definition eq := fun l r => byte_cmp l r = Eq.
  Definition lt := fun l r => byte_cmp l r = Lt.
  Theorem eq_refl (x : t) : eq x x.
  Proof.
    intros; apply N.compare_refl.
  Qed.
  Theorem eq_sym (x y : t) : eq x y -> eq y x.
  Proof.
    intros Hxy. eapply N.compare_eq in Hxy. unfold eq, byte_cmp.
    rewrite Hxy. apply eq_refl.
  Qed.
  Theorem eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof.
    intros Hxy Hyz. eapply N.compare_eq in Hxy. eapply N.compare_eq in Hyz.
    unfold eq, byte_cmp. rewrite -> Hxy, Hyz.
    apply eq_refl.
  Qed.
  Theorem lt_trans (x y z : t) : lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt, byte_cmp. rewrite ->!N.compare_lt_iff.
    lia.
  Qed.
  Theorem lt_not_eq (x y : t) : lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq, byte_cmp. rewrite ->N.compare_lt_iff, N.compare_eq_iff.
    lia.
  Qed.
  Definition compare (x y : t) : OrderedType.Compare lt eq x y.
  Proof.
    refine (match byte_cmp x y as X return byte_cmp x y = X -> OrderedType.Compare lt eq x y with
      | Eq => fun pf => OrderedType.EQ pf
      | Lt => fun pf => OrderedType.LT pf
      | Gt => fun pf => OrderedType.GT _
      end Logic.eq_refl).
    unfold lt, byte_cmp.
    abstract (rewrite N.compare_antisym; apply CompOpp_iff, pf).
  Defined.

  Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
  Proof.
    refine (match byte_cmp x y as Z return byte_cmp x y = Z -> _ with
        | Eq => fun pf => left pf
        | _ => fun _ => right _
        end Logic.eq_refl);
    abstract congruence.
  Defined.
End OT_byte.

Theorem byte_cmp_spec x y : CompareSpec (x = y) (OT_byte.lt x y) (OT_byte.lt y x) (byte_cmp x y).
Proof.
  unfold byte_cmp, OT_byte.lt, byte_cmp.
  destruct (N.compare_spec (Byte.to_N x) (Byte.to_N y)); constructor; auto.
  apply byte_to_N_inj. assumption.
Qed.

(** bytestrings *)
(** Many functions on byte strings are meant to be always used
qualified, as they conflict with similar functions from [List] or [String].

All such functions are collected in a module [BS], which serves as a namespace:
that is, it is not meant to be imported by clients.
*)

Module Import BS.
  Inductive t : Set :=
  | EmptyString
  | String (_ : Byte.byte) (_ : t).

  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
  Proof. decide equality. apply Byte.byte_eq_dec. Defined.

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

  Lemma print_parse_inv (x : t) :
    parse (print x) = x.
  Proof.
    induction x; simpl; intros; auto.
    f_equal; auto.
  Qed.

  Lemma parse_print_inv (x : list Byte.byte) :
    print (parse x) = x.
  Proof.
    induction x; simpl; intros; auto.
    f_equal; auto.
  Qed.

  Fixpoint append (x y : t) : t :=
    match x with
    | EmptyString => y
    | String x xs => String x (append xs y)
    end.

  (** Module [Bytestring_notations] is exported below, and contains
  notations that can be safely exported. *)
  Module Import Bytestring_notations.
    Notation bs := BS.t.

    Declare Scope bs_scope.
    Delimit Scope bs_scope with bs.
    Bind Scope bs_scope with bs.

    Notation "x ++ y" := (append x y) : bs_scope.

    String Notation bs BS.parse BS.print : bs_scope.
  End Bytestring_notations.

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
        if Byte.byte_eq_dec x y then prefix xs ys
        else false
      end
    end.

  (** [substring n m s] returns the substring of [s] that starts
      at position [n] and of length [m];
      if this does not make sense it returns [""] *)
  Fixpoint substring (n m : nat) (s : bs) : bs :=
    match n, m, s with
    | O,    O,    _              => BS.EmptyString
    | O,    S m', BS.EmptyString => s
    | O,    S m', BS.String c s' => BS.String c (substring 0 m' s')
    | S n', _,    BS.EmptyString => s
    | S n', _,    BS.String c s' => substring n' m s'
    end.

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

  Lemma print_length (s : bs) :
    List.length (print s) = length s.
  Proof.
    induction s; simpl.
    - easy.
    - now rewrite IHs.
  Qed.

  Fixpoint contains (start : nat) (keys : list bs) (fullname : bs) :bool :=
    match keys with
    | kh::ktl =>
      match index start kh fullname with
      | Some n => contains (n + length kh) ktl fullname
      | None => false
      end
    | [] => true
    end.

  Definition eqb (a b : bs) : bool :=
    if eq_dec a b then true else false.

  #[deprecated(since="2021-09-21", note="Use [byte_to_N_inj]")]
  Notation to_N_inj := byte_to_N_inj.
End BS.
Export Bytestring_notations.

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

Module OT_bs <: OrderedType.OrderedType with Definition t := bs.
  Definition t := bs.
  Definition eq := @eq bs.
  Definition lt := fun l r => bs_cmp l r = Lt.

  Theorem lm x y : CompareSpec (x = y) (lt x y) (lt y x) (bs_cmp x y).
  Proof.
    revert y; induction x; destruct y; simpl.
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
    refine (
      match bs_cmp x y as X return bs_cmp x y = X -> OrderedType.Compare lt eq x y  with
      | Eq => fun pf => OrderedType.EQ _
      | Lt => fun pf => OrderedType.LT pf
      | Gt => fun pf => OrderedType.GT _
      end (Logic.eq_refl));
    abstract (generalize (lm x y); rewrite pf; inversion 1; auto).
  Defined.

  Theorem eq_refl (x : t) : eq x x.
  Proof. reflexivity. Qed.
  Theorem eq_sym (x y : t) : eq x y -> eq y x.
  Proof. eapply eq_sym. Qed.
  Theorem eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof. eapply eq_trans. Qed.
  Theorem lt_trans (x y z : t) : lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    revert y z.
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
  Theorem lt_not_eq (x y : t) : lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq.
    intros Heq ->.
    induction y; simpl in *; try congruence.
    rewrite ->byte_cmp_refl in Heq. auto.
  Qed.

  Definition eq_dec := BS.eq_dec.
End OT_bs.
