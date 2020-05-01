(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Strings.String.
Require Import stdpp.countable.

Set Primitive Projections.

(** bytes *)
Instance byte_dec : EqDecision Byte.byte := Byte.byte_eq_dec.

Instance byte_countable : Countable Byte.byte.
refine {| encode x := encode (Byte.to_N x)
        ; decode x := Byte.of_N (Pos.pred_N x) |}.
abstract (intros; destruct x; reflexivity).
Defined.


Definition byte_parse (b : Byte.byte) : Byte.byte := b.
Definition byte_print (b : Byte.byte) : Byte.byte := b.

Delimit Scope byte_scope with byte.
String Notation Byte.byte byte_parse byte_print : byte_scope.

Bind Scope byte_scope with Byte.byte.

(** bytestrings *)
Module Bytestring.
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
    ∀ x : Bytestring.t, Bytestring.parse (Bytestring.print x) = x.
  Proof.
    induction x; simpl; intros; auto.
    f_equal; auto.
  Qed.

  Instance t_dec : EqDecision t.
  Proof. solve_decision. Defined.
End Bytestring.

Definition bs := Bytestring.t.

Declare Scope bs_scope.
Delimit Scope bs_scope with bs.
Bind Scope bs_scope with bs.

String Notation Bytestring.t Bytestring.parse Bytestring.print : bs_scope.

Instance bytestring_countable : Countable bs.
refine {| encode x := encode (Bytestring.print x)
        ; decode x := match decode x with
                      | None => None
                      | Some y => Some (Bytestring.parse y)
                      end |}.
{ induction x; simpl.
  - reflexivity.
  - rewrite decode_encode in *. simpl in *.
    injection IHx; intro; subst.
    rewrite Bytestring.print_parse_inv. reflexivity. }
Defined.

Import Bytestring.

Fixpoint append (x y : bs) : bs :=
  match x with
  | Bytestring.EmptyString => y
  | Bytestring.String x xs => Bytestring.String x (append xs y)
  end.

Notation "x ++ y" := (append x y) : bs_scope.

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

Local Fixpoint contains (start: nat) (keys: list bs) (fullname: bs) :bool :=
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
