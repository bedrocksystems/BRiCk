(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From stdpp Require Import countable strings namespaces.
Require Export bedrock.prelude.bytestring_core.

#[local] Set Default Proof Using "Type".

(** Bytestring extensions. Integrate with stdpp and strings. *)
(** bytes *)
#[global] Instance byte_inhabited : Inhabited Byte.byte := populate Byte.x00.
#[global] Instance byte_eq_dec : EqDecision Byte.byte := Byte.byte_eq_dec.

#[deprecated(since="2021-09-21", note="Use [byte_eq_dec]")]
Notation byte_dec := byte_eq_dec.

#[global] Instance byte_countable : Countable Byte.byte.
Proof.
  apply (inj_countable Byte.to_N Byte.of_N).
  abstract (by intros []).
Defined.

#[global] Instance bytestring_eq_dec : EqDecision bs := BS.eq_dec.

#[global] Instance bytestring_inhabited : Inhabited bs := populate ""%bs.
#[global] Instance bytestring_countable : Countable bs.
Proof.
  apply (inj_countable' BS.print BS.parse),
    BS.print_parse_inv.
Defined.


(** bytestrings *)
(** Many functions on byte strings are meant to be always used
qualified, as they conflict with similar functions from [List] or [String].

All such functions are collected in a module [BS], which is not meant
to be imported, as it defines names like [t].
*)
Module Import BS.
  Export bytestring_core.BS.

  Fixpoint to_string (b : bs) : string :=
    match b with
    | BS.EmptyString => String.EmptyString
    | BS.String x xs => String.String (Ascii.ascii_of_byte x) (to_string xs)
    end.

  Fixpoint of_string (b : string) : bs :=
    match b with
    | String.EmptyString => ""
    | String.String x xs => String (Ascii.byte_of_ascii x) (of_string xs)
    end%bs.

  Lemma of_string_to_string_inv :
    forall (b : bs),
      of_string (to_string b) = b.
  Proof.
    intros *; induction b as [| a b' IHb']; simpl.
    - by reflexivity.
    - by rewrite IHb', Ascii.byte_of_ascii_of_byte.
  Qed.

  Lemma to_string_of_string_inv :
    forall (b : string),
      to_string (of_string b) = b.
  Proof.
    intros *; induction b as [| a b' IHb']; simpl.
    - by reflexivity.
    - by rewrite IHb', Ascii.ascii_of_byte_of_ascii.
  Qed.

  #[deprecated(since="2021-09-21", note="Use [decide (arg1 = arg2)]")]
  Notation t_dec := bytestring_eq_dec.

  (* [sepBy sep ls] concatenates the elements in [ls] using
    the separator [sep] *)
  Fixpoint sepBy (sep : bs) (ls : list bs) : bs :=
    match ls with
    | nil => ""
    | l :: nil => l
    | l :: ls => l ++ sep ++ sepBy sep ls
    end.

  Fixpoint take (n : nat) (acc b : bs) : bs * bs :=
    match n with
    | 0 => (BS.rev BS.EmptyString acc, b)
    | S n => match b with
            | BS.String x y => take n (BS.String x acc) y
            | BS.EmptyString => (BS.rev BS.EmptyString acc, b)
            end
    end.

  Fixpoint drop (n : nat) (b : bs) : bs :=
    match n with
    | 0 => b
    | S n => match b with
            | BS.String _ b => drop n b
            | _ => b
            end
    end.

  Fixpoint last (b : bs) (o : option Byte.byte) : option Byte.byte :=
    match b with
    | BS.EmptyString => o
    | BS.String s b => last b (Some s)
    end.
End BS.

(* stdpp-specific. *)
Notation "N .@@ x" := (ndot (A := bs) N x%bs)
  (at level 19, left associativity, format "N .@@ x") : stdpp_scope.
Notation "(.@@)" := (ndot (A := bs)) (only parsing) : stdpp_scope.

(* [sepBy sep ls] concatenates the elements in [ls] using
   the separator [sep] *)
Fixpoint sepBy (b : bs) (ls : list bs) : bs :=
  match ls with
  | nil => ""
  | l :: ls =>
    match ls with
    | nil => l
    | _ :: _ => l ++ b ++ sepBy b ls
    end
  end.
