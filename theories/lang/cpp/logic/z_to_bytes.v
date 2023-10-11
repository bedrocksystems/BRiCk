(*
 * Copyright (c) 2020-2021,2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.list_numbers.
Require Export bedrock.lang.cpp.arith.z_to_bytes.
Require Import stdpp.numbers.
Require Import bedrock.lang.cpp.arith.types.
Require Import bedrock.lang.cpp.semantics.values.

Section with_σ.
  Context {σ : genv}.

  Lemma _Z_to_bytes_has_type_prop (cnt : nat) (endianness : endian) sign (z : Z) :
    List.Forall (fun (v : N) => has_type_prop (Vn v) Tu8) (_Z_to_bytes cnt endianness sign z).
  Proof.
    eapply List.Forall_impl.
    2: { exact: _Z_to_bytes_range. }
    move => ? /= ?.
    rewrite -has_int_type.
    rewrite/bound/min_val/max_val.
    lia.
  Qed.

  Lemma _Z_from_bytes_unsigned_le_has_type_prop (sz : int_type) :
    forall (bytes : list N),
      lengthN bytes = bytesN sz ->
      has_type_prop (_Z_from_bytes_unsigned_le bytes) (Tnum sz Unsigned).
  Proof.
    intros * Hlength; rewrite -has_int_type/bound/=.
    rewrite /lengthN/bytesN in Hlength; apply Nat2N.inj in Hlength.
    eapply _Z_from_bytes_unsigned_le_bound; rewrite Hlength.
    destruct sz=> /=; lia.
  Qed.

  Lemma _Z_from_bytes_le_has_type_prop (bytes : list N) (sz : int_type) (sgn : signed) :
    lengthN bytes = bytesN sz ->
    has_type_prop (_Z_from_bytes_le sgn bytes) (Tnum sz sgn).
  Proof.
    move => Hlength. rewrite /_Z_from_bytes_le.
    case_match; subst; last by apply _Z_from_bytes_unsigned_le_has_type_prop.
    rewrite /lengthN /bytesN in Hlength; apply Nat2N.inj in Hlength; rewrite Hlength.
    unfold operator.to_signed_bits.
    rewrite bool_decide_false; last by destruct sz.
    destruct sz => /=.
    all: repeat (destruct bytes as [|? bytes]; simpl in Hlength; try lia; clear Hlength).
    all: case_bool_decide; rewrite -has_int_type /bound/=;
      try match goal with
      | |- context[Z.modulo ?a ?b] => pose proof (Z.mod_pos_bound a b ltac:(lia)); lia
      end.
  Qed.

  Lemma _Z_from_bytes_has_type_prop :
    forall (endianness : endian) (sz : int_type) (sgn : signed) (bytes : list N),
      lengthN bytes = bytesN sz ->
      has_type_prop (Vint (_Z_from_bytes endianness sgn bytes)) (Tnum sz sgn).
  Proof.
    intros * Hlength.
    rewrite _Z_from_bytes_eq/_Z_from_bytes_def.
    eapply _Z_from_bytes_le_has_type_prop.
    case_match; auto; unfold lengthN in *; by rewrite rev_length.
  Qed.
End with_σ.
