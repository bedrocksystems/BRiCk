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

  Lemma _Z_from_bytes_le_has_type_prop :
    forall (bytes : list N) (sz : int_type) (sgn : signed),
      lengthN bytes = bytesN sz ->
      has_type_prop (_Z_from_bytes_le sgn bytes) (Tnum sz sgn).
  Proof.
    intros * Hlength; unfold _Z_from_bytes_le; case_match; subst;
      last by apply _Z_from_bytes_unsigned_le_has_type_prop.
    rewrite /lengthN/bytesN in Hlength; apply Nat2N.inj in Hlength.
    unfold operator.to_signed_bits.
    rewrite bool_decide_false; cbn; last by (rewrite Hlength; destruct sz=> //=).
    assert ((sz = W8 /\
             exists b1,
               bytes = [b1]) \/
            (sz = W16 /\
             exists b1 b2,
               bytes = [b1; b2]) \/
            (sz = W32 /\
             exists b1 b2 b3 b4,
               bytes = [b1; b2; b3; b4]) \/
            (sz = W64 /\
             exists b1 b2 b3 b4 b5 b6 b7 b8,
               bytes = [b1; b2; b3; b4; b5; b6; b7; b8]) \/
            (sz = W128 /\
             exists b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16,
               bytes = [b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16]))
      as [[-> Hbytes] | [[-> Hbytes] | [[-> Hbytes] | [[-> Hbytes] | [-> Hbytes]]]]]. 1: {
      destruct sz; cbn in Hlength; repeat (destruct bytes as [| ? bytes]; try discriminate);
        [ do 0 right; left
        | do 1 right; left
        | do 2 right; left
        | do 3 right; left
        | do 4 right];
        split; eauto.
      - do 8 eexists; eauto.
      - do 16 eexists; eauto.
    }
    all: repeat (match goal with
                 | H : exists _, _ |- _ =>
                     destruct H as [? H]
                 end); subst; cbn.
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
