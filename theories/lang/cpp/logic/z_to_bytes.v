(*
 * Copyright (c) 2020-2021,2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

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

End with_σ.
