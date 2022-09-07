(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From iris Require Import bi.bi.
From bedrock Require Import lang.bi.prelude.
Require Import bedrock.prelude.addr.
Import ChargeNotation.

#[local] Open Scope N_scope.
Section lift.
  Context {PROP: bi}.
  Variable byte_at : forall (hpa:paddr) (hpaFrac : Qp) (value : N), PROP.

  #[local] Fixpoint lift_aux n (pa : paddr) (q:Qp) (v : N) :=
    match n with
    | O => byte_at pa q v
    | S n => let bytesize :N := (2 ^ (N.of_nat n)) in
            let bitsize := 8 * bytesize in
            lift_aux n pa q (N.land v (2 ^ bitsize - 1))
            ** lift_aux n (pa+bytesize) q (N.shiftr v bitsize)
    end.

  (* byte by byte, layout the bits of [v] starting at [paddr], lsb first (little-endian), using the [byte_at] parameter to lay out each byte *)
  Definition bytes_at (nbytes:N) (pa : paddr) (q:Qp) (v : N) :=
    lift_aux (N.to_nat (BinNatDef.N.log2 nbytes)) pa q v.

  Section test.

    Let short_at (pa : paddr) (q:Qp) (v : N) : PROP :=
      byte_at pa q (N.land v (2^8 - 1))
      ** byte_at (pa + 1)%N q (N.shiftr v 8).

    Let word_at (pa : paddr) (q : Qp) (v : N) : PROP :=
      short_at pa q (N.land v (2^16 - 1))
      ** short_at (pa + 2)%N q (N.shiftr v 16).

    Succeed Example t1 pa q v : short_at pa q v = bytes_at 2 pa q v := eq_refl.
    Succeed Example t2 pa q v : word_at pa q v = bytes_at 4 pa q v := eq_refl.
  End test.

End lift.
