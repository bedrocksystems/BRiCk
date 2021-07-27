(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From Coq Require Import NArith.BinNat.
Require Export bedrock.prelude.wrap.

(*
Module [types] is only used for compatibility with some clients.
TODO FM-643: flatten this module once clients are migrated.. *)
Module Export types.
  Variant Phant_Int_line : Set := Build_Phant_Int_line.
  Definition int_line : Set := WrapN Phant_Int_line.
  Definition Build_int_line (n : N) : int_line := Build_WrapN Phant_Int_line n.
  Definition get_int_line (s : int_line) : N := s.(unwrapN).

  Variant Phant_Time := Build_Phant_Time.
  Definition time := WrapN Phant_Time.
  Definition Build_time (n : N) : time := Build_WrapN Phant_Time n.
  Definition get_time (t : time) : N := t.(unwrapN).

  Variant Phant_Cpu := Build_Phant_Cpu.
  Definition cpu := WrapN Phant_Cpu.
  Definition Build_cpu (n : N) : cpu := Build_WrapN Phant_Cpu n.
  Definition get_cpu (s : cpu) : N := s.(unwrapN).

  Variant Phant_mmio_idx : Set := Build_Phant_mmio_idx.
  Definition mmio_idx : Set := WrapN Phant_mmio_idx.
  Definition Build_mmio_idx (n : N) : mmio_idx := Build_WrapN Phant_mmio_idx n.
  Definition get_mmio_idx (i : mmio_idx) : N := i.(unwrapN).

  Variant Phant_size_bytes : Set := Build_Phant_size_bytes.
  Definition size_bytes : Set := WrapN Phant_size_bytes.
  Definition Build_size_bytes (n : N) : size_bytes := Build_WrapN Phant_size_bytes n.
  Definition get_size_bytes (sz : size_bytes) : N := sz.(unwrapN).
End types.
