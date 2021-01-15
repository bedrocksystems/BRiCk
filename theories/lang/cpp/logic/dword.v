(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

From iris.bi.lib Require Import fractional.

From bedrock.lang.cpp Require Import logic.pred.
From bedrock.lang.cpp.semantics Require Import types genv values.
Require Import bedrock.lang.prelude.addr.

Variant Virt_or_phys : Set := Virtual | Physical.
Parameter data_at :
  forall `{Σ:cpp_logic} {σ:genv}
     (virt : Virt_or_phys) (sz : bitsize) (q : Qp) (addr : N) (n : N), mpred.
Axiom data_at_fractional :
  forall `{Σ:cpp_logic} {σ:genv} virt sz addr n,
    Fractional (λ q, data_at virt sz q addr n).
#[global] Existing Instance data_at_fractional.
Axiom data_at_timeless :
  forall `{Σ:cpp_logic} {σ:genv} virt sz q addr n,
    Timeless (data_at virt sz q addr n).
#[global] Existing Instance data_at_timeless.

(*[pdata_at sz q pa n]: Physical address [pa] contains value [n], encoded
  as [sz] with permission [q].*)
#[global] Notation pdata_at := (@data_at _ _ _ Physical).
#[global] Notation pbyte_at := (pdata_at W8).
#[global] Notation pshort_at := (pdata_at W16).
#[global] Notation pword_at := (pdata_at W32).
#[global] Notation pdword_at := (pdata_at W64).

(*[vdata_at sz q va n]: Virtual address [va] contains value [n], encoded
  as [sz] with permission [q].*)
#[global] Notation vdata_at := (@data_at _ _ _ Virtual).
#[global] Notation vbyte_at := (vdata_at W8).
#[global] Notation vshort_at := (vdata_at W16).
#[global] Notation vword_at := (vdata_at W32).
#[global] Notation vdword_at := (vdata_at W64).

(*[phantdata_at sz q p]: In the C++ abstract machine, [p] previously contained
  some integer data encoded as [sz], with permission [q]. When you re-enter the
  C++ virtual machine (via [compiler_memory_entry]), you combine [phantdata_at]
  with a virtual points-to fact to get a C++-level points-to.*)
Parameter phantdata_at :
  forall `{Σ:cpp_logic} {σ:genv} (sz : bitsize) (q : Qp) (p : ptr), mpred.
#[global] Notation phantbyte_at := (phantdata_at W8).
#[global] Notation phantshort_at := (phantdata_at W16).
#[global] Notation phantword_at := (phantdata_at W32).
#[global] Notation phantdword_at := (phantdata_at W64).
Axiom phantdata_at_fractional :
  forall `{Σ:cpp_logic} {σ:genv} sz p, Fractional (λ q, phantdata_at sz q p).
#[global] Existing Instance phantdata_at_fractional.
Axiom phantdata_at_timeless :
  forall `{Σ:cpp_logic} {σ:genv} sz q p, Timeless (phantdata_at sz q p).
#[global] Existing Instance phantdata_at_timeless.
