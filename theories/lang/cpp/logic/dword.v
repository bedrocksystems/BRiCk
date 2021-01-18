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

Parameter vdata_at :
  forall `{Σ:cpp_logic} {σ:genv}
    (sz : bitsize) (q : Qp) (addr : N) (n : N), mpred.
Axiom vdata_at_fractional :
  forall `{Σ:cpp_logic} {σ:genv} sz addr n,
    Fractional (λ q, vdata_at sz q addr n).
#[global] Existing Instance vdata_at_fractional.
Axiom vdata_at_timeless :
  forall `{Σ:cpp_logic} {σ:genv} sz q addr n,
    Timeless (vdata_at sz q addr n).
#[global] Existing Instance vdata_at_timeless.

(*[vdata_at sz q va n]: Virtual address [va] contains value [n], encoded
  as [sz] with permission [q].*)
#[global] Notation vbyte_at := (vdata_at W8).
#[global] Notation vshort_at := (vdata_at W16).
#[global] Notation vword_at := (vdata_at W32).
#[global] Notation vdword_at := (vdata_at W64).

(*[phantdata_at ty q p]: In the C++ abstract machine, [p] previously
  contained a [ty]-typed value with permission [q]. When you re-enter
  the C++ virtual machine (via [memory_entry]), you combine
  [phantdata_at] with a virtual points-to fact to get a C++-level
  points-to.*)
Parameter phantdata_at :
  forall `{Σ:cpp_logic} {σ:genv} (ty : type) (q : Qp) (p : ptr), mpred.
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
