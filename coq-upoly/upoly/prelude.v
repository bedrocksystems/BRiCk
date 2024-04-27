(*
 * Copyright (c) 2023-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export Coq.ssr.ssreflect.
Require Export stdpp.base.

#[export] Set Typeclasses Unique Instances.

#[export] Set Universe Polymorphism.
#[export] Set Polymorphic Inductive Cumulativity.
#[export] Unset Auto Template Polymorphism.
#[export] Unset Universe Minimization ToSet.

#[export] Set Primitive Projections.
#[export] Set Printing Coercions.	(** Readability *)

#[export] Set Suggest Proof Using.
#[export] Set Default Proof Using "Type".
#[export] Set Default Goal Selector "!".
#[export] Set Ltac Backtrace.
#[export] Unset Program Cases.
