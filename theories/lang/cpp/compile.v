(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)

(** this file describes the assumptions made about the compiler.

    in particular, it describes the connection between the semantics
    of C++ declarations (e.g. functions, methods, constructors, destructors),
    and the machine-level specification of the bytes in memory ([fspec]).

 *)

Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.logic.
Require Import bedrock.lang.cpp.semantics.

Section with_Σ.
  Context `{Σ : cpp_logic thread_info}.
  Context {ti : thread_info} {σ : genv}.

  (** compilation of a function [f] is correct if the weakest pre-condition
      of the function ([wp_func]) implies the weakest pre-condition of the
      compiled code ([fspec]).
   *)
  Axiom code_at_ok : forall (f : Func) p,
      code_at (σ:=σ) f p
      |-- Forall ti ls Q, wp_func (resolve:=σ) f ti ls Q -*
                          fspec ti (Vptr p) ls Q.

  Axiom method_at_ok : forall (m : Method) p,
      method_at (σ:=σ) m p
      |-- Forall ti ls Q, wp_method (resolve:=σ) m ti ls Q -*
                          fspec ti (Vptr p) ls Q.

  Axiom ctor_at_ok : forall (c : Ctor) p,
      ctor_at (σ:=σ) c p
      |-- Forall ti ls Q, wp_ctor (resolve:=σ) c ti ls Q -*
                          fspec ti (Vptr p) ls Q.

  Axiom dtor_at_ok : forall (d : Dtor) p,
      dtor_at (σ:=σ) d p
      |-- Forall ti ls Q, wp_dtor (resolve:=σ) d ti ls Q -*
                          fspec ti (Vptr p) ls Q.

End with_Σ.
