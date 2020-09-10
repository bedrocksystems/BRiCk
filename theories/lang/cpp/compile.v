(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
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
      code_at σ f p
      |-- Forall ti ls Q, wp_func (resolve:=σ) f ti ls Q -*
                          fspec (Σ:=Σ) σ.(genv_tu).(globals) (type_of_value (Ofunction f)) ti (Vptr p) ls Q.

  Axiom method_at_ok : forall (m : Method) p,
      method_at σ m p
      |-- Forall ti ls Q, wp_method (resolve:=σ) m ti ls Q -*
                          fspec (Σ:=Σ) σ.(genv_tu).(globals) (type_of_value (Omethod m)) ti (Vptr p) ls Q.

  Axiom ctor_at_ok : forall (c : Ctor) p,
      ctor_at σ c p
      |-- Forall ti ls Q, wp_ctor (resolve:=σ) c ti ls Q -*
                          fspec σ.(genv_tu).(globals) (type_of_value (Oconstructor c)) ti (Vptr p) ls Q.

  Axiom dtor_at_ok : forall (d : Dtor) p,
      dtor_at σ d p
      |-- Forall ti ls Q, wp_dtor (resolve:=σ) d ti ls Q -*
                          fspec σ.(genv_tu).(globals) (type_of_value (Odestructor d)) ti (Vptr p) ls Q.

End with_Σ.
