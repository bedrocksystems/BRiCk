(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
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
  Context {ti : thread_info} {σ : genv} (tu : translation_unit).

  (* BEGIN COMPILE SNIPPET *)
  (** compilation of a function [f] is correct if the weakest pre-condition
      of the function ([wp_func]) implies the weakest pre-condition of the
      compiled code ([fspec]).
   *)
  Axiom code_at_ok : forall (f : Func) p,
      code_at σ tu f p
      |-- Forall ls Q, wp_func (resolve:=σ) tu f ls Q -*
                       fspec (Σ:=Σ) tu.(globals) (type_of_value (Ofunction f)) p ls Q.

  Axiom method_at_ok : forall (m : Method) p,
      method_at σ tu m p
      |-- Forall ls Q, wp_method (resolve:=σ) tu m ls Q -*
                       fspec (Σ:=Σ) tu.(globals) (type_of_value (Omethod m)) p ls Q.

  Axiom ctor_at_ok : forall (c : Ctor) p,
      ctor_at σ tu c p
      |-- Forall ls Q, wp_ctor (resolve:=σ) tu c ls Q -*
                       fspec tu.(globals) (type_of_value (Oconstructor c)) p ls Q.

  Axiom dtor_at_ok : forall (d : Dtor) p,
      dtor_at σ tu d p
      |-- Forall ls Q, wp_dtor (resolve:=σ) tu d ls Q -*
                       fspec tu.(globals) (type_of_value (Odestructor d)) p ls Q.
  (* END COMPILE SNIPPET *)

End with_Σ.
