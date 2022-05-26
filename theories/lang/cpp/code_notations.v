(*
 * Copyright (c) 2019-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.ZArith.ZArith.

Require bedrock.lang.cpp.ast.
From bedrock.lang.cpp.syntax Require Import type_notations expr_notations stmt_notations.

#[local] Open Scope Z_scope.
#[local] Open Scope bs_scope.

(* TODOS (JH):
   - Look into disabling (selective) scopes
   - Determine what the minimum [Printing Width] needed for reasonable goal display is
 *)

Module Export CodeNotations.
  Export TypeNotations.
  Export ExprNotations.
  Export StmtNotations.
End CodeNotations.

(* NOTE: The following [Section] is only used for testing purposes; if you break one of these
   tests - or add a new notation - please update things accordingly.
 *)

Section TestCodeNotations.
  Import bedrock.lang.cpp.ast.
  Import CodeNotations. Import List.ListNotations.
  #[local] Set Printing Width 10000.

  (* Check *)
  (*   (Sseq ( *)
  (*             [ Sif *)
  (*               (Some (Dvar "x" (Qmut Ti32) (Some (Eint 0 (Qmut Ti32))))) *)
  (*               (Ecast Cint2bool Prvalue *)
  (*                   (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool)) *)
  (*               (Scontinue) *)
  (*               (Sseq [Scontinue;Scontinue;Scontinue;Scontinue]) *)
  (*             ; Sreturn (Some (Evar (Lname "x") Ti32)) *)
  (*             ; Sreturn None *)
  (*             ] *)
  (*   )). *)

  (* Check *)
  (*   (Sseq ( *)
  (*             [ Sif *)
  (*               (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32))))) *)
  (*               (Ecast Cint2bool Prvalue *)
  (*                   (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool)) *)
  (*               (Scontinue) *)
  (*               (Scontinue) *)
  (*             ; Sreturn (Some (Evar (Lname "x") Ti32)) *)
  (*             ; Sreturn None *)
  (*             ] *)
  (*   )). *)

  (* Check *)
  (*   (Sseq ( *)
  (*             (Sif *)
  (*               (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32))))) *)
  (*               (Ecast Cint2bool Prvalue *)
  (*                   (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool)) *)
  (*               (Sseq ( *)
  (*                   (Sexpr Prvalue *)
  (*                     (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil)) *)
  (*               Scontinue) :: *)
  (*             nil)). *)

  (* Check *)
  (*   (Sseq ( *)
  (*             (Sif *)
  (*               (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32))))) *)
  (*               (Ecast Cint2bool Prvalue *)
  (*                   (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool)) *)
  (*               (Sseq ( *)
  (*                   (Sexpr Prvalue *)
  (*                     (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil)) *)
  (*               (Sseq ( *)
  (*                   (Sexpr Lvalue *)
  (*                     (Epredec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) :: *)
  (*             (Swhile *)
  (*               (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32))))) *)
  (*               (Ecast Cint2bool Prvalue *)
  (*                   (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool)) *)
  (*               (Sseq ( *)
  (*                   (Sexpr Prvalue *)
  (*                     (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) :: nil)). *)

  (* Check *)
  (*   (Sseq ( *)
  (*        (Sdo *)
  (*           (Sseq ( *)
  (*                (Sexpr Prvalue *)
  (*                       (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil)) *)
  (*           (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) *)
  (*        ) :: nil)). *)

  (* Check *)
  (*   (Sseq ( *)
  (*        (Sdo *)
  (*           (Sseq ( *)
  (*                (Sexpr Lvalue *)
  (*                       (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)) :: nil)) *)
  (*           (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) *)
  (*        ) :: nil)). *)

  (* Check *)
  (*   (Sexpr Lvalue *)
  (*           (Eassign (Evar (Lname "should_continue") Tbool) *)
  (*              (Eunop Unot *)
  (*                 (Ecall *)
  (*                    (Ecast Cfunction2pointer Lvalue *)
  (*                       (Evar (Gname "_Z15process_commandPKN4Zeta8Zeta_ctxEPcR9UmxSharedRmR5Admin") *)
  (*                          (Tfunction Tbool *)
  (*                             [Tqualified {| q_const := true; q_volatile := false |} *)
  (*                                (Tptr *)
  (*                                   (Tqualified {| q_const := true; q_volatile := false |} Tvoid)); *)
  (*                             Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;  *)
  (*                             Tref Ti32])) *)
  (*                       (Tptr *)
  (*                          (Tfunction Tbool *)
  (*                             [Tqualified {| q_const := true; q_volatile := false |} *)
  (*                                (Tptr *)
  (*                                   (Tqualified {| q_const := true; q_volatile := false |} Tvoid)); *)
  (*                             Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;  *)
  (*                             Tref Ti32]))) *)
  (*                    [Ecast Cl2r Lvalue *)
  (*                       (Evar (Lname "ctx") *)
  (*                          (Tqualified {| q_const := true; q_volatile := false |} *)
  (*                             (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid)))) *)
  (*                       (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid)); *)
  (*                    Ecast Carray2pointer Lvalue (Evar (Lname "buffer") (Tarray Tu8 1024)) (Tptr Tu8); *)
  (*                    Eread_ref (Evar (Lname "shared") (Tnamed "_Z9UmxShared")); *)
  (*                    Eread_ref (Evar (Lname "client") Tu64); Evar (Lname "result") Ti32] *)
  (*                    Tbool) Tbool) *)
  (*              Tbool)). *)
End TestCodeNotations.
