(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import ZArith.

Require Import bedrock.prelude.base.
From bedrock.lang Require Import ast notations code_notations.

(* TODO (JH): Add more examples here (and remove the duplicates) *)
Section TestCodeNotations.
  Context (ty : type) (e : Expr) (s : Stmt).

  Check (Sexpr Lvalue (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)).

  Check (Ebinop Badd (Ederef (Eaddrof (Evar (Lname "hello") Tvoid)) Tvoid)
                (Eint 3%Z Tvoid) Tvoid).


  Check (Sseq (Sexpr Lvalue (Evar (Lname "hello") Tvoid) :: Scontinue :: Sbreak :: Sexpr Lvalue (Evar (Lname "world") Tvoid) :: Sif None (Evar (Lname "world") Tvoid) Scontinue Sbreak :: nil)).

  Check
    (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq [Scontinue;Scontinue;Scontinue;Scontinue])
                Sbreak
              ; Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq [])
                Sbreak
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sexpr Lvalue (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
              ; Sreturn None
              ]%list
    )).

  Check
    Sseq (
                [ Sif
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool Prvalue
                      (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                  (Scontinue)
                  (Sseq [Scontinue;Scontinue;Scontinue;Scontinue])
                ; Sreturn (Some (Evar (Lname "x") Ti32))
                ; Sreturn None
                ]%list
    ).

  Check
    Sseq (
                [ Sif
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool Prvalue
                      (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                  (Scontinue)
                  (Scontinue)
                ; Sreturn (Some (Evar (Lname "x") Ti32))
                ; Sreturn None
                ]%list
    ).

  Check
    Sseq (
                (Sif
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool Prvalue
                      (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                  (Sseq (
                      (Sexpr Prvalue
                        (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                  Scontinue) ::
                nil
    ).

  Check
    Sseq (
                (Sif
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool Prvalue
                      (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                  (Sseq (
                      (Sexpr Prvalue
                        (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                  (Sseq (
                      (Sexpr Lvalue
                        (Epredec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) ::
                (Swhile
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool Prvalue
                      (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                  (Sseq (
                      (Sexpr Prvalue
                        (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) :: nil).

  Check
    Sseq (
           (Sdo
              (Sseq (
                   (Sexpr Prvalue
                          (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
              (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))
           ) :: nil).

  Check
    Sseq (
           (Sdo
              (Sseq (
                   (Sexpr Lvalue
                          (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)) :: nil))
              (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))
           ) :: nil).

  Check
    Sexpr Lvalue
              (Eassign (Evar (Lname "should_continue") Tbool)
                 (Eunop Unot
                    (Ecall
                       (Ecast Cfunction2pointer Lvalue
                          (Evar (Gname "_Z15process_commandPKN4Zeta8Zeta_ctxEPcR9UmxSharedRmR5Admin")
                             (Tfunction Tbool
                                [Tqualified {| q_const := true; q_volatile := false |}
                                   (Tptr
                                      (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                                Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;
                                Tref Ti32]%list))
                          (Tptr
                             (Tfunction Tbool
                                [Tqualified {| q_const := true; q_volatile := false |}
                                   (Tptr
                                      (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                                Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;
                                Tref Ti32]%list)))
                       [Ecast Cl2r Lvalue
                          (Evar (Lname "ctx")
                             (Tqualified {| q_const := true; q_volatile := false |}
                                (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid))))
                          (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                       Ecast Carray2pointer Lvalue (Evar (Lname "buffer") (Tarray Tu8 1024)) (Tptr Tu8);
                       Eread_ref (Evar (Lname "shared") (Tnamed "_Z9UmxShared"));
                       Eread_ref (Evar (Lname "client") Tu64); Evar (Lname "result") Ti32]%list
                       Tbool) Tbool)
                 Tbool).

  Check
    (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint 0 (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Scontinue)
                (Sseq [Scontinue;Scontinue;Scontinue;Scontinue])
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sreturn None
              ]
    )).

  Check
    (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Scontinue)
                (Scontinue)
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sreturn None
              ]
    )).

  Check
    (Sseq (
              (Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq (
                    (Sexpr Prvalue
                      (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                Scontinue) ::
              nil)).

  Check
    (Sseq (
              (Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq (
                    (Sexpr Prvalue
                      (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                (Sseq (
                    (Sexpr Lvalue
                      (Epredec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) ::
              (Swhile
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq (
                    (Sexpr Prvalue
                      (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) :: nil)).

  Check
    (Sseq (
         (Sdo
            (Sseq (
                 (Sexpr Prvalue
                        (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
            (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))
         ) :: nil)).

  Check
    (Sseq (
         (Sdo
            (Sseq (
                 (Sexpr Lvalue
                        (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)) :: nil))
            (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))
         ) :: nil)).

  Check
    (Sexpr Lvalue
            (Eassign (Evar (Lname "should_continue") Tbool)
               (Eunop Unot
                  (Ecall
                     (Ecast Cfunction2pointer Lvalue
                        (Evar (Gname "_Z15process_commandPKN4Zeta8Zeta_ctxEPcR9UmxSharedRmR5Admin")
                           (Tfunction Tbool
                              [Tqualified {| q_const := true; q_volatile := false |}
                                 (Tptr
                                    (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                              Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;
                              Tref Ti32]))
                        (Tptr
                           (Tfunction Tbool
                              [Tqualified {| q_const := true; q_volatile := false |}
                                 (Tptr
                                    (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                              Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;
                              Tref Ti32])))
                     [Ecast Cl2r Lvalue
                        (Evar (Lname "ctx")
                           (Tqualified {| q_const := true; q_volatile := false |}
                              (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid))))
                        (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                     Ecast Carray2pointer Lvalue (Evar (Lname "buffer") (Tarray Tu8 1024)) (Tptr Tu8);
                     Eread_ref (Evar (Lname "shared") (Tnamed "_Z9UmxShared"));
                     Eread_ref (Evar (Lname "client") Tu64); Evar (Lname "result") Ti32]
                     Tbool) Tbool)
               Tbool)).
End TestCodeNotations.
