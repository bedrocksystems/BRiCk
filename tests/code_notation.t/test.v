(*
 * Copyright (c) 2022-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import ZArith.

Require Import bedrock.prelude.base.
From bedrock.lang Require Import ast notations code_notations.

(* TODO (JH): Add more examples here (and remove the duplicates) *)
Section TestCodeNotations.
  Context (ty : decltype) (e : Expr) (s : Stmt).

  Let stmt1 : Stmt :=
    Sexpr (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid).
  Print stmt1.

  Let expr1 : Expr :=
    Ebinop Badd (Ederef (Eaddrof (Evar (Lname "hello") Tvoid)) Tvoid) (Eint 3%Z Tvoid) Tvoid.
  Print expr1.

  Let stmt2 : Stmt :=
    Sseq (Sexpr (Evar (Lname "hello") Tvoid) :: Scontinue :: Sbreak :: Sexpr (Evar (Lname "world") Tvoid) :: Sif None (Evar (Lname "world") Tvoid) Scontinue Sbreak :: nil).
  Print stmt2.

  Let stmt3 : Stmt :=
    (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool
                    (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                (Sseq [Scontinue;Scontinue;Scontinue;Scontinue])
                Sbreak
              ; Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool
                    (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                (Sseq [])
                Sbreak
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sexpr (Ecast Cint2bool
                    (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
              ; Sreturn None
              ]%list
    )).
  Print stmt3.

  Let stmt4 : Stmt :=
    Sseq (
                [ Sif
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool
                      (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                  (Scontinue)
                  (Sseq [Scontinue;Scontinue;Scontinue;Scontinue])
                ; Sreturn (Some (Evar (Lname "x") Ti32))
                ; Sreturn None
                ]%list
    ).
  Print stmt4.

  Let stmt5 : Stmt :=
    Sseq (
                [ Sif
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool
                      (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                  (Scontinue)
                  (Scontinue)
                ; Sreturn (Some (Evar (Lname "x") Ti32))
                ; Sreturn None
                ]%list
    ).
  Print stmt5.

  Let stmt6 : Stmt :=
    Sseq (
                (Sif
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool
                      (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                  (Sseq (
                      (Sexpr
                        (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                  Scontinue) ::
                nil
    ).
  Print stmt6.

  Let stmt7 : Stmt :=
    Sseq (
                (Sif
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool
                      (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                  (Sseq (
                      (Sexpr
                        (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                  (Sseq (
                      (Sexpr
                        (Epredec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) ::
                (Swhile
                  (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                  (Ecast Cint2bool
                      (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                  (Sseq (
                      (Sexpr
                        (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) :: nil).
  Print stmt7.

  Let stmt8 : Stmt :=
    Sseq (
           (Sdo
              (Sseq (
                   (Sexpr
                          (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
              (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32))
           ) :: nil).
  Print stmt8.

  Let stmt9 : Stmt :=
    Sseq (
           (Sdo
              (Sseq (
                   (Sexpr
                          (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)) :: nil))
              (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32))
           ) :: nil).
  Print stmt9.

  Let stmt10 : Stmt :=
    Sexpr
              (Eassign (Evar (Lname "should_continue") Tbool)
                 (Eunop Unot
                    (Ecall
                       (Ecast Cfun2ptr
                          (Evar (Gname "_Z15process_commandPKN4Zeta8Zeta_ctxEPcR9UmxSharedRmR5Admin")
                             (Tfunction Tbool
                                [Tqualified QC
                                   (Tptr
                                      (Tqualified QC Tvoid));
                                Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;
                                Tref Ti32]%list))
                          Prvalue
                          (Tptr
                             (Tfunction Tbool
                                [Tqualified QC
                                   (Tptr
                                      (Tqualified QC Tvoid));
                                Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;
                                Tref Ti32]%list)))
                       [Ecast Cl2r
                          (Evar (Lname "ctx")
                             (Tqualified QC
                                (Tptr (Tqualified QC Tvoid))))
                          Prvalue
                          (Tptr (Tqualified QC Tvoid));
                       Ecast Carray2ptr (Evar (Lname "buffer") (Tarray Tu8 1024)) Prvalue (Tptr Tu8);
                       Evar (Lname "shared") (Tref (Tnamed "_Z9UmxShared"));
                       Evar (Lname "client") (Tref Tu64); Evar (Lname "result") Ti32]%list
                       Tbool) Tbool)
                 Tbool).
  Print stmt10.

  Let stmt11 : Stmt :=
    (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint 0 (Qmut Ti32)))))
                (Ecast Cint2bool
                    (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                (Scontinue)
                (Sseq [Scontinue;Scontinue;Scontinue;Scontinue])
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sreturn None
              ]
    )).
  Print stmt11.

  Let stmt12 : Stmt :=
    (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool
                    (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                (Scontinue)
                (Scontinue)
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sreturn None
              ]
    )).
  Print stmt12.

  Let stmt13 : Stmt :=
    (Sseq (
              (Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool
                    (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                (Sseq (
                    (Sexpr
                      (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                Scontinue) ::
              nil)).
  Print stmt13.

  Let stmt14 : Stmt :=
    (Sseq (
              (Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool
                    (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                (Sseq (
                    (Sexpr
                      (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                (Sseq (
                    (Sexpr
                      (Epredec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) ::
              (Swhile
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool
                    (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32)) Prvalue (Qmut Tbool))
                (Sseq (
                    (Sexpr
                      (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) :: nil)).
  Print stmt14.

  Let stmt15 : Stmt :=
    (Sseq (
         (Sdo
            (Sseq (
                 (Sexpr
                        (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
            (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32))
         ) :: nil)).
  Print stmt15.

  Let stmt16 : Stmt :=
    (Sseq (
         (Sdo
            (Sseq (
                 (Sexpr
                        (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)) :: nil))
            (Ecast Cl2r (Evar (Lname  "x") (Qmut Ti32)) Prvalue (Qmut Ti32))
         ) :: nil)).
  Print stmt16.

  Let stmt17 : Stmt :=
    (Sexpr
            (Eassign (Evar (Lname "should_continue") Tbool)
               (Eunop Unot
                  (Ecall
                     (Ecast Cfun2ptr
                        (Evar (Gname "_Z15process_commandPKN4Zeta8Zeta_ctxEPcR9UmxSharedRmR5Admin")
                           (Tfunction Tbool
                              [Tqualified QC
                                 (Tptr
                                    (Tqualified QC Tvoid));
                              Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;
                              Tref Ti32]))
                        Prvalue
                        (Tptr
                           (Tfunction Tbool
                              [Tqualified QC
                                 (Tptr
                                    (Tqualified QC Tvoid));
                              Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64;
                              Tref Ti32])))
                     [Ecast Cl2r
                        (Evar (Lname "ctx")
                           (Tqualified QC
                              (Tptr (Tqualified QC Tvoid))))
                        Prvalue
                        (Tptr (Tqualified QC Tvoid));
                     Ecast Carray2ptr (Evar (Lname "buffer") (Tarray Tu8 1024)) Prvalue (Tptr Tu8);
                     Evar (Lname "shared") (Tref (Tnamed "_Z9UmxShared"));
                     Evar (Lname "client") (Tref Tu64); Evar (Lname "result") Ti32]
                     Tbool) Tbool)
               Tbool)).
  Print stmt17.
End TestCodeNotations.
