(*
 * Copyright (c) 2019-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.ZArith.ZArith.

From bedrock.lang.cpp.syntax Require Import names stmt.

#[local] Open Scope Z_scope.
#[local] Open Scope bs_scope.

(* TODO (JH): Investigate which (if any) of the subsequent notations we can make
   printing/parsing
 *)
Module Export StmtNotations.
  Declare Custom Entry CPP_stmt.
  Declare Scope CPP_stmt_scope.
  Delimit Scope CPP_stmt_scope with cpp_stmt.

  (* Injection into [constr] in case we're printing this at the top-level *)
  Notation "'{(stmt:' s )}" := s
    ( at level 200
    , s custom CPP_stmt at level 200
    , format "'[hv' {(stmt:  '/' s )} ']'"
    , only printing) : CPP_stmt_scope.
  (* Injection from [constr] in case we're printing a subterm we don't recognize *)
  Notation "'{(coq:' e ')}'"
      := e
         ( in custom CPP_stmt at level 0
         , e constr
         , format "'[hv' {(coq:  '/' e )} ']'").
End StmtNotations.

(* NOTE: The following [Section]s are only used for testing purposes; if you break one of these
   tests - or add a new notation - please update things accordingly.
 *)

Section TestStmtNotations.
End TestStmtNotations.

(* [cpp2v/theories/auto/cpp/notations/code.v@janno/code-notations], but that branch is out of date
Declare Custom Entry CPP.
Declare Scope CPP_scope.
Delimit Scope CPP_scope with cpp.

(** Notations for statements *)
Notation "'{stmt:' e }"
    := e
       ( at level 0
       , e custom cpp_stmt at level 200
       , format "{stmt:  e }"
       , only printing)
    : cppstmt_scope.

(* Statements that provide their own line break *)
(* NOTE (JH): statements will be enclosed in [{stmt: ...}], so we don't include curly
   braces here.
 *)
(* NOTE (JH): statements terminal [Stmt]s will have notations which insert semicolons
   (and the appropriate spacing after them).
 *)
Notation "'//' 'end' 'block'"
    := (Sseq nil)
       ( in custom cpp_stmt at level 0
       , format "'[' //  end  block ']'"
       , only printing).
Notation "s"
    := (Sseq (cons s nil))
       ( in custom cpp_stmt at level 0
       , s custom cpp_stmt at level 200
       , format "'[' s ']'"
       , only printing).
Notation "s1 .. s2 '//' 'end' 'block'"
    := (Sseq (cons s1 .. (cons s2 (nil)) ..))
       ( in custom cpp_stmt at level 0
       , s1 custom cpp_stmt at level 200
       , s2 custom cpp_stmt at level 200
       , format "'[v' s1 '/' .. '/' s2 '//' //  end  block ']'"
       , only printing).

(* Statements that provide their own line break *)
(* Notation "{ s1 ; .. ; s2 ; }" *)
(*     := (Sseq (cons s1 .. (cons s2 (nil)) ..)) *)
(*        ( in custom cpp_stmt at level 0 *)
(*        , s1 custom cpp_stmt at level 200 *)
(*        , s2 custom cpp_stmt at level 200 *)
(*        , format "'/' { '//'  '[v' s1 ';' '//' .. ';' '//' s2 ';' ']' '//' }" *)
(*        , only printing). *)

(* Notation "{ s1 ; .. ; s2 ; }" := (Sseq (@cons Stmt s1 .. (@cons Stmt s2 (@nil Stmt)) ..)) *)
(*                                (in custom cpp_stmt at level 0, *)
(*                                 s1 custom cpp_stmt at level 200, *)
(*                                 s2 custom cpp_stmt at level 200, *)
(*                                 only printing, *)
(*                                 format "'[  ' { '//' '[v' s1 ';' '//' .. ';' '//' s2 ';' ']' '//' ']' }"). *)

(* Notation "s1 ; .. ; s2 ;" := (Sseq (@cons Stmt s1 .. (@cons Stmt s2 (@nil Stmt)) ..)) *)
(*                                (in custom cpp_stmt_unbraced at level 0, *)
(*                                 s1 custom cpp_stmt at level 200, *)
(*                                 s2 custom cpp_stmt at level 200, *)
(*                                 only printing, *)
(*                                 format "'[v' '//' s1 ';' '//' .. ';' '//' s2 ';' ']' '//'"). *)

(* Notation "s" := (Sseq (@cons s nil)) (in custom cpp_stmt at level 0, s custom cpp_stmt). *)

(* Notation "s" := (s) (in custom cpp_stmt_unbraced at level 0, s custom cpp_stmt at level 200, only printing). *)

Notation "e ;"
    := (Sexpr _ e)
       ( in custom cpp_stmt at level 0
       , e custom cpp_expr at level 200
       , format "'[' e ; ']'"
       , only printing).

(* Check (Sexpr Lvalue (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)). *)

Notation "'continue;'"
    := Scontinue
       ( in custom cpp_stmt at level 0
       , format "'[' continue;  ']'"
       , only printing).
Notation "'break;'"
    := Sbreak
       ( in custom cpp_stmt at level 0
       , format "'[' break;  ']'"
       , only printing).
Notation "'return' e ;"
    := (Sreturn (Some (e)))
       ( in custom cpp_stmt at level 0
       , e custom cpp_expr at level 200
       , format "'[' return  e ;  ']'"
       , only printing).
Notation "'return;'"
    := (Sreturn None)
       ( in custom cpp_stmt at level 199
       , format "'[' return;  ']'"
       , only printing).

Notation "'//' 'empty' 'decl' 'block'"
    := (Sdecl nil)
       ( in custom cpp_stmt at level 0
       , format "//  empty  decl  block"
       , only printing).
Notation "d"
    := (Sdecl (cons d nil))
       ( in custom cpp_stmt at level 0
       , d custom cpp_stmt at level 200
       , format "'[' d ']'"
       , only printing).
Notation "d1 .. d2"
    := (Sdecl (cons d1 .. (cons d2 nil) ..))
       ( in custom cpp_stmt at level 0
       , d1 custom cpp_stmt at level 200
       , d2 custom cpp_stmt at level 200
       , format "'[v' d1 '/' .. '/' d2 ']' '//'"
       , only printing).

Notation "ty $ v = e ;"
    := (Dvar v ty (Some e))
       ( in custom cpp_stmt at level 0
       , e custom cpp_expr at level 200
       , ty custom cpp_type at level 200
       , v constr
       , format "'[' ty  $ v  =  e ; ']'"
       , only printing).


Notation "'if' ( t ) { thn } 'else' { els }"
    := (Sif None t thn els)
       ( in custom cpp_stmt at level 200
       , t custom cpp_expr at level 200
       , thn custom cpp_stmt at level 200
       , els custom cpp_stmt at level 200
       , format "'[hv' if ( t )  { '//'   thn '//' }  else  { '//'   els '//' } ']'"
       , only printing).
Notation "'while' ( t ) { bod }"
    := (Swhile None t bod)
       ( in custom cpp_stmt at level 200
       , t custom cpp_expr at level 200
       , bod at level 100
       , format "'[hv' while ( t )  { '//'   bod '//' } ']'"
       , only printing).
Notation "'while' ( t $ i = e ) { bod }"
    := (Swhile (Some (Dvar i t (Some e))) _ bod)
       ( in custom cpp_stmt at level 200
       , t custom cpp_type at level 100
       , e custom cpp_expr at level 200
       , bod at level 100
       , i constr
       , format "'[hv' while ( '[' t  $ i  =  e ']' )  { '//'   bod '//' } ']'"
       , only printing).


Notation "'do' { bod } 'while' ( e ) ;"
    := (Sdo bod e)
       ( in custom cpp_stmt at level 200
       , e custom cpp_expr at level 200
       , bod custom cpp_stmt at level 200
       , format "'[hv' do  { '//'   bod '//' }  while ( e ) ; ']'"
       , only printing).

(** Tests *)
Definition E (e : Expr) : Prop := True.
Definition S (s : Stmt) : Prop := True.
Definition T (t : type) : Prop := True.

Arguments E (_%cexpr).
Arguments S (_%cstmt).

(*
Check E (Ebinop Badd (Ederef (Eaddrof (Evar (Lname "hello") Tvoid)) Tvoid)
                (Eint 3%Z Tvoid) Tvoid).


Check S (Sseq (Sexpr Lvalue (Evar (Lname "hello") Tvoid) :: Scontinue :: Sbreak :: Sexpr Lvalue (Evar (Lname "world") Tvoid) :: Sif None (Evar (Lname "world") Tvoid) Scontinue Sbreak :: nil)).
*)

Notation "'if' ( t $ i = e ) { thn } 'else' { els }"
    := (Sif (Some (Dvar i%bs t (Some e))) _ thn els)
       ( in custom cpp_stmt at level 200
       , t custom cpp_type at level 100
       , e custom cpp_expr at level 200
       , thn custom cpp_stmt at level 200
       , els custom cpp_stmt at level 200
       , i constr
       , format "'[hv' if ( '[  ' t  $ i  =  e ']' )  { '//'   thn '//' }  else  { '//'   els '//' } ']'"
       , only printing).

Import List.ListNotations.
Set Printing Width 400.
Check
  S (Sseq (
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
              ]
    )).

Check
  S (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Scontinue)
                (Sseq [Scontinue;Scontinue;Scontinue;Scontinue])
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sreturn None
              ]
    )).

Check
  S (Sseq (
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
  S (Sseq (
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
  S (Sseq (
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
  S (Sseq (
         (Sdo
            (Sseq (
                 (Sexpr Prvalue
                        (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
            (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))
         ) :: nil)).

Check
  S (Sseq (
         (Sdo
            (Sseq (
                 (Sexpr Lvalue
                        (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)) :: nil))
            (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))
         ) :: nil)).

Check
  S (Sexpr Lvalue
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
(*
                     [Ecast Cl2r Lvalue
                        (Evar (Lname "ctx")
                           (Tqualified {| q_const := true; q_volatile := false |}
                              (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid))))
                        (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                     Ecast Carray2pointer Lvalue (Evar (Lname "buffer") (Tarray Tu8 1024)) (Tptr Tu8);
                     Eread_ref (Evar (Lname "shared") (Tnamed "_Z9UmxShared"));
                     Eread_ref (Evar (Lname "client") Tu64); Evar (Lname "result") Ti32]
*)
                     [] Tbool) Tbool)
               Tbool)).
*)
