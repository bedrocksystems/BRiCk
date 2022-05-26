(*
 * Copyright (c) 2019-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.ZArith.ZArith.

Require bedrock.lang.cpp.ast.
From bedrock.lang.cpp.syntax Require Import names stmt expr_notations type_notations.

#[local] Open Scope Z_scope.
#[local] Open Scope bs_scope.

(* TODO (JH): Investigate which (if any) of the subsequent notations we can make
   printing/parsing
 *)
Module Export StmtNotations.
  Declare Custom Entry CPP_stmt.
  Declare Scope CPP_stmt_scope.
  Delimit Scope CPP_stmt_scope with cpp_stmt.
  (* TODO (JH): Determine if we want (something like) this, and then do it. *)
  Bind Scope CPP_stmt_scope with Stmt.

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

  (* Statements that provide their own line break

     NOTES (JH):
     - [Stmt]s will be enclosed in [{(stmt: ...)}], so we don't include curly braces here.
     - terminal [Stmt]s will have notations which insert semicolons (and the appropriate
       spacing after them).
   *)
  Notation "'//' 'end' 'block'"
      := (Sseq nil)
         ( in custom CPP_stmt at level 0
         , format "'[' //  end  block ']'"
         , only printing).
  Notation "s"
      := (Sseq (cons s nil))
         ( in custom CPP_stmt at level 0
         , s custom CPP_stmt at level 200
         , format "'[' s ']'"
         , only printing).
  Notation "s1 .. s2 '//' 'end' 'block'"
      := (Sseq (cons s1 .. (cons s2 nil) ..))
         ( in custom CPP_stmt at level 0
         , s1 custom CPP_stmt at level 200
         , s2 custom CPP_stmt at level 200
         , format "'[v' s1 '/' .. '/' s2 '//' //  end  block ']'"
         , only printing).

  (* TODO (JH): Notations for other [VarDecl] forms *)
  Notation "ty $ v = e ;"
      := (Dvar v%bs ty (Some e))
         ( in custom CPP_stmt at level 0
         , e custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , v constr
         , format "'[' ty  $ v  =  e ; ']'"
         , only printing).

  Notation "'//' 'end' 'decl' 'block'"
      := (Sdecl nil)
         ( in custom CPP_stmt at level 0
         , format "//  end  decl  block"
         , only printing).
  Notation "d"
      := (Sdecl (cons d nil))
         ( in custom CPP_stmt at level 0
         , d custom CPP_stmt at level 200
         , format "'[' d ']'"
         , only printing).
  Notation "d1 .. d2"
      := (Sdecl (cons d1 .. (cons d2 nil) ..))
         ( in custom CPP_stmt at level 0
         , d1 custom CPP_stmt at level 200
         , d2 custom CPP_stmt at level 200
         , format "'[v' d1 '/' .. '/' d2 ']' '//'"
         , only printing).

  Notation "'if' ( cond ) { thn } 'else' { els }"
      := (Sif None cond thn els)
         ( in custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , thn custom CPP_stmt at level 200
         , els custom CPP_stmt at level 200
         , format "'[hv' if  ( cond )  { '//'   thn '//' }  else  { '//'   els '//' } ']'"
         , only printing).
  Notation "'if' ( decl cond ) { thn } 'else' { els }"
      := (Sif (Some decl) cond thn els)
         ( in custom CPP_stmt at level 200
         , decl custom CPP_stmt
         , cond custom CPP_expr at level 200
         , thn custom CPP_stmt at level 200
         , els custom CPP_stmt at level 200
         , format "'[hv' if  ( '[hv   ' decl  '/' cond ']' )  { '//'   thn '//' }  else  { '//'   els '//' } ']'"
         , only printing).

  Notation "'while' ( cond ) { body }"
      := (Swhile None cond body)
         ( in custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' while  ( cond )  { '//'   body '//' } ']'"
         , only printing).
  Notation "'while' ( decl cond ) { body }"
      := (Swhile (Some decl) cond body)
         ( in custom CPP_stmt at level 200
         , decl custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' while  ( '[hv  ' decl  '/' cond ']' )  { '//'   body '//' } ']'"
         , only printing).

  Notation "'for' '(;;)' { body }"
      := (Sfor None None None body)
         ( in custom CPP_stmt at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  (;;)  { '//'   body '//' } ']'"
         , only printing).
  (* NOTE (JH): init will insert a semicolon since it will be a terminal stmt in realistic ASTs *)
  Notation "'for' ( init ';)' { body }"
      := (Sfor (Some init) None None body)
         ( in custom CPP_stmt at level 200
         , init custom CPP_stmt at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  ( init  ;)  { '//'   body '//' } ']'"
         , only printing).
  Notation "'for' '(;' cond ';)' { body }"
      := (Sfor None (Some cond) None body)
         ( in custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  (;  cond ;)  { '//'   body '//' } ']'"
         , only printing).
  Notation "'for' '(;;' incr ) { body }"
      := (Sfor None None (Some (_, incr)) body)
         ( in custom CPP_stmt at level 200
         , incr custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  (;;  incr )  { '//'   body '//' } ']'"
         , only printing).
  (* NOTE (JH): init will insert a semicolon since it will be a terminal stmt in realistic ASTs *)
  Notation "'for' ( init cond ';)' { body }"
      := (Sfor (Some init) (Some cond) None body)
         ( in custom CPP_stmt at level 200
         , init custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  ( init  cond ;)  { '//'   body '//' } ']'"
         , only printing).
  (* NOTE (JH): init will insert a semicolon since it will be a terminal stmt in realistic ASTs *)
  Notation "'for' ( init ; incr ) { body }"
      := (Sfor (Some init) None (Some (_, incr)) body)
         ( in custom CPP_stmt at level 200
         , init custom CPP_stmt at level 200
         , incr custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  ( init ;  incr )  { '//'   body '//' } ']'"
         , only printing).
  Notation "'for' (; cond ; incr ) { body }"
      := (Sfor None (Some cond) (Some (_, incr)) body)
         ( in custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , incr custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  (;  cond ;  incr )  { '//'   body '//' } ']'"
         , only printing).
  (* NOTE (JH): init will insert a semicolon since it will be a terminal stmt in realistic ASTs *)
  Notation "'for' ( init cond ; incr ) { body }"
      := (Sfor (Some init) (Some cond) (Some (_, incr)) body)
         ( in custom CPP_stmt at level 200
         , init custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , incr custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  ( init  cond ;  incr )  { '//'   body '//' } ']'"
         , only printing).

  Notation "'do' { bod } 'while' ( e ) ;"
      := (Sdo bod e)
         ( in custom CPP_stmt at level 200
         , e custom CPP_expr at level 200
         , bod custom CPP_stmt at level 200
         , format "'[hv' do  { '//'   bod '//' }  while ( e ) ; ']'"
         , only printing).

  (* TODO (JH): [Sswitch]/[Scase]/[Sdefault] *)

  Notation "'break;'"
      := (Sbreak)
         ( in custom CPP_stmt at level 0
         , format "'[' break;  ']'"
         , only printing).

  Notation "'continue;'"
      := (Scontinue)
         ( in custom CPP_stmt at level 0
         , format "'[' continue;  ']'"
         , only printing).

  Notation "'return;'"
      := (Sreturn None)
         ( in custom CPP_stmt at level 0
         , format "'[' return;  ']'"
         , only printing).
  Notation "'return' e ;"
      := (Sreturn (Some e))
         ( in custom CPP_stmt at level 0
         , e custom CPP_expr at level 200
         , format "'[' return  e ;  ']'"
         , only printing).

  Notation "e ;"
      := (Sexpr _ e)
         ( in custom CPP_stmt at level 0
         , e custom CPP_expr at level 200
         , format "'[' e ; ']'"
         , only printing).

  Notation "s"
      := (Sattr nil s)
         ( in custom CPP_stmt at level 0
         , s custom CPP_stmt at level 200
         , format "'[' s ']'"
         , only printing).
  Notation "'[[' attr1 , .. , attr2 ']]' s"
      := (Sattr (cons attr1%bs .. (cons attr2%bs nil) ..) s)
         ( in custom CPP_stmt at level 0
         , attr1 constr
         , attr2 constr
         , s custom CPP_stmt at level 200
         , format "'[' [[ '[hv' attr1 ,  '/' .. ,  '/' attr2 ']' ]]  s ']'"
         , only printing).

  (* TODO (JH): [Sasm] *)

  Notation "'<LABEL:' lbl > s"
      := (Slabeled lbl%bs s)
         ( in custom CPP_stmt at level 0
         , lbl constr
         , s custom CPP_stmt at level 200
         , format "'[' <LABEL:  lbl >  s ']'"
         , only printing).

  Notation "'goto' lbl ;"
      := (Sgoto lbl%bs)
         ( in custom CPP_stmt at level 0
         , lbl constr
         , format "'[' goto  lbl ; ']'"
         , only printing).

  Notation "'{UNSUPPORTED:' msg }"
      := (Sunsupported msg%bs)
         ( in custom CPP_stmt at level 0
         , msg constr
         , format "'[hv   ' {UNSUPPORTED:  '/' msg } ']'"
         , only printing).
End StmtNotations.

(* NOTE: The following [Section]s are only used for testing purposes; if you break one of these
   tests - or add a new notation - please update things accordingly.
 *)

Section TestStmtNotations.
  Import bedrock.lang.cpp.ast.
  Import TypeNotations. #[local] Open Scope CPP_type_scope.
  Import ExprNotations. #[local] Open Scope CPP_expr_scope.
  Import StmtNotations. #[local] Open Scope CPP_stmt_scope.

(* Check (Sexpr Lvalue (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)). *)

(** Tests *)
(* Check (Ebinop Badd (Ederef (Eaddrof (Evar (Lname "hello") Tvoid)) Tvoid) *)
(*               (Eint 3%Z Tvoid) Tvoid). *)


(* Check (Sseq (Sexpr Lvalue (Evar (Lname "hello") Tvoid) :: Scontinue :: Sbreak :: Sexpr Lvalue (Evar (Lname "world") Tvoid) :: Sif None (Evar (Lname "world") Tvoid) Scontinue Sbreak :: nil)). *)

(*
Import List.ListNotations.
Set Printing Width 300.
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
            ]
  )).
*)

(*
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

End TestStmtNotations.
