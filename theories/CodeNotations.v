(* Notations for code.
 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Cpp.Syntax.Ast.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Declare Custom Entry cpp_type.
Declare Custom Entry cpp_expr.
Declare Custom Entry cpp_stmt.


Delimit Scope cppexpr_scope with cexpr.
Delimit Scope cppstmt_scope with cstmt.
Delimit Scope cpptype_scope with ctype.


(** Notations for types *)
Notation "'int'" := (Qmut T_int) (in custom cpp_type at level 0).

(** Notations for expressions *)
Notation "{e{ e }}" := e (at level 200, e custom cpp_expr at level 200, only printing) : expr_scope.
Notation "( e )" := e (in custom cpp_expr at level 0, e custom cpp_expr at level 200, only printing, format "'[' (  e  ) ']'").
Notation "& e" := (Eaddrof e _)
                    (in custom cpp_expr at level 10, e custom cpp_expr at level 10, format "& e", only printing).
Notation "* e" := (Ederef e _)
                    (in custom cpp_expr at level 10, e custom cpp_expr at level 10, format " * e", only printing).
Notation "# v" := (Eint v%Z _)
                    (in custom cpp_expr at level 1, v constr
                    ,format "# v", only printing).
Notation "e --" := (Epostdec e _)
                    (in custom cpp_expr at level 5, e custom cpp_expr at level 5
                    ,format "e --", only printing).
Notation "-- e" := (Epredec e _)
                    (in custom cpp_expr at level 5, e custom cpp_expr at level 5
                    ,format "-- e", only printing).
Notation "e ++" := (Epostinc e _)
                    (in custom cpp_expr at level 5, e custom cpp_expr at level 5
                    ,format "e ++", only printing).
Notation "++ e" := (Epreinc e _)
                    (in custom cpp_expr at level 5, e custom cpp_expr at level 5
                    ,format "++ e", only printing).
Notation "e1 + e2" := (Ebinop Badd e1 e2 _)
                    (in custom cpp_expr at level 50,
                     e1 custom cpp_expr,
                     e2 custom cpp_expr at level 51,
                     left associativity, only printing).
Notation "v" := (Evar (Lname v%string) _)
                    (in custom cpp_expr at level 1, v constr
                    ,format "v", only printing).
Notation ":: v" := (Evar (Gname v%string) _)
                    (in custom cpp_expr at level 1, v constr
                    ,format ":: v", only printing).


(** Notations for statements *)
Notation "{s{ e }}" := e (e custom cpp_stmt at level 200) : stmt_scope.
Notation "{ s1 ; .. ; s2 ; }" := (Sseq (@cons Stmt s1 .. (@cons Stmt s2 (@nil Stmt)) ..))
                               (in custom cpp_stmt at level 0,
                                s1 custom cpp_stmt at level 200,
                                s2 custom cpp_stmt at level 200,
                                format "'[' { '[v  ' '//' s1 ';' '//' .. ';' '//' s2 ';'  ']' '//' } ']'").
Notation "e" := (Sexpr _ e) (in custom cpp_stmt at level 0, e custom cpp_expr at level 200).
Notation "'continue'" := Scontinue (in custom cpp_stmt at level 0).
Notation "'break'" := Sbreak (in custom cpp_stmt at level 0).
Notation "'return'" := (Sreturn None) (in custom cpp_stmt at level 0).
Notation "'return' e" := (Sreturn (Some (_, e))) (in custom cpp_stmt at level 0, e custom cpp_expr at level 200).
Notation "'if' ( t ) thn 'else' els" := (Sif None t thn els)
         (in custom cpp_stmt at level 200,
          t custom cpp_expr at level 200,
          thn custom cpp_stmt at level 200,
          els custom cpp_stmt at level 200).
Notation "'while' ( t ) bod" := (Swhile None t bod)
                                  (in custom cpp_stmt at level 200,
                                   t custom cpp_expr at level 200,
                                   bod at level 100, only printing).
Notation "'while' ( t i = e ) bod" := (Swhile (Some (i, t, Some e)) _ bod)
                                  (in custom cpp_stmt at level 200,
                                   t custom cpp_type at level 100,
                                   i constr,
                                   e custom cpp_expr at level 200,
                                   bod at level 100, only printing).
Notation "≈ e" := (Ecast _ (_, e) _)
                  (in custom cpp_expr at level 0, e custom cpp_expr, only printing).

(** Tests *)
Definition E (e : Expr) : Prop := True.
Definition S (s : Stmt) : Prop := True.
Definition T (t : type) : Prop := True.

Arguments E (_%cexpr).
Arguments S (_%cstmt).

(*
Check E (Ebinop Badd (Ederef (Eaddrof (Evar (Lname "hello") Tvoid) Tvoid) Tvoid)
                (Eint 3%Z Tvoid) Tvoid).


Check S (Sseq (Sexpr Lvalue (Evar (Lname "hello") Tvoid) :: Scontinue :: Sbreak :: Sexpr Lvalue (Evar (Lname "world") Tvoid) :: Sif None (Evar (Lname "world") Tvoid) Scontinue Sbreak :: nil)).
*)

Notation "'if' ( t i = e ) thn 'else' els" := (Sif (Some (i%string, t, Some e)) _ thn els)
         (in custom cpp_stmt at level 200,
          t custom cpp_type at level 100,
          i constr,
          e custom cpp_expr at level 200,
          thn custom cpp_stmt at level 200,
          els custom cpp_stmt at level 200, only printing,
          format "'[hv' if ( t i = e )  '/' thn '//' else '//' els ']'").



Definition e0 :=
  S (Sseq (
              (Sif
                (Some ("x", (Qmut T_int), (Some (Eint (0) (Qmut T_int)))))
                (Ecast (CCcast Cint2bool) (Rvalue,
                    (Ecast (CCcast Cl2r) (Lvalue, (Evar (Lname  "x") (Qmut T_int))) (Qmut T_int))) (Qmut Tbool))
                Scontinue Sbreak) :: nil)).

Definition e1 :=
  S (Sseq (
              (Sif
                (Some ("x", (Qmut T_int), (Some (Eint (0) (Qmut T_int)))))
                (Ecast (CCcast Cint2bool) (Rvalue,
                    (Ecast (CCcast Cl2r) (Lvalue, (Evar (Lname  "x") (Qmut T_int))) (Qmut T_int))) (Qmut Tbool))
                (Sseq (
                    (Sexpr Rvalue
                      (Epostinc (Evar (Lname  "x") (Qmut T_int)) (Qmut T_int))) :: nil))
                Scontinue) ::
              nil)).

Definition e2 :=
  S (Sseq (
              (Sif
                (Some ("x", (Qmut T_int), (Some (Eint (0) (Qmut T_int)))))
                (Ecast (CCcast Cint2bool) (Rvalue,
                    (Ecast (CCcast Cl2r) (Lvalue, (Evar (Lname  "x") (Qmut T_int))) (Qmut T_int))) (Qmut Tbool))
                (Sseq (
                    (Sexpr Rvalue
                      (Epostinc (Evar (Lname  "x") (Qmut T_int)) (Qmut T_int))) :: nil))
                (Sseq (
                    (Sexpr Lvalue
                      (Epredec (Evar (Lname  "x") (Qmut T_int)) (Qmut T_int))) :: nil))) ::
              (Swhile
                (Some ("x", (Qmut T_int), (Some (Eint (5) (Qmut T_int)))))
                (Ecast (CCcast Cint2bool) (Rvalue,
                    (Ecast (CCcast Cl2r) (Lvalue, (Evar (Lname  "x") (Qmut T_int))) (Qmut T_int))) (Qmut Tbool))
                (Sseq (
                    (Sexpr Rvalue
                      (Epostdec (Evar (Lname  "x") (Qmut T_int)) (Qmut T_int))) :: nil))) :: nil)).
