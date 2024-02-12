(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.ast.

Require test.valcat_of_11_cpp.
Require test.valcat_of_14_cpp.
Require test.valcat_of_17_cpp.
Require test.valcat_of_20_cpp.

Variant Error :=
| ValCatError (_ : Expr) (observed expected : ValCat)
| ExprTypeError (_ : Expr) (observed expected : exprtype)
| DeclTypeError (_ : Expr) (observed expected : decltype)
| UnexpectedStmt (_ : Stmt)
| UnexpectedDecl (_ : ObjValue)
| MissingTest (_ : translation_unit).

Fixpoint check_expr (e : Expr) :=
  match e with
  | Ecomma (Ecast C2void e _ _) (Esizeof (inl t) _) =>
    (*
    [e] is the expression,
    [t] is `decltype((e))`
    *)
    let dterr :=
      let obs := decltype_of_expr e in
      let exp := t in
      if bool_decide (obs = exp) then [] else [DeclTypeError e obs exp]
    in
    let eterr :=
      let obs := type_of e in
      let exp := drop_reference t in
      if bool_decide (obs = exp) then [] else [ExprTypeError e obs exp]
    in
    let vcerr :=
      let obs := valcat_of e in
      let exp := (decltype_to_exprtype t).1 in
      if bool_decide (obs = exp) then [] else [ValCatError e obs exp]
    in
    dterr ++ eterr ++ vcerr
  | Eandclean e => check_expr e
  | _ => [UnexpectedStmt (Sexpr e)]
  end.

Definition check_stmt (s : Stmt) : list Error :=
  match s with
  | Sexpr e => check_expr e
  | Sdecl _ => nil
  | _ => [UnexpectedStmt s]
  end.

Definition run_test (tu : translation_unit) : list Error :=
  match tu.(symbols) !! "_Z4testv"%bs with
  | Some d =>
      match d with
      | Ofunction f =>
          match f.(f_body) with
          | Some (Impl (Sseq stmts)) =>
              flat_map check_stmt stmts
          | _ => [UnexpectedDecl d]
          end
      | _ => [UnexpectedDecl d]
      end
  | _ => [MissingTest tu]
  end.

Example test_11 : run_test valcat_of_11_cpp.module = nil :=
  ltac:(vm_compute; reflexivity).
Example test_14 : run_test valcat_of_14_cpp.module = nil :=
  ltac:(vm_compute; reflexivity).
Example test_17 : run_test valcat_of_17_cpp.module = nil :=
  ltac:(vm_compute; reflexivity).
Example test_20 : run_test valcat_of_20_cpp.module = nil :=
  ltac:(vm_compute; reflexivity).
