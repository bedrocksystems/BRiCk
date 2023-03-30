(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.ast.

From bedrocktest Require valcat_of_11_cpp valcat_of_14_cpp valcat_of_17_cpp valcat_of_20_cpp.

Variant Error :=
| ValCatError (_ : Expr) (observed expected : ValCat)
| TypeError (_ : Expr) (observed expected : type)
| TypeIncompatible (_ : Expr) (t vct : type)
| UnexpectedStmt (_ : Stmt)
| UnexpectedDecl (_ : ObjValue)
| MissingTest (_ : translation_unit).

Definition vc_of_type (ty : type) : ValCat :=
  match ty with
  | Tref _ => Lvalue
  | Trv_ref _ => Xvalue
  | _ => Prvalue
  end.
Definition type_compat (e : Expr) (vct t : type) : list Error :=
  if bool_decide (drop_reference vct = t) then nil
  else TypeIncompatible e vct t :: nil.

Fixpoint check_expr (e : Expr) :=
  match e with
  | Ecomma (Ecomma (Ecast C2void e _ _) (Esize_of (inl vc_expected) _)) (Esize_of (inl type_expected) _) =>
      (* [e] is the expression,
         [vc_expected] is `decltype((e))`
         [type_expected] is `decltype(e)` *)
      let terr :=
        let obs := drop_qualifiers $ type_of e in
        let exp := drop_reference type_expected in
        if bool_decide (obs = exp) then [] else [TypeError e obs exp]
      in
      let vcerr :=
        let obs := valcat_of e in
        let exp := vc_of_type vc_expected in
        if bool_decide (obs = exp) then [] else [ValCatError e obs exp]
      in
      (* type_compat e vc_expected type_expected ++ *) terr ++ vcerr
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
