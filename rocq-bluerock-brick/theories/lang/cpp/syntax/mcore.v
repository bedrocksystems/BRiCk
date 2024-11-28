(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.syntax.prelude.
Require Export bedrock.lang.cpp.syntax.core.

#[local] Set Primitive Projections.

(** ** C++ with templates *)
Import lang.

Notation Mname := (name' temp).
Notation Mglobname := (globname' temp).
Notation Mobj_name := (obj_name' temp).
Notation Mtype := (type' temp).
Notation Mexprtype := (exprtype' temp).
Notation Mdecltype := (decltype' temp).
Notation MCast := (Cast' temp).
Notation Moperator_impl := (operator_impl' temp).
Notation MMethodRef := (MethodRef' temp).
Notation MExpr := (Expr' temp).
Notation Mfunction_type := (function_type' temp).
Notation Mtemp_param := (temp_param' temp).
Notation Mtemp_arg := (temp_arg' temp).
Notation Mfunction_name := (function_name' temp).
Notation Matomic_name := (atomic_name' temp).
Notation MBindingDecl := (BindingDecl' lang.temp).
Notation MVarDecl := (VarDecl' temp).
Notation MStmt := (Stmt' temp).
Notation Mfield_name := (field_name.t temp).
