(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(* This file contains intensional functions necessary to
 * describe the semantics of our AST.
 *
 * It would be great if we could eliminate this, but it
 * requires some more thought.
 *
 * Another option would be to completely pre-process the
 * AST and remove these nodes.
 *)
Require Import Coq.ZArith.ZArith_base.
Require Import bedrock.lang.cpp.ast.

(* this function determines whether the type is an aggregate type, i.e.
 * arrays and objects.
 *)
Fixpoint is_aggregate (t : type) : bool :=
  match t with
  | Tnamed _
  | Tarray _ _ => true
  | Tqualified _ t => is_aggregate t
  | _ => false
  end.

Fixpoint is_void (t : type) : bool :=
  match t with
  | Tqualified _ t => is_void t
  | Tvoid => true
  | _ => false
  end.

(* this determines whether a type is initializable from a primitive.
 *)
Fixpoint prim_initializable (t : type) : bool :=
  match t with
  | Tpointer _
  | Tnum _ _
  | Tbool
  | Tenum _
  | Tnullptr => true
  | Tqualified _ t => prim_initializable t
  | _ => false
  end.
