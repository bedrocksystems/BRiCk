(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Cpp Require Import
     Ast.

Fixpoint type_of (e : Expr) : type :=
  match e with
  | Econst_ref _ t
  | Evar _ t
  | Echar _ t
  | Estring _ t
  | Eint _ t => t
  | Ebool _ => Tbool
  | Eunop _ _ t
  | Ebinop _ _ _ t
  | Ederef _ t
  | Eaddrof _ t
  | Eassign _ _ t
  | Eassign_op _ _ _ t
  | Epreinc _ t
  | Epostinc _ t
  | Epredec _ t
  | Epostdec _ t
  | Eseqand _ _ t
  | Eseqor _ _ t
  | Ecomma _ _ _ t
  | Ecall _ _ t
  | Ecast _ _ t
  | Emember _ _ t
  | Emember_call _ _ _ _ t
  | Esubscript _ _ t
  | Esize_of _ t
  | Ealign_of _ t
  | Econstructor _ _ t
  | Eimplicit _ t
  | Eif _ _ _ t
  | Ethis t => t
  | Enull => Tpointer Tvoid
  (* todo(gmm): c++ seems to have a special nullptr type *)
  | Einitlist _ t => t
  | Enew _ _ _ t
  | Edelete _ _ _ t
  | Eandclean _ t
  | Etemp _ t => t
  | Eatomic _ _ t => t
  end.
