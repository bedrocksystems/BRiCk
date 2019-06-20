(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Cpp.Ast.
From Cpp.Sem Require Import
     Semantics Logic Wp PLogic.

(* remove from the stack *)
Definition destroy {resolve} ti (parent : Dtor_type) (cls : globname) (v : val) (Q : mpred) : mpred :=
  Exists da, _global (dtor_name parent cls) &~ da **
                     |> fspec (resolve:=resolve) da (v :: nil) ti
                     (fun _ => _at (_eq v) (tany (Tref cls)) ** Q).
