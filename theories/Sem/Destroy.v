(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.ZArith.
Require Import Cpp.Ast.
From Cpp.Sem Require Import
     Semantics Logic Wp PLogic.

Section destroy.
  Context {Σ:gFunctors}.
  Context (ti : thread_info).

  Local Notation mpred := (mpred Σ) (only parsing).

  (* remove from the stack *)
  Definition destruct_obj (dtor : obj_name) (cls : globname) (v : val) (Q : mpred) : mpred :=
    Exists da, _global dtor &~ da **
               |> fspec da (v :: nil) ti
                        (fun _ => Q).

  Fixpoint destruct (t : type) (this : val) (dtor : obj_name) (Q : mpred)
           {struct t}
  : mpred :=
    match t with
    | Tqualified _ t => destruct t this dtor Q
    | Tref cls =>
      destruct_obj dtor cls this Q
    | Tarray t sz =>
      let destruct_at i :=
          Exists p, _offsetL (_sub t (Z.of_nat i)) (_eq this) &~ p ** destruct t p dtor empSP
      in
      sepSPs (List.map destruct_at (List.seq 0 (N.to_nat sz - 1)))
    | _ => empSP
    end.

  (* call the destructor (if available) and delete the memory *)
  Definition mdestroy (ty : type) (this : val) (dtor : option obj_name) (Q : mpred)
  : mpred :=
    match dtor with
    | None => fun x => x
    | Some dtor => destruct ty this dtor
    end (_at (_eq this) (tany (erase_qualifiers ty) 1) ** Q).

End destroy.
