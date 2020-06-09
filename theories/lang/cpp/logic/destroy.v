(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.ZArith.ZArith.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred wp path_pred heap_pred.

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.
  Variable (ti : thread_info).

  Local Notation _sub := (_sub (resolve:=σ)) (only parsing).
  Local Notation anyR := (anyR (resolve:=σ)) (only parsing).
  Local Notation _global := (_global (resolve:=σ)) (only parsing).

  (* remove from the stack *)
  Definition destruct_obj (dtor : obj_name) (cls : globname) (v : val) (Q : mpred) : mpred :=
    Exists da, _global dtor &~ da **
               |> fspec ti (Vptr da) (v :: nil) (fun _ => Q).

  Fixpoint destruct (t : type) (this : val) (dtor : obj_name) (Q : mpred)
           {struct t}
  : mpred :=
    match t with
    | Tqualified _ t => destruct t this dtor Q
    | Tnamed cls =>
      destruct_obj dtor cls this Q
    | Tarray t sz =>
      let destruct_at i :=
          Exists p, _offsetL (_sub t (Z.of_nat i)) (_eqv this) &~ p ** destruct t (Vptr p) dtor empSP
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
    end (_at (_eqv this) (anyR (erase_qualifiers ty) 1) ** Q).

End destroy.
