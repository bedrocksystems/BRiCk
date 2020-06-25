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
Require Import bedrock.lang.cpp.logic.dispatch.

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.
  Variable (ti : thread_info).

  Local Notation _sub := (_sub (resolve:=σ)) (only parsing).
  Local Notation anyR := (anyR (resolve:=σ)) (only parsing).
  Local Notation _global := (_global (resolve:=σ)) (only parsing).

  (* this destructs an object by invoking its destructor
     note: it does *not* free the underlying memory.
   *)
  Definition destruct_obj (dtor : obj_name) (cls : globname) (v : val) (Q : mpred) : mpred :=
    match σ.(genv_tu) !! cls with
    | Some (Gstruct s) =>
      match s.(s_virtual_dtor) with
      | Some dtor =>
        resolve_virtual (σ:=σ) (_eqv v) cls dtor (fun da p =>
                   |> fspec ti (Vptr da) (Vptr p :: nil) (fun _ => Q))
      | None =>
        Exists da, _global dtor &~ da **
                   |> fspec ti (Vptr da) (v :: nil) (fun _ => Q)
      end
    | _ => lfalse
    end.

  (* [destruct_val t this dtor Q] invokes the destructor ([dtor]) on [this]
     with the type of [this] is [t].

     note: it does *not* free the underlying memory.
   *)
  Fixpoint destruct_val (t : type) (this : val) (dtor : obj_name) (Q : mpred)
           {struct t}
  : mpred :=
    match t with
    | Tqualified _ t => destruct_val t this dtor Q
    | Tnamed cls =>
      destruct_obj dtor cls this Q
    | Tarray t sz =>
      fold_right (fun i Q =>
         Exists p, _offsetL (_sub t (Z.of_nat i)) (_eqv this) &~ p ** destruct_val t (Vptr p) dtor Q) Q (List.rev (seq 0 (N.to_nat sz)))
    | _ => empSP
    end.

  (* call the destructor (if available) and delete the memory *)
  Definition mdestroy (ty : type) (this : val) (dtor : option obj_name) (Q : mpred)
  : mpred :=
    match dtor with
    | None => fun x => x
    | Some dtor => destruct_val ty this dtor
    end (_at (_eqv this) (anyR (erase_qualifiers ty) 1) ** Q).

End destroy.
