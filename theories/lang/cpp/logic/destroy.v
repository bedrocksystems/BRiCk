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

Require Import bedrock.lang.cpp.heap_notations.

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.
  Variable (ti : thread_info).

  Local Notation _sub := (o_sub σ) (only parsing).
  Local Notation anyR := (anyR (resolve:=σ)) (only parsing).
  Local Notation _global := (_global (resolve:=σ)) (only parsing).

  (* this destructs an object by invoking its destructor
     note: it does *not* free the underlying memory.
   *)
  Definition destruct_obj (dtor : obj_name) (cls : globname) (v : ptr) (Q : mpred) : mpred :=
    match σ.(genv_tu) !! cls with
    | Some (Gstruct s) =>
      match σ.(genv_tu) !! dtor with
      | Some ov =>
        let ty := type_of_value ov in
        match s.(s_virtual_dtor) with
        | Some dtor =>
          resolve_virtual (σ:=σ) v cls dtor (fun da p =>
             |> fspec σ.(genv_tu).(globals) ty ti (Vptr da) (Vptr p :: nil) (fun _ => Q))
        | None =>
             |> fspec σ.(genv_tu).(globals) ty ti (Vptr $ _global dtor) (Vptr v :: nil) (fun _ => Q)
        end
      | _ => False
      end
    | _ => False
    end.

  (* [destruct_val t this dtor Q] invokes the destructor ([dtor]) on [this]
     with the type of [this] is [t].

     note: it does *not* free the underlying memory.
   *)
  Fixpoint destruct_val (t : type) (this : ptr) (dtor : option obj_name) (Q : mpred)
           {struct t}
  : mpred :=
    match t with
    | Tqualified _ t => destruct_val t this dtor Q
    | Tnamed cls =>
      match dtor with
      | None => Q
      | Some dtor => destruct_obj dtor cls this Q
      end
    | Tarray t sz =>
      fold_right (fun i Q => valid_ptr (this .[ t ! Z.of_nat i ]) **
         destruct_val t (this .[ t ! Z.of_nat i ]) dtor Q) Q (List.rev (seq 0 (N.to_nat sz)))
    | _ => emp
    end.

End destroy.
