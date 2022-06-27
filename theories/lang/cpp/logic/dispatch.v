(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
 * reflecting virtual function dispatch in the logic.
 *)
Require Import iris.proofmode.proofmode.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import pred heap_pred path_pred.
Require Import bedrock.lang.cpp.logic.wp.
Require Import bedrock.lang.cpp.heap_notations.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* the [offset] to cast a [base] to a [derived] *)
  Fixpoint base_to_derived {σ : genv} (base : globname) (path : list globname) : offset :=
    match path with
    | nil => o_id
    | derived :: rest => o_dot (o_derived σ base derived) (base_to_derived derived rest)
    end.

  (* the [offset] to cast a [derived] to a [base] *)
  Fixpoint derived_to_base {σ : genv} (derived : globname) (path : list globname) : offset :=
    match path with
    | nil => o_id
    | base :: rest => o_dot (o_base σ derived base) (derived_to_base base rest)
    end.

  (** If successful, returns a pair of the function pointer to the
   *  implementation and the downcast for [this] pointer. *)
  Definition get_impl {σ} (base : globname) (path : list globname) (f : obj_name)
    : option (ptr * offset) :=
    match dispatch.dispatch σ base path f with
    | None => None
    | Some (path, fptr) => Some (_global fptr, base_to_derived base path)
    end.

  (** [resolve_virtual σ this cls f Q] returns [Q fa this'] if resolving [f] on
   * [this] results in a function that is equivalent to calling the pointer [fa]
   * passing [this'] as the "this" argument.
   *)
  Definition resolve_virtual {σ : genv}
             (this : ptr) (cls : globname) (f : obj_name)
             (Q : forall (faddr : ptr) (cls_type : globname) (this_addr : ptr), mpred) : mpred :=
    Exists σ' mdc (path : list globname),
      [| class_derives cls path |] **
        (* ^ we quantify over another program environment because class
             extension is open, the caller does not need to know the target
             function.
           - the [class_derives] fact *must* be in [σ'] because [mdc] might
             not exist in [σ].
         *)
    (<absorb> Exists q, this |-> identityR (σ:=σ') cls path q) //\\
              (* ^ the [class_compatible σ σ' cls] ensures that the virtual
                   tables the [cls] class are compatible between the (possibly
                   different) translation units.
               *)
      match get_impl cls path f with
      | Some (fa, off) => Q fa mdc (_offset_ptr this off)
      | None => (* the function wasn't found or the implementation was pure virtual *)
        False
      end.

  Lemma resolve_virtual_frame:
    ∀ {σ : genv} (cls : globname) (this : ptr) (Q Q' : ptr → globname → ptr → mpredI) (s : Struct),
      Forall (a : ptr) (b : globname) (c : ptr), Q a b c -* Q' a b c
      |-- resolve_virtual this cls (s_dtor s) Q -* resolve_virtual this cls (s_dtor s) Q'.
  Proof.
    intros.
    rewrite /resolve_virtual.
    iIntros "X". iDestruct 1 as (a b c) "Y"; iExists a, b, c.
    iSplit.
    { iDestruct "Y" as "[$ _]". }
    { iDestruct "Y" as "[_ Y]". case_match => //.
      destruct p. by iApply "X". }
  Qed.

End with_cpp.
