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
From bedrock.lang.cpp.logic Require Import wp translation_unit.
Require Import bedrock.lang.cpp.heap_notations.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** [base_to_derived derived path] is the offset to [derived]
      from the path [path]. For example,
      [[
      Eval simpl in base_to_derived "::D" ["::B";"::A";"::X"]%bs.
      (* = o_id ,, o_derived σ "::X" "::A" ,, o_derived σ "::A" "::B" ,, o_derived σ "::B" "::D" *)
      ]]

      NOTE the arguments are the same as [derived_to_base] but the direction
           of the cast is swapped.
   *)
  Fixpoint base_to_derived {σ : genv} (derived : globname) (path : list globname) : offset :=
    match path with
    | nil => o_id
    | base :: rest => o_dot (base_to_derived base rest) (o_derived σ base derived)
    end.

  (** [derived_to_base derived path] is the offset from [derived]
      from the path [path]. For example,
      [[
      Eval simpl in derived_to_base "::D" ["::B";"::A";"::X"]%bs.
      (* =  o_base σ "::D" "::B" ,, (o_base σ "::B" "::A" ,, (o_base σ "::A" "::X" ,, o_id)) *)
      ]]

      NOTE the arguments are the same as [base_to_derived] but the direction
           of the cast is swapped.
   *)
  Fixpoint derived_to_base {σ : genv} (derived : globname) (path : list globname) : offset :=
    match path with
    | nil => o_id
    | base :: rest => o_dot (o_base σ derived base) (derived_to_base base rest)
    end.

  (** If successful, returns a pair of the function pointer to the
   *  implementation and the downcast for [this] pointer. *)
  Definition get_impl {σ} (base : globname) (path : list globname) (f : obj_name)
    : option (ptr * globname * offset) :=
    match dispatch.dispatch σ base path f with
    | None => None
    | Some (cls, path, fptr) => Some (_global fptr, cls, base_to_derived cls path)
    end.

  Section tu.
    Context `{σ : genv}.
    Variable tu : translation_unit.

    Definition tu_get_impl (base : globname) (path : list globname) (f : obj_name)
      : option (ptr * globname * offset) :=
      match dispatch.tu_dispatch tu base path f with
      | Some (cls, path, fptr) => Some (_global fptr, cls, base_to_derived cls path)
      | None => None
      end.

    Lemma tu_get_impl_ok (MOD : tu ⊧ σ) : forall base path fn a b c,
        tu_get_impl base path fn = Some (a, b, c) ->
        get_impl base path fn = Some (a, b, c).
    Proof.
      rewrite /tu_get_impl/get_impl; intros.
      do 3 (case_match; try congruence).
      erewrite tu_dispatch_ok; eauto.
    Qed.

    Lemma resolve_match_get_impl (MOD : tu ⊧ σ) {PROP : bi} base path fn a b c (P : _ -> PROP) :
        tu_get_impl base path fn = Some (a, b, c) ->
        P (a, b, c) -|-
      match get_impl base path fn with
      | Some x => P x
      | None => False
      end.
    Proof. intros; erewrite tu_get_impl_ok; eauto. Qed.
  End tu.

  (** [resolve_virtual σ this cls f Q] returns [Q fa this'] if resolving [f] on
      [this] results in a function that is equivalent to calling the pointer [fa]
      passing [this'] as the "this" argument.
   *)
  Definition resolve_virtual
             (this : ptr) (cls : globname) (f : obj_name)
             (Q : forall (faddr : ptr) (cls_type : globname) (this_addr : ptr), mpred)
    : mpred :=
    Exists (path : list globname) σ tu, denoteModule (resolve:=σ) tu **
      ((Exists q, this |-> identityR cls path q ** [| path <> nil |] ** True) //\\
      match get_impl cls path f with
      | Some (fa, cls, off) => Q fa cls (_offset_ptr this off)
      | None => (* the function was not found or the implementation was pure virtual *)
        False
      end).

  Lemma resolve_virtual_frame (cls : globname) (this : ptr) s
    (Q Q' : ptr → globname → ptr → mpredI) :
        Forall (a : ptr) (b : globname) (c : ptr), Q a b c -* Q' a b c
    |-- resolve_virtual this cls (s_dtor s) Q -* resolve_virtual this cls (s_dtor s) Q'.
  Proof.
    intros.
    rewrite /resolve_virtual.
    iIntros "X Y".
    iDestruct "Y" as (path ? ?) "[? Y]".
    iExists path, _, _; iFrame.
    iSplit.
    { iDestruct "Y" as "[$ _]". }
    { iDestruct "Y" as "[_ Y]". case_match => //.
      destruct p as [[??]?]. by iApply "X". }
  Qed.

End with_cpp.
