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
  Fixpoint base_to_derived `(d : !class_derives σ derived base) : offset :=
    match d with
    | Derives_here st _ => o_id
    | Derives_base base st _ _ _ _ d =>
      o_dot (base_to_derived d) (o_derived σ base derived)
    end.

  (* the [offset] to cast a [derived] to a [base] *)
  Fixpoint derived_to_base `(d : !class_derives σ derived base) : offset :=
    match d with
    | Derives_here st _ => o_id
    | Derives_base base st _ _ _ _ d =>
      o_dot (o_base σ derived base) (derived_to_base d)
    end.

  (** If successful, returns a pair of the function pointer to the
   *  implementation and the downcast for [this] pointer. *)
  Definition get_impl `(r : !class_derives σ mdc tcls) (f : obj_name)
    : option (ptr * offset) :=
    let override := dispatch σ r f in
    s ← override.(vimpl);
    mret (_global s, base_to_derived override.(derivation)).

  (** [resolve_virtual σ this cls f Q] returns [Q fa this'] if resolving [f] on
   * [this] results in a function that is equivalent to calling the pointer [fa]
   * passing [this'] as the "this" argument.
   *)
  Definition resolve_virtual {σ : genv}
             (this : ptr) (cls : globname) (f : obj_name)
             (Q : forall (faddr : ptr) (cls_type : globname) (this_addr : ptr), mpred) : mpred :=
    Exists σ' mdc (pf : class_derives σ' mdc cls),
        (* ^ we quantify over another program environment because class
             extension is open, the caller does not need to know the target
             function.
           - the [class_derives] fact *must* be in [σ'] because [mdc] might
             not exist in [σ].
         *)
    (Exists q, this |-> identityR (σ:=σ') cls (Some mdc) q  **
                 [| class_compatible σ.(genv_tu) σ'.(genv_tu) cls |] ** True) //\\
              (* ^ the [class_compatible σ σ' cls] ensures that the virtual
                   tables the [cls] class are compatible between the (possibly
                   different) translation units.
               *)
      match get_impl pf f with
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
