(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.ZArith.ZArith.
Require Import iris.proofmode.proofmode.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred wp path_pred heap_pred const.
Require Import bedrock.lang.cpp.logic.dispatch.

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.
  Variable tu : translation_unit.

  (* [wp_destructor ty dtor this Q] is the weakest pre-condition of invoking the destructor
     [dtor] (which is the destructor for [ty] on [this].
   *)
  #[local] Definition wp_destructor (ty : type) (dtor : ptr) (this : ptr) (Q : epred) : mpred :=
    (* NOTE using [Tfunction Tvoid nil] implicitly requires all destructors
       to have C calling convention. *)
    mspec tu.(globals) ty (Tfunction Tvoid nil)
          dtor (this :: nil) (* NOTE this is the correct calling convention for member functions *)
          (fun p => Exists v, p |-> primR Tvoid (cQp.mut 1) v ** this |-> tblockR ty (cQp.mut 1) ** Q).
              (* ^ this is inlining [operand_receive] which is not accessible due to cirularity *)

  Lemma wp_destructor_frame ty dtor this Q Q' :
    Q -* Q' |-- wp_destructor ty dtor this Q -* wp_destructor ty dtor this Q'.
  Proof.
    rewrite /wp_destructor. iIntros "X"; iApply mspec_frame; iIntros (?) "Y".
    iDestruct "Y" as (vv) "Y".
    iExists vv. iDestruct "Y" as "[$ [$ ?]]". by iApply "X".
  Qed.

  (** [destroy_val ty this Q] destructs [this] (which has [ty] as its most specific type).
      If [this] is an aggregate, we invoke [ty]'s destructor (leaving any virtual
      lookup to the caller). The memory is returned to the C++ abstract machine and the
      continuation [Q] is invoked.

      NOTE in our semantics (unlike the standard) all aggregates are destroyed
      via destructors. This is justified because the only objects that do not
      have destructors according to the standard have no-op destructors. Thus,
      we can model the "not having a destructor" as an optimization. This
      choice makes the semantics more uniform. *)
  Parameter destroy_val : forall {σ : genv}, translation_unit -> type -> ptr -> epred -> mpred.
  Axiom destroy_val_frame : forall tu' ty p Q Q',
      sub_module tu tu' ->
      Q -* Q' |-- destroy_val tu ty p Q -* destroy_val tu' ty p Q'.

  Definition destroy_val_body (destroy_val : type -> ptr -> epred -> mpred)
    (ty : type) (this : ptr) (Q : epred) : mpred :=
    let UNSUPPORTED Q := destroy_val ty this Q in
    (*  ^^ we eta-expand this to avoid cbv reduction looping *)
    let '(cv, rty) := decompose_type ty in
    let (q, handle_const) :=
      if q_const cv then
        (cQp.c 1, wp_make_mutable tu this rty)
      else (cQp.m 1, id)
    in
    match rty with
    | Tnamed cls      =>
        |> handle_const (* << putting [handle_const] here makes things a little bit cleaner
                           NOTE that if the type is not defined in the translation unit, then
                                [handle_const] will also result in [False] *)
          match tu !! cls with
          | Some (Gstruct s) =>
              (* NOTE the setup with explicit destructors (even when those destructors are trivial)
                 abstracts away some of the complexities of the underlying C++ semantics that
                  the semantics itself seems less than clear about. [CITATION NEEDED]

             TODO let's find some justification in the standard. *)
              (* In the current implementation, we generate destructor even when they are implicit
             to make the framework a bit more uniform (all types have destructors) and allow
             for direct destructor calls, e.g. [c.~C()], which are encoded as
             [Emember_call ... "~C" ..] *)
              wp_destructor rty (_global s.(s_dtor)) this Q
          | Some (Gunion u)  =>
              (* Unions cannot have [virtual] destructors: we directly invoke the destructor. *)
              wp_destructor rty (_global u.(u_dtor)) this Q
          | _ => False
          end
    | Tarray ety sz   =>
      (* NOTE array elements are destroyed with non-virtual dispatch. *)
      (* TODO replace [fold_right ... rev] by [fold_left]? *)
      |> (handle_const $ fold_right (fun i Q =>
        let p := this .[ erase_qualifiers ety ! Z.of_nat i ] in
        destroy_val ety p Q) Q (rev (seq 0 (N.to_nat sz))))
    | Tref r_ty
    | Trv_ref r_ty    =>
        (* NOTE rvalue references [Trv_ref] are represented as references [Tref]. *)
        this |-> anyR (Tref $ erase_qualifiers r_ty) q ** Q
    | Tnum _ _
    | Tchar_ _
    | Tfloat _
    | Tenum _
    | Tbool
    | Tnullptr
    | Tptr _
    | Tmember_pointer _ _
    | Tvoid =>
        (* if the field is a constant, then you only reclaim the portion given to the program *)
        this |-> anyR (erase_qualifiers ty) q ** Q
    | Tfunction _ _ => UNSUPPORTED Q
    | Tarch _ _ => UNSUPPORTED Q
    | Tqualified q ty => False
    end%I.

  Axiom destroy_val_intro : forall ty p Q,
      destroy_val_body (destroy_val tu) ty p Q |-- destroy_val tu ty p Q.

  Lemma destroy_val_body_frame : forall ty q_c this (Q Q' : epred),
      Q -* Q' |-- destroy_val q_c ty this Q -* destroy_val q_c ty this Q'.
  Proof.
    (* TODO: Prove this
    intro ty; induction ty; simpl; eauto;
      try solve [ intros; iIntros "Q [$ X]"; iRevert "X"; done ].
    - induction (rev _); first done.
      by iIntros (q_c ptr Q Q') "W"; iApply IHty; iApply IHl.
    - intros. case_match; eauto.
      by case_match; eauto; (try case q_c);
        iIntros "A B !>"; iRevert "B";
        (try iApply cv_cast_frame; try reflexivity);
        iApply wp_destructor_frame.
  Qed. *) Abort.

  (* BEGIN interp *)
  (** [interp free Q] "runs" [free] and then acts like [Q].

      NOTE this could directly support update modalities like regular [wp]s
           but in practice it is always going to occur at the end of a [wp] which
           means it will already have access to a fancy update.
   *)
  Fixpoint interp (free : FreeTemps) (Q : epred) : mpred :=
    match free with
    | FreeTemps.id => Q
    | FreeTemps.seq f g => interp f $ interp g Q
    | FreeTemps.par f g => Exists Qf Qg, interp f Qf ** interp g Qg ** (Qf -* Qg -* Q)
    | FreeTemps.delete ty addr => destroy_val tu ty addr Q
    | FreeTemps.delete_va va addr => addr |-> varargsR va ** Q
    end.
  (* END interp *)

  Lemma interp_frame free : forall Q1 Q2,
      Q1 -* Q2 |-- interp free Q1 -* interp free Q2.
  Proof.
    induction free; simpl; intros; eauto.
    { iIntros "X"; iApply destroy_val_frame; done. }
    { iIntros "X [$ Y]". iApply "X". done. }
    { iIntros "a"; iApply IHfree1; iApply IHfree2; done. }
    { iIntros "a b"; iDestruct "b" as (??) "(x & y & z)"; iExists _; iExists _; iFrame.
      iIntros "f g"; iApply "a"; iRevert "g"; by iApply "z". }
  Qed.

End destroy.
