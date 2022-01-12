(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.ZArith.ZArith.
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred wp path_pred heap_pred.
Require Import bedrock.lang.cpp.logic.dispatch.

Require Import bedrock.lang.cpp.heap_notations.

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.

  (** [resolve_dtor cls this Q] reduces to [Q dtor' this'] where [dtor'] is the
      destructor to be called on [this'] which is used to destroy [this].
   *)
  Definition resolve_dtor (cls : globname) (this : ptr) (Q : forall (faddr : ptr) (cls_name : globname) (this_addr : ptr), mpred)
    : mpred :=
    match σ.(genv_tu) !! cls with
    | Some (Gstruct s) =>
      if has_virtual_dtor s then
        resolve_virtual this cls s.(s_dtor) Q
      else
        Q (_global s.(s_dtor)) cls this
    | Some (Gunion u) => Q (_global u.(u_dtor)) cls this
    | _ => False
    end%I.

  Lemma resolve_dtor_frame : forall cls this Q Q',
      Forall a b c, Q a b c -* Q' a b c |-- resolve_dtor cls this Q -* resolve_dtor cls this Q'.
  Proof.
    rewrite /resolve_dtor.
    intros. case_match; eauto.
    case_match; eauto.
    { iIntros "X"; iApply "X". }
    { case_match.
      { iApply resolve_virtual_frame. }
      { iIntros "X"; iApply "X". } }
  Qed.

  (** [delete_val dispatch ty this Q] destruct [this] (which is of type [ty]).
      The memory is returned to the C++ abstract machine. The continuation [Q]
      is applied to the destroyed pointer [p] (it might not be equal to [this]
      when virtual dispatch is used) and the type [ty] from which qualifiers
      are erased.

      The [dispatch] parameter determines whether the call is a *potentially*
      virtual call. If [dispatch] is true *and the destructor of the class is
      virtual*, then the call is a virtual call.

      NOTE in our semantics (unlike the standard) all objects are destroyed
      via destructors. This is justified because the only objects that do not
      have destructors according to the standard have no-op destructors. Thus,
      we can model the "not having a destructor" as an optimization. This
      choice makes the semantics more uniform. *)
  Fixpoint delete_val (dispatch : bool) (ty : type) (this : ptr)
                      (Q : ptr -> type -> mpred) {struct ty} : mpred :=
    match ty with
    | Tqualified _ ty => delete_val dispatch ty this Q
    | Tnamed cls      =>
      match σ.(genv_tu) !! cls with
      | Some (Gstruct s) =>
        match dispatch && has_virtual_dtor s with
        | true =>
          (* In this case, use virtual dispatch to invoke the destructor. *)
          resolve_dtor cls this (fun fimpl impl_class this' =>
            let r_ty := Tnamed impl_class in
            |> mspec σ.(genv_tu).(globals) r_ty (Tfunction Tvoid nil)
                     (Vptr fimpl) (Vptr this' :: nil)
                     (fun _ => this' |-> tblockR r_ty 1 ** Q this' r_ty)
          )
        | _    =>
          (* NOTE the setup with explicit destructors (even when those destructors are trivial)
                  abstracts away some of the complexities of the underlying C++ semantics that
                  the semantics itself seems less than clear about. [CITATION NEEDED]

             TODO let's find some justification in the standard. *)
          (* In the current implementation, we generate destructor even when they are implicit
             to make the framework a bit more uniform (all objects have destructors) and allow
             for direct desructor calls, e.g. [c.~C()], which are encoded as
             [Emember_call ... "~C" ..] *)
          (* NOTE using [Tfunction Tvoid nil] implicitly requires all destructors
             to have C calling convention. *)
          |> mspec σ.(genv_tu).(globals) ty (Tfunction Tvoid nil)
                   (Vptr $ _global s.(s_dtor)) (Vptr this :: nil)
                   (fun _ => this |-> tblockR ty 1 ** Q this ty)
        end
      | Some (Gunion u)  =>
        (* Unions cannot have [virtual] destructors: we directly invoke the destructor. *)
        |> mspec σ.(genv_tu).(globals) ty (Tfunction Tvoid nil)
                 (Vptr $ _global u.(u_dtor)) (Vptr this :: nil)
                 (fun _ => this |-> tblockR ty 1 ** Q this ty)
      | _                => False
      end
    | Tarray ety sz   =>
      (* NOTE array elements are destroyed with non-virtual dispatch. *)
      (* TODO replace [fold_right ... rev] by [fold_left]? *)
      fold_right (fun i Q =>
        let p := this .[ erase_qualifiers ety ! Z.of_nat i ] in
        valid_ptr p ** delete_val false ety p (fun _ _ => Q)
      ) (Q this (erase_qualifiers ty)) (rev (seq 0 (N.to_nat sz)))
    | Tref r_ty
    | Trv_ref r_ty    =>
      (* NOTE rvalue references [Trv_ref] are represented as references [Tref]. *)
      this |-> anyR (Tref $ erase_qualifiers r_ty) 1 **
      Q this (erase_qualifiers ty)
    | ty              =>
      this |-> anyR (erase_qualifiers ty) 1 **
      Q this (erase_qualifiers ty)
    end%I.

  Lemma delete_val_frame dispatch : forall ty this Q Q',
      Forall this' ty, Q this' ty -* Q' this' ty |-- delete_val dispatch ty this Q -* delete_val dispatch ty this Q'.
  Proof.
    intro ty; generalize dependent dispatch; induction ty; simpl; eauto;
      try solve [ intros; iIntros "Q [$ X]"; iRevert "X"; done ].
    { induction (rev _); simpl; intros.
      { iIntros "X"; iApply "X". }
      { iIntros "Q [$ V]". iRevert "V"; iApply IHty; iIntros (??); iApply IHl; eauto. } }
    { intros. case_match; eauto.
      case_match; eauto.
      { iIntros "X Y"; iNext; iRevert "Y"; iApply mspec_frame.
        iIntros (?) "[$ Q]"; iApply "X"; done. }
      { case_match.
        { iIntros "X"; iApply resolve_dtor_frame; iIntros (???) "B"; iNext; iRevert "B".
          iApply mspec_frame; iIntros (?) "[$ Q]"; iApply "X"; done. }
        { iIntros "X Y"; iNext; iRevert "Y"; iApply mspec_frame.
          iIntros (?) "[$ Q]"; iApply "X"; done. } } }
  Qed.

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
    | FreeTemps.delete ty addr => delete_val false ty addr (fun _ _ => Q)
    end.
  (* END interp *)

  Lemma interp_frame free : forall Q1 Q2,
      Q1 -* Q2 |-- interp free Q1 -* interp free Q2.
  Proof.
    induction free; simpl; intros; eauto.
    { iIntros "X"; iApply delete_val_frame; iIntros (??); done. }
    { iIntros "a"; iApply IHfree1; iApply IHfree2; done. }
    { iIntros "a b"; iDestruct "b" as (??) "(x & y & z)"; iExists _; iExists _; iFrame.
      iIntros "f g"; iApply "a"; iRevert "g"; by iApply "z". }
  Qed.

End destroy.
