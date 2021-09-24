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

  (* [destruct_val dispatch t this Q] invokes the destructor on [this]
     where the type of [this] is [t].

     The [dispatch] parameter determines whether the call is a *potentially*
     virtual call. If [dispatch] is true *and the destructor of the class is
     virtual*, then the call is a virtual call.

     note: it does *not* free the underlying memory.

     NOTE in our semantics (unlike the standard) all objects are destroyed
     via destructors. This is justified because the only objects
     that do not have destructors according to the standard have
     no-op destructors. Thus, we can model the "not having a destructor"
     as an optimization. This choice makes the semantics more uniform.
   *)
  Fixpoint destruct_val (dispatch : bool) (t : type) (this : ptr) (Q : mpred)
           {struct t}
  : mpred :=
    match t with
    | Tqualified _ t => destruct_val dispatch t this Q
    | Tnamed cls =>
      match σ.(genv_tu) !! cls with
      | Some (Gstruct s) =>
        (** when [dispatch:=true], we should use virtual dispatch
            to invoke the destructor.
         *)
        if dispatch && has_virtual_dtor s then
          resolve_dtor cls this (fun fimpl impl_class this' =>
            let ty := Tfunction Tvoid nil in
            |> mspec σ.(genv_tu).(globals) (Tnamed impl_class) ty (Vptr fimpl) (Vptr this' :: nil) (fun _ => Q))
        else
          (* NOTE the setup with explicit destructors (even when those destructors are trivial)
                  abstracts away some of the complexities of the underlying C++ semantics that
                  the semantics itself seems less than clear about. [CITATION NEEDED]

             TODO let's find some justification in the standard.
           *)
          (* In the current implementation, we generate destructor even when they are implicit
             to make the framework a bit more uniform (all objects have destructors) and allow
             for direct desructor calls, e.g. [c.~C()], which are encoded as
             [Emember_call ... "~C" ..] *)
          (let dtor := s.(s_dtor) in
           let ty := Tfunction Tvoid nil in (** NOTE this implicitly requires all destructors to have C calling convention *)
           |> mspec σ.(genv_tu).(globals) (Tnamed cls) ty (Vptr $ _global s.(s_dtor)) (Vptr this :: nil) (fun _ => Q))

      | Some (Gunion u) =>
          (* unions can not have [virtual] destructors, so we directly invoke
             the destructor.
           *)
          (let dtor := u.(u_dtor) in
           let ty := Tfunction Tvoid nil in
           |> mspec σ.(genv_tu).(globals) (Tnamed cls) ty (Vptr $ _global u.(u_dtor)) (Vptr this :: nil) (fun _ => Q))
      | _ => False
      end
    | Tarray t sz =>
      (* NOTE when destroying an array, elements of the array are destroyed with non-virtual dispatch. *)
      fold_right (fun i Q => valid_ptr (this .[ t ! Z.of_nat i ]) **
           destruct_val false t (this .[ t ! Z.of_nat i ]) Q) Q (List.rev (seq 0 (N.to_nat sz)))
    | _ =>
      (* |={↑pred_ns}=> *) this |-> anyR (erase_qualifiers t) 1 ** (this |-> tblockR (erase_qualifiers t) 1 -* Q)
      (* emp *)
    end%I.

  Lemma destruct_val_frame dispatch : forall ty this Q Q',
      Q -* Q' |-- destruct_val dispatch ty this Q -* destruct_val dispatch ty this Q'.
  Proof.
    intro ty; generalize dependent dispatch; induction ty; simpl; eauto;
      try solve [
            intros; iIntros "Q [$ X]"; iIntros "A"; iApply "Q"; iApply "X"; eauto ].
    { induction (rev _); simpl; eauto.
      intros.
      iIntros "Q [$ V]"; iRevert "V"; iApply IHty; iApply IHl; eauto. }
    { intros. case_match; eauto.
      case_match; eauto.
      { iIntros "X Y"; iNext; iRevert "Y"; iApply mspec_frame; iIntros (?); done. }
      { case_match.
        { by iIntros "X"; iApply resolve_dtor_frame; iIntros (???) "B"; iNext; iRevert "B"; iApply mspec_frame; iIntros (?). }
        { iIntros "X Y"; iNext; iRevert "Y"; iApply mspec_frame; iIntros (?); done. } } }
  Qed.
End destroy.

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.

  (*
  (** [wp_alloc ty Q] allocates storage for [ty] and passes the address
      to [Q]. Generally, [Q] will initialize this memory.
   *)
  Definition wp_alloc (ty : type) (Q : ptr -> mpred) : mpred :=
    Forall addr : ptr, addr |-> tblockR (erase_qualifiers ty) 1 -* Q addr.

  (** [wp_free ty addr Q] frees the memory of a [ty] at address [addr].
   *)
  Definition wp_free (ty : type) (addr : ptr) (Q : mpred) : mpred :=
    destruct_val false ty addr (addr |-> tblockR (σ:=σ) ty 1 ** Q).
  *)

  (** [delete_val dispatch ty this Q] destructs [this] (of type [t]) and then
      frees the underlying memory
   *)
  Definition delete_val (ty : type) (this : ptr) (Q : epred) : mpred :=
    destruct_val false ty this (this |-> tblockR (erase_qualifiers ty) 1 ** Q).

  Lemma delete_val_frame ty this Q1 Q2 :
      Q1 -* Q2 |-- delete_val ty this Q1 -* delete_val ty this Q2.
  Proof.
    iIntros "a"; iApply destruct_val_frame. iIntros "[$ X]"; by iApply "a".
  Qed.

  (** [interp free Q] "runs" [free] and then acts like [Q].

      TODO it might make sense for this to be like a [wp] where this
      will have fancy update modalities.
   *)
  Fixpoint interp (free : FreeTemps) (Q : epred) : mpred :=
    match free with
    | FreeTemps.id => Q
    | FreeTemps.seq f g => interp f $ interp g Q
    | FreeTemps.par f g => Exists Qf Qg, interp f Qf ** interp g Qg ** (Qf -* Qg -* Q)
    | FreeTemps.delete ty addr => delete_val ty addr Q
    end.

  Lemma interp_frame free : forall Q1 Q2,
      Q1 -* Q2 |-- interp free Q1 -* interp free Q2.
  Proof.
    induction free; simpl; intros; eauto.
    { iApply delete_val_frame. }
    { iIntros "a"; iApply IHfree1; iApply IHfree2; done. }
    { iIntros "a b"; iDestruct "b" as (??) "(x & y & z)"; iExists _; iExists _; iFrame.
      iIntros "f g"; iApply "a"; iRevert "g"; by iApply "z". }
  Qed.

End destroy.
