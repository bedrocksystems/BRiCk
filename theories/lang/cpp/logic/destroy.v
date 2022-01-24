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
     pred wp path_pred heap_pred.
Require Import bedrock.lang.cpp.logic.dispatch.

Require Import bedrock.lang.cpp.heap_notations.

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.

  (* [wp_destructor ty dtor this Q] is the weakest pre-condition of invoking the destructor
     [dtor] (which is the destructor for [ty] on [this].
   *)
  #[local] Definition wp_destructor (ty : type) (dtor : ptr) (this : ptr) (Q : epred) : mpred :=
    (* NOTE using [Tfunction Tvoid nil] implicitly requires all destructors
       to have C calling convention. *)
    mspec σ.(genv_tu).(globals) ty (Tfunction Tvoid nil)
                                (Vptr dtor) (Vptr this :: nil)
                                (fun _ => this |-> tblockR ty 1 ** Q).

(** [destroy_val ty this Q] destructs [this] (which has [ty] as its most specific type).
      If [this] is an aggregate, we invoke [ty]'s destructor (leaving any virtual
      lookup to the caller). The memory is returned to the C++ abstract machine and the 
      continuation [Q] is invoked.

      NOTE in our semantics (unlike the standard) all aggregates are destroyed
      via destructors. This is justified because the only objects that do not
      have destructors according to the standard have no-op destructors. Thus,
      we can model the "not having a destructor" as an optimization. This
      choice makes the semantics more uniform. *)
  Fixpoint destroy_val (ty : type) (this : ptr) (Q : epred) {struct ty} : mpred :=
    match ty with
    | Tqualified _ ty => destroy_val ty this Q
    | Tnamed cls      =>
      match σ.(genv_tu) !! cls with
      | Some (Gstruct s) =>
         (* NOTE the setup with explicit destructors (even when those destructors are trivial)
                  abstracts away some of the complexities of the underlying C++ semantics that
                  the semantics itself seems less than clear about. [CITATION NEEDED]

             TODO let's find some justification in the standard. *)
          (* In the current implementation, we generate destructor even when they are implicit
             to make the framework a bit more uniform (all types have destructors) and allow
             for direct destructor calls, e.g. [c.~C()], which are encoded as
             [Emember_call ... "~C" ..] *)
        |> wp_destructor ty (_global s.(s_dtor)) this Q
      | Some (Gunion u)  =>
        (* Unions cannot have [virtual] destructors: we directly invoke the destructor. *)
        |> wp_destructor ty (_global u.(u_dtor)) this Q
      | _ => False
      end
    | Tarray ety sz   =>
      (* NOTE array elements are destroyed with non-virtual dispatch. *)
      (* TODO replace [fold_right ... rev] by [fold_left]? *)
      fold_right (fun i Q =>
        let p := this .[ erase_qualifiers ety ! Z.of_nat i ] in
        valid_ptr p ** destroy_val ety p Q
      ) Q (rev (seq 0 (N.to_nat sz)))
    | Tref r_ty
    | Trv_ref r_ty    =>
      (* NOTE rvalue references [Trv_ref] are represented as references [Tref]. *)
      this |-> anyR (Tref $ erase_qualifiers r_ty) 1 ** Q
    | ty              =>
      this |-> anyR (erase_qualifiers ty) 1 ** Q
    end%I.

  Lemma destroy_val_frame : forall ty this (Q Q' : epred),
      Q -* Q' |-- destroy_val ty this Q -* destroy_val ty this Q'.
  Proof.
    intro ty; generalize dependent dispatch; induction ty; simpl; eauto;
      try solve [ intros; iIntros "Q [$ X]"; iRevert "X"; done ].
    { induction (rev _); simpl; intros.
      { iIntros "X"; iApply "X". }
      { iIntros "Q [$ V]". iRevert "V"; iApply IHty; eauto. iApply IHl; eauto. } }
    { intros. case_match; eauto.
      case_match; eauto.
      { iIntros "X Y"; iNext; iRevert "Y"; iApply mspec_frame.
        iIntros (?) "[$ Q]"; iApply "X"; done. }
      { iIntros "X Y"; iNext; iRevert "Y"; iApply mspec_frame.
        iIntros (?) "[$ Q]"; iApply "X"; done. } }
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
    | FreeTemps.delete ty addr => destroy_val ty addr Q
    end.
  (* END interp *)

  Lemma interp_frame free : forall Q1 Q2,
      Q1 -* Q2 |-- interp free Q1 -* interp free Q2.
  Proof.
    induction free; simpl; intros; eauto.
    { iIntros "X"; iApply destroy_val_frame; done. }
    { iIntros "a"; iApply IHfree1; iApply IHfree2; done. }
    { iIntros "a b"; iDestruct "b" as (??) "(x & y & z)"; iExists _; iExists _; iFrame.
      iIntros "f g"; iApply "a"; iRevert "g"; by iApply "z". }
  Qed.

End destroy.
