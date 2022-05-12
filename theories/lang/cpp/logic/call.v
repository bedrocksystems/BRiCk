(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.proofmode.proofmode.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp initializers.
Require Import bedrock.lang.cpp.heap_notations.

Section with_resolve.
  Context `{Σ : cpp_logic} {σ : genv}.
  Variables (ρ : region).
  Implicit Types (p : ptr).

  #[local] Notation wp_call_initialize := (wp_call_initialize ρ).

  Definition arg_types (ty : type) : option (list type * function_arity) :=
    match ty with
    | @Tfunction _ ar _ args => Some (args, ar)
    | _ => None
    end.

  Fixpoint wp_varargs' (es : list Expr) (Q : list vararg -> list FreeTemps -> mpred)
  : mpred :=
    match es with
    | nil => Q nil nil
    | e :: es =>
      let t := type_of e in
      Exists Qarg,
        wp_call_initialize t e Qarg **
        wp_varargs' es
          (fun varargs frees' =>
             Forall v free frees,
               if to_vararg t v is Some vararg then
                 Qarg v free frees -* Q (vararg :: varargs) (free >*> frees :: frees')
               else
                 False)
    end%I%free.

  (**
     [wp_args' ts es Q] evaluates the arguments [es] to a function taking types [ts]
     and invokes [Q] with the values and the temporary destruction expression.

     > When a function is called, each parameter ([dcl.fct]) is initialized
     > ([dcl.init], [class.copy.ctor]) with its corresponding argument.

     This is encapsulated because the order of evaluation of function arguments is not
     specified in C++.
     NOTE this definition is *not* sound in the presence of exceptions.
  *)
  (** TODO [Q] could be [list ptr -> FreeTemps -> mpred] *)
  Fixpoint wp_args' (ts : list type) (ar : function_arity) (es : list Expr) (Q : list ptr -> list FreeTemps -> mpred)
  : mpred :=
    match ts with
    | [] =>
      if ar is Ar_Variadic then
        wp_varargs' es
          (fun varargs frees =>
             Forall p,
               p |-> variadicR varargs -*
               Q [p] (FreeTemps.delete_va varargs p :: frees))
      else
        [| es = [] |]
    | t :: ts =>
      match es with
      | [] => False
      | e :: es =>
        Exists Qarg,
          wp_call_initialize t e Qarg **
          wp_args' ts ar es
            (fun vs frees' =>
               Forall v free frees,
                 Qarg v free frees -*
                 Q (v :: vs) (free >*> frees :: frees'))
      end
    end%I%free.

  Lemma wp_args'_frame_strong : forall ts ar es Q Q',
      Forall vs free, [| length vs = length es |] -* Q vs free -* Q' vs free
      |-- wp_args' ts ar es Q -* wp_args' ts ar es Q'.
  Proof.
    elim; destruct es => /=; try solve [ by intros; iIntros "? []" ].
    (* { by iIntros (? ?) "H"; iApply "H". } *)
    (* { intros. iIntros "X Y". *)
    (*   iDestruct "Y" as (Qa) "[Y Ys]". *)
    (*   iExists Qa. iFrame. *)
    (*   iRevert "Ys". iApply H. *)
    (*   iIntros (??) "% Y"; iIntros (???) "?". *)
    (*   iApply "X"; simpl; eauto. *)
    (*   by iApply "Y".} *)
  Admitted.

  Definition wp_args ts ar es Q :=
    wp_args' ts ar es (fun vs frees => Q vs (FreeTemps.pars frees)).

  Lemma wp_args_frame_strong : forall ts ar es Q Q',
      (Forall vs free, [| length vs = length es |] -* Q vs free -* Q' vs free) |-- wp_args ts ar es Q -* wp_args ts ar es Q'.
  Proof.
    intros.
    iIntros "X". iApply wp_args'_frame_strong.
    iIntros (? ?) "%". by iApply "X".
  Qed.

  Lemma wp_args_frame : forall ts ar es Q Q',
      (Forall vs free, Q vs free -* Q' vs free) |-- wp_args ts ar es Q -* wp_args ts ar es Q'.
  Proof.
    intros; iIntros "X".
    iApply wp_args_frame_strong.
      by iIntros (vs free) "% H"; iApply "X".
  Qed.

  (*
     The following definitions describe the "return"-convention. Specifically,
     they describe how the returned pointer is recieved into the value category that
     it is called with.
     We consolidate these definitions here because they are shared between all
     function calls.
   *)
  Definition xval_receive (ty : type) (res : ptr) (Q : ptr -> mpred) : mpred :=
    Exists p, res |-> primR (Tref ty) 1 (Vref p) ** Q p.

  Lemma xval_receive_frame ty res Q Q' :
      Forall v, Q v -* Q' v |-- xval_receive ty res Q -* xval_receive ty res Q'.
  Proof.
    rewrite /xval_receive. iIntros "X Y"; iDestruct "Y" as (x) "[? ?]"; iExists x; iFrame; by iApply "X".
  Qed.

  Definition lval_receive (ty : type) (res : ptr) (Q : ptr -> mpred) : mpred :=
    Exists p, res |-> primR (Tref ty) 1 (Vref p) ** Q p.

  Lemma lval_receive_frame ty res Q Q' :
      Forall v, Q v -* Q' v |-- lval_receive ty res Q -* lval_receive ty res Q'.
  Proof.
    rewrite /lval_receive. iIntros "X Y"; iDestruct "Y" as (x) "[? ?]"; iExists x; iFrame; by iApply "X".
  Qed.

  Definition operand_receive (ty : type) (res : ptr) (Q : val -> mpred) : mpred :=
    Exists v, res |-> primR ty 1 v ** Q v.

  Lemma operand_receive_frame ty res Q Q' :
      Forall v, Q v -* Q' v |-- operand_receive ty res Q -* operand_receive ty res Q'.
  Proof.
    rewrite /operand_receive. iIntros "X Y"; iDestruct "Y" as (x) "[? ?]"; iExists x; iFrame; by iApply "X".
  Qed.

  Definition init_receive (ty : type) (addr : ptr) (res : ptr) (Q : FreeTemp -> mpred) : mpred :=
    ([| addr = res |] -* Q (FreeTemps.delete ty addr)).

  Lemma init_receive_frame ty addr res Q Q' :
      Forall v, Q v -* Q' v |-- init_receive ty addr res Q -* init_receive ty addr res Q'.
  Proof.
    rewrite /init_receive. iIntros "X Y Z"; iApply "X"; iApply "Y"; done.
  Qed.

  #[global] Arguments xval_receive _ _ _ /.
  #[global] Arguments lval_receive _ _ _ /.
  #[global] Arguments operand_receive _ _ _ /.
  #[global] Arguments init_receive _ _ _ _ /.

End with_resolve.
