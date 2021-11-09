(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp destroy initializers.
Require Import bedrock.lang.cpp.heap_notations.

Section with_resolve.
  Context `{Σ : cpp_logic} {σ : genv}.
  Variables (M : coPset) (ρ : region).

  Local Notation wp_lval := (wp_lval M ρ).
  Local Notation wp_prval := (wp_prval M ρ).
  Local Notation wp_xval := (wp_xval M ρ).
  Local Notation wp_init := (wp_init M ρ).

  (** [valcat_of_type t] is the value category embedded in the type [t].
      This is used when calling a function that takes [t] as an argument.
   *)
  Fixpoint valcat_of_type (t : type) : ValCat :=
    match t with
    | Tref _ => Lvalue
    | Trv_ref _ => Xvalue
    | Tqualified _ t => valcat_of_type t
    | _ => Prvalue
    end.

  Definition arg_types (ty : type) : option (list type) :=
    match ty with
    | @Tfunction _ _ args => Some args
    | _ => None
    end.

  (**
     [wp_args' ts es Q] evaluates the arguments [es] to a function taking types [ts]
     and invokes [Q] with the values and the temporary destruction expression.

     This is encapsulated because the order of evaluation of function arguments is not
     specified in C++.
     NOTE this definition is *not* sound in the presence of exceptions.

     NOTE that this deviates from the standard because it uses a different parameter
     passing convention.
  *)
  (** TODO [Q] could be [list ptr -> FreeTemps -> mpred] *)
  Fixpoint wp_args' (ts : list type) (es : list Expr) (Q : list val -> list FreeTemps -> mpred)
  : mpred :=
    match ts , es with
    | nil , nil => Q nil nil
    | t :: ts , e :: es =>
      match valcat_of_type t with
      | Prvalue =>
        if is_aggregate t then
          Forall a : ptr,
          Exists Qarg,
          wp_init t a e Qarg **
          wp_args' ts es (fun vs frees =>
                          Forall free,
                          Qarg free -* Q (Vptr a :: vs) (FreeTemps.delete t a >*> free :: frees)%free)
        else
          Exists Qarg,
          wp_prval e Qarg **
          wp_args' ts es (fun vs frees => Forall v free,
                                       Qarg v free -* Q (v :: vs) (free :: frees))
      | Lvalue =>
        Exists Qarg,
        wp_lval e Qarg **
        wp_args' ts es (fun vs frees => Forall p free,
           Qarg p free -* Q (Vptr p :: vs) (free :: frees))
      | Xvalue =>
        Exists Qarg,
        wp_xval e Qarg **
        wp_args' ts es (fun vs frees => Forall p free,
           Qarg p free -* Q (Vptr p :: vs) (free :: frees))
      end
     (* the (more) correct definition would use initialization semantics for each expression.
        > When a function is called, each parameter ([dcl.fct]) is initialized ([dcl.init], [class.copy.ctor])
        > with its corresponding argument.
      Forall a : ptr,
      Exists Qarg,
        wp_initialize M ti ρ t a e Qarg **
        wp_args ts es (fun vs frees =>
                         Forall free,
                         Qarg free -* Q (Vptr a :: vs) (FreeTemps.delete t a >*> free :: frees))
      *)
    | _ , _ => False (* mismatched arguments and parameters. *)
    end%I%free.

  Lemma wp_args'_frame_strong : forall ts es Q Q',
      Forall vs free, [| length vs = length es |] -* Q vs free -* Q' vs free
      |-- wp_args' ts es Q -* wp_args' ts es Q'.
  Proof.
    elim; destruct es => /=; try solve [ by intros; iIntros "? []" ].
    { by iIntros (? ?) "H"; iApply "H". }
    { destruct (valcat_of_type a) => /=; intros.
      { iIntros "X Y".
        iDestruct "Y" as (Qa) "[Y Ys]".
        iExists Qa. iFrame.
        iRevert "Ys". iApply H.
        iIntros (??) "% H"; iIntros (??) "H'".
        iDestruct ("H" with "H'") as "H".
        iRevert "H". iApply "X". iPureIntro. simpl; eauto. }
      { case_match.
        { iIntros "X Y" (?).
          iDestruct ("Y" $! a0) as (?) "Y".
          iExists _. iDestruct "Y" as "[$ A]".
          iRevert "A"; iApply H.
          iIntros (??) "% Y"; iIntros (?) "Z".
          iApply "X"; first by simpl; eauto.
            by iApply "Y". }
        { iIntros "X Y".
          iDestruct "Y" as (?) "Y".
          iExists _; iDestruct "Y" as "[$ Y]".
          iRevert "Y"; iApply H.
          iIntros (??) "% Y"; iIntros (??) "Z".
          iApply "X"; first by simpl; eauto.
          by iApply "Y". } }
      { iIntros "X Y".
        iDestruct "Y" as (?) "[Y Ys]".
        iExists _. iFrame.
        iRevert "Ys". iApply H.
        iIntros (??) "% H"; iIntros (??) "H'".
        iDestruct ("H" with "H'") as "H".
        iRevert "H". iApply "X". iPureIntro. simpl; eauto. } }
  Qed.

  Definition wp_args ts es Q :=
    wp_args' ts es (fun vs frees => Q vs (FreeTemps.pars frees)).

  Lemma wp_args_frame_strong : forall ts es Q Q',
      (Forall vs free, [| length vs = length es |] -* Q vs free -* Q' vs free) |-- wp_args ts es Q -* wp_args ts es Q'.
  Proof.
    intros.
    iIntros "X". iApply wp_args'_frame_strong.
    iIntros (? ?) "%". by iApply "X".
  Qed.

  Lemma wp_args_frame : forall ts es Q Q',
      (Forall vs free, Q vs free -* Q' vs free) |-- wp_args ts es Q -* wp_args ts es Q'.
  Proof.
    intros; iIntros "X".
    iApply wp_args_frame_strong.
      by iIntros (vs free) "% H"; iApply "X".
  Qed.

End with_resolve.
