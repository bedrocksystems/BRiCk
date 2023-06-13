(*
 * Copyright (c) 2020-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import ExtLib.Tactics.Forward.
Require Import iris.proofmode.proofmode.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp initializers.

Section zipTypes.
  Context `{Σ : cpp_logic}.
  Context {T : Type}.
  Variable wp_expr : type -> Expr -> wp.WPE.M T.

  (** [zipTypes ts ar es = Some (ms, var_arg)]

      Sets up the evaluation for a function that accepts [ts] arguments and is
      variadic arguments as described by [ar].
   *)
  #[local] Fixpoint zipTypes (ts : list type) (ar : function_arity) (es : list Expr)
    : option (list (wp.WPE.M T) * option (nat * list type)) :=
    let wp_arg_init ty init K :=
      (* top-level qualifiers on arguments are ignored, they are taken from the definition,
         not the declaration. Dropping qualifiers here makes it possible to support code
         like the following:
         <<
         // f.hpp
         void f(int);
         void g() { f(1); } // calls using [void f(int)] rather than [void f(const int)]
         // f.cpp
         void f(const int) {}
         >>
       *)
      wp_expr (drop_qualifiers ty) init K
    in
    match ts with
    | [] =>
        if ar is Ar_Variadic then
          let rest := map (fun e => let ty := drop_qualifiers (type_of e) in
                                 (ty, wp_arg_init ty e)) es in
          Some (map snd rest, Some (0, map fst rest))
        else match es with
             | [] => Some ([], None)
             | _ :: _ => None
             end
    | t :: ts =>
        match es with
        | [] => None
        | e :: es =>
            let update (x : list (wp.WPE.M T) * option (nat * list type)) :=
              (wp_arg_init t e :: x.1, (fun x => (1 + x.1, x.2)) <$> x.2)
            in
            update <$> zipTypes ts ar es
        end
    end.

  Lemma zipTypes_definite_base_case :
    zipTypes [] Ar_Definite [] = Some ([], None).
  Proof. reflexivity. Qed.

  Lemma zipTypes_definite_nonnull :
    forall (ts : list type) (es : list Expr)
      (Hlengths : lengthN ts = lengthN es),
      zipTypes ts Ar_Definite es <> None.
  Proof.
    intros ts; induction ts as [| t ts' IHts'];
      intros [| e es'] Hlengths; cbn; try done.
    rewrite !lengthN_cons in Hlengths.
    intro CONTRA; apply (IHts' es'); first by lia.
    by apply fmap_None in CONTRA.
  Qed.

  Hypothesis wp_expr_frame : forall ty e , |-- wp.WPE.Mframe (wp_expr ty e) (wp_expr ty e).

  #[local] Lemma zipTypes_ok : forall ts ar es ms r,
      zipTypes ts ar es = Some (ms, r) ->
      length ms = length es /\
      match r with
      | None => ar = Ar_Definite
      | Some (n, va_ts) => ar = Ar_Variadic /\ length ms = n + length va_ts /\ n = length ts
      end /\ |-- [∗list] m ∈ ms, wp.WPE.Mframe m m.
  Proof using wp_expr_frame.
    induction ts; simpl; intros.
    { destruct ar; first by destruct es; inversion H.
      inversion H; clear H; subst.
      rewrite !map_map !map_length.
      split; eauto.
      split.
      { split; eauto. }
      { induction es =>/=; eauto.
        rewrite -IHes. rewrite right_id.
        iIntros (??) "X Y". iApply (wp_expr_frame with "X Y"). } }
    { destruct es; try congruence.
      specialize (IHts ar es).
      destruct (zipTypes ts ar es); simpl in *; try congruence.
      inversion H; clear H; subst.
      destruct p; simpl in *.
      specialize (IHts _ _ eq_refl).
      destruct IHts; split; eauto.
      split.
      { destruct o; simpl in *.
        { destruct p; simpl. forward_reason. split; eauto. }
        { destruct H0; eauto. } }
      { iSplitL.
        { iIntros (??) "X Y". iApply (wp_expr_frame with "X Y"). }
        { destruct H0. iApply H1. } } }
  Qed.

End zipTypes.

Section with_resolve.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).
  Variables (ρ : region).
  Implicit Types (p : ptr).

  Definition arg_types (ty : type) : option (list type * function_arity) :=
    match ty with
    | @Tfunction _ ar _ args => Some (args, ar)
    | _ => None
    end.

  Definition wp_arg ty e K :=
    Forall p, wp_initialize tu ρ ty p e (fun free => K p (FreeTemps.delete ty p >*> free)%free).

  Lemma wp_arg_frame : forall ty e, |-- wp.WPE.Mframe (wp_arg ty e) (wp_arg ty e).
  Proof.
    rewrite /wp.WPE.Mframe; intros.
    iIntros (??) "X Y %p".
    iSpecialize ("Y" $! p).
    iRevert "Y".
    iApply wp_initialize_frame. done.
    iIntros (?); iApply "X".
  Qed.

  (**
     [wp_args eo pre ts_ar es] evaluates [pre ++ es] according to the evaluation order [eo].
     The expressions in [es] are evaluated using initialization semantics for the argument types
     described in [ts_ar] (including handling for variadic functions). The continuation [Q] is applied
     to the evaluated results of each argument, and the [FreeTemps] accounts for the correct destruction
     of all temporaries.

     Unlike [es], [pre] is expressed directly as a semantic computation in order to unify the
     different ways that it can be used, e.g. to evaluate the object in [o.f()] (which is evaluated
     as a gl-value) or to evaluate the function in [f()] (which is evaluated as a pointer-typed operand).
   *)
  Definition wp_args (eo : evaluation_order.t) (pre : list (wp.WPE.M ptr))
    (ts_ar : list type * function_arity) (es : list Expr) (Q : list ptr -> list ptr -> FreeTemps -> mpred)
    : mpred :=
    match zipTypes wp_arg ts_ar.1 ts_ar.2 es with
    | Some (args, va_info) =>
        letI* ps, fs := eval eo (pre ++ args) in
        let pre := firstn (length pre) ps in
        let ps := skipn (length pre) ps in
        match va_info with
        | Some (non_va, types) =>
            let real := firstn non_va ps in
            let vargs := skipn non_va ps in
            let va_info := zip types vargs in
            Forall p, p |-> varargsR va_info -*
                        Q pre (real ++ [p]) (FreeTemps.delete_va va_info p >*> fs)%free
        | None =>
            Q pre ps fs
        end
    | _ => False
    end.

  Lemma wp_args_frame_strong : forall eo pres ts_ar es Q Q',
      ([∗list] m ∈ pres, wp.WPE.Mframe m m)%I
      |-- (Forall ps vs free,
        [| length ps = length pres |] -*
        [| if ts_ar.2 is Ar_Variadic then
             length vs = length ts_ar.1 + 1
           else length vs = length es |] -*
        Q ps vs free -* Q' ps vs free) -*
      wp_args eo pres ts_ar es Q -* wp_args eo pres ts_ar es Q'.
  Proof.
    intros.
    iIntros "PRS X".
    rewrite /wp_args. destruct ts_ar; simpl.
    generalize (zipTypes_ok wp_arg wp_arg_frame l f es).
    destruct (zipTypes wp_arg l f es); eauto.
    destruct p; eauto.
    intros X. destruct (X _ _ eq_refl); clear X.
    forward_reason.
    iApply (eval_frame_strong with "[PRS] [X]"); eauto.
    { iFrame. iApply H1. }
    rewrite app_length.
    iIntros (???).
    destruct o.
    { destruct p.
      iIntros "Y" (p) "Z"; iSpecialize ("Y" $! p with "Z"); iRevert "Y".
      iApply "X".
      { rewrite firstn_length. iPureIntro.
        lia. }
      { destruct H0 as [?[??]].
        iPureIntro. subst.
        rewrite !firstn_length app_length !firstn_length !skipn_length /=; lia. } }
    { subst. iApply "X";
      iPureIntro; rewrite !firstn_length ?skipn_length /=; lia. }
  Qed.

  Lemma wp_args_frame : forall eo pres ts_ar es Q Q',
      ([∗list] m ∈ pres, wp.WPE.Mframe m m)%I
      |-- (Forall ps vs free, Q ps vs free -* Q' ps vs free) -*
          wp_args eo pres ts_ar es Q -* wp_args eo pres ts_ar es Q'.
  Proof.
    intros; iIntros "X Y".
    iApply (wp_args_frame_strong with "X").
    iIntros (?????); iApply "Y".
  Qed.

  (*
     The following definitions describe the "return"-convention. Specifically,
     they describe how the returned pointer is received into the value category that
     it is called with.
     We consolidate these definitions here because they are shared between all
     function calls.
   *)
  Definition xval_receive (ty : type) (res : ptr) (Q : ptr -> epred) : mpred :=
    Exists p, res |-> primR (Tref (erase_qualifiers ty)) (cQp.mut 1) (Vref p) ** Q p.

  Lemma xval_receive_frame ty res (Q Q' : ptr -> epred) :
      Forall v, Q v -* Q' v |-- xval_receive ty res Q -* xval_receive ty res Q'.
  Proof.
    rewrite /xval_receive. iIntros "X Y"; iDestruct "Y" as (x) "[? ?]"; iExists x; iFrame; by iApply "X".
  Qed.

  Definition lval_receive (ty : type) (res : ptr) (Q : ptr -> epred) : mpred :=
    Exists p, res |-> primR (Tref (erase_qualifiers ty)) (cQp.mut 1) (Vref p) ** Q p.

  Lemma lval_receive_frame ty res (Q Q' : ptr -> epred) :
      Forall v, Q v -* Q' v |-- lval_receive ty res Q -* lval_receive ty res Q'.
  Proof.
    rewrite /lval_receive. iIntros "X Y"; iDestruct "Y" as (x) "[? ?]"; iExists x; iFrame; by iApply "X".
  Qed.

  Definition operand_receive (ty : type) (res : ptr) (Q : val -> epred) : mpred :=
    Exists v,
    let c := qual_norm (fun cv _ => q_const cv) ty in
    res |-> primR (erase_qualifiers ty) (cQp.mk c 1) v **
    Q v.

  Lemma operand_receive_frame ty res (Q Q' : val -> epred) :
      Forall v, Q v -* Q' v |-- operand_receive ty res Q -* operand_receive ty res Q'.
  Proof.
    rewrite /operand_receive. iIntros "X Y"; iDestruct "Y" as (x) "[? ?]"; iExists x; iFrame; by iApply "X".
  Qed.

  Definition init_receive (addr res : ptr) (Q : epred) : mpred :=
    [| addr = res |] -* Q.

  Lemma init_receive_frame addr res (Q Q' : epred) :
      Q -* Q' |-- init_receive addr res Q -* init_receive addr res Q'.
  Proof.
    rewrite /init_receive. iIntros "X Y Z"; iApply "X"; iApply "Y"; done.
  Qed.

  #[global] Arguments xval_receive _ _ _ / : assert.
  #[global] Arguments lval_receive _ _ _ / : assert.
  #[global] Arguments operand_receive _ _ _ / : assert.
  #[global] Arguments init_receive _ _ _ / : assert.

End with_resolve.
