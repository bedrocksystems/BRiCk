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
Require Import bedrock.lang.cpp.heap_notations.

Section with_resolve.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).
  Variables (ρ : region).
  Implicit Types (p : ptr).

  Definition arg_types (ty : type) : option (list type * function_arity) :=
    match ty with
    | @Tfunction _ ar _ args => Some (args, ar)
    | _ => None
    end.

  (**
     [wp_args' ts es Q] evaluates the arguments [es] to a function taking types [ts]
     and invokes [Q] with the values and the temporary destruction expression.

     > When a function is called, each parameter ([dcl.fct]) is initialized
     > ([dcl.init], [class.copy.ctor]) with its corresponding argument.

     This is encapsulated because the order of evaluation of function arguments is not
     specified in C++.
     NOTE this definition is *not* sound in the presence of exceptions.
  *)
  Fixpoint zipTypes (ts : list type) (ar : function_arity) (es : list Expr) : option (list (M ptr) * option (nat * list type)) :=
    let wp_arg_init ty init K := Forall p, wp_initialize tu ρ ty p init (fun frees => K p (FreeTemps.delete ty p >*> frees)%free) in
    match ts with
    | [] =>
        if ar is Ar_Variadic then
          let rest := map (fun e => (type_of e, wp_arg_init (type_of e) e)) es in
          Some (map snd rest, Some (0, map fst rest))
        else None
    | t :: ts =>
        match es with
        | [] => None
        | e :: es =>
            let update (x : list (M ptr) * option (nat * list type)) :=
              (wp_arg_init t e :: x.1, (fun x => (1 + x.1, x.2)) <$> x.2)
            in
            update <$> zipTypes ts ar es
        end
    end.

  Lemma zipTypes_ok : forall ts ar es ms r,
      zipTypes ts ar es = Some (ms, r) ->
      length ms = length es /\
      match r with
      | None => ar = Ar_Definite
      | Some (n, va_ts) => ar = Ar_Variadic /\ length ms = n + length va_ts /\ n = length ts
      end /\ |-- [∗list] m ∈ ms, Mframe m m.
  Proof.
    induction ts; simpl; intros.
    { destruct ar; try congruence.
      inversion H; clear H; subst.
      rewrite !map_map !map_length.
      split; eauto.
      split.
      { split; eauto. }
      { induction es =>/=; eauto.
        rewrite -IHes. rewrite right_id.
        iIntros (??) "X Y". iIntros (p).
        iSpecialize ("Y" $! p); iRevert "Y".
        iApply wp_initialize_frame.
        iIntros (?); iApply "X". } }
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
        { iIntros (??) "X Y". iIntros (f).
          iSpecialize ("Y" $! f); iRevert "Y".
          iApply wp_initialize_frame.
          iIntros (?); iApply "X". }
        destruct H0. eauto. } }
  Qed.

  Definition wp_args (ts_ar : list type * function_arity) (es : list Expr) (Q : list ptr -> FreeTemps -> mpred)
    : mpred :=
    match zipTypes ts_ar.1 ts_ar.2 es with
    | Some (args, va_info) =>
        nd_seqs args (fun ps fs =>
                        match va_info with
                        | Some (non_va, types) =>
                            let real := firstn non_va ps in
                            let vargs := skipn non_va ps in
                            let va_info := zip types vargs in
                            Forall p, p |-> varargsR va_info -*
                                      Q (real ++ [p]) (FreeTemps.delete_va va_info p >*> fs)%free
                        | None => Q ps fs
                        end)
    | _ => False
    end.

  Lemma wp_args_frame_strong : forall ts_ar es Q Q',
      (Forall vs free, [| if ts_ar.2 is Ar_Variadic then
                            length vs = length ts_ar.1 + 1
                          else length vs = length es |] -* Q vs free -* Q' vs free) |-- wp_args ts_ar es Q -* wp_args ts_ar es Q'.
  Proof.
    intros.
    iIntros "X".
    rewrite /wp_args. destruct ts_ar; simpl.
    generalize (zipTypes_ok l f es).
    destruct (zipTypes l f es); eauto.
    destruct p; eauto.
    intros X. destruct (X _ _ eq_refl); clear X.
    forward_reason.
    iApply (nd_seqs_frame_strong with "[X] []"); eauto.
    iIntros (??).
    destruct o.
    { destruct p.
      iIntros "% Y" (p) "Z"; iSpecialize ("Y" $! p with "Z"); iRevert "Y".
      iApply "X". destruct H; subst.
      iPureIntro.
      rewrite app_length/=.
      rewrite firstn_length_le; try lia.
      forward_reason; subst. eauto. }
    { destruct H. subst.
      iIntros "%"; iApply "X".
      iPureIntro. eauto. }
  Qed.

  Lemma wp_args_frame : forall ts_ar es Q Q',
      (Forall vs free, Q vs free -* Q' vs free) |-- wp_args ts_ar es Q -* wp_args ts_ar es Q'.
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
