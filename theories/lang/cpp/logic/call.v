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
Require Import bedrock.prelude.letstar.

Fixpoint split_at {T : Type} (n : nat) (ls : list T) : list T * list T :=
  match n , ls with
  | 0 , _ => (nil, ls)
  | S n , [] => (nil, nil)
  | S n , l :: ls => let '(a,b) := split_at n ls in (l :: a, b)
  end.

Lemma split_at_firstn_skipn {T} (ls : list T) : forall (n : nat),
    split_at n ls = (firstn n ls, skipn n ls).
Proof.
  induction ls; destruct n; simpl; eauto.
  rewrite IHls; done.
Qed.

Definition check_arity (ts : list type) (ar : function_arity) (es : list Expr) : bool :=
  match Nat.compare (length ts) (length es) with
  | Eq => true
  | Lt => bool_decide (ar = Ar_Variadic)
  | Gt => false
  end.

Definition setup_args (ts : list type) (ar : function_arity) (es : list Expr)
  : (list (type * Expr) * option nat) :=
  let normal_params := length ts in
  let (regular, variadic) := split_at normal_params es in
  (combine ts regular ++ map (fun e => (type_of e, e)) variadic,
    match ar with
    | Ar_Definite => None
    | Ar_Variadic => Some normal_params
    end).

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
    (let '(ts,ar) := ts_ar in
    if check_arity ts ar es then
      let '(tes, va_info) := setup_args ts ar es in
      letI* ps, fs := eval eo (pre ++ map (fun '(t, e) => wp_arg t e) tes) in
        let (pre, ps) := split_at (length pre) ps in
        match va_info with
        | Some non_va =>
            let (real, vargs) := split_at non_va ps in
            let types := map fst $ skipn non_va tes in
            let va_info := zip types vargs in
            Forall p, p |-> varargsR va_info -*
                        Q pre (real ++ [p]) (FreeTemps.delete_va va_info p >*> fs)%free
        | None =>
            Q pre ps fs
        end
    else
      False)%I.

  Lemma big_opL_map {PROP : bi} (T U : Type) (f : T -> U) (P : _ -> PROP) (ls : list T) :
    ([∗list] x ∈ map f ls , P x)%I -|- [∗list] x ∈ ls , P (f x).
  Proof.
    induction ls; simpl; eauto.
    by rewrite IHls.
  Qed.

  Lemma big_opL_all  {PROP : bi} (T : Type) (P : T -> PROP) (ls : list T) :
    bi_intuitionistically (Forall x, P x) |-- [∗list] x ∈ ls , P x.
  Proof.
    induction ls; simpl; eauto.
    iIntros "#H". iSplitL.
    iApply "H". iApply IHls. iApply "H".
  Qed.

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
    rewrite /check_arity/setup_args.
    case Nat.compare_spec; intros; try iIntros "[]".
    { rewrite split_at_firstn_skipn.
      iApply (eval_frame_strong with "[PRS]").
      { iSplitL; eauto.
        rewrite big_opL_map.
        iApply big_opL_all.
        iModIntro.
        iIntros (te); destruct te; iApply wp_arg_frame. }
      { iIntros (??) "%".
        rewrite split_at_firstn_skipn.
        revert H0.
        rewrite app_length map_length app_length map_length combine_length firstn_length skipn_length.
        intros. destruct f.
        { iApply "X"; iPureIntro.
          rewrite firstn_length. lia.
          rewrite skipn_length. lia. }
        { rewrite split_at_firstn_skipn.
          iIntros "H" (p) "V".
          iSpecialize ("H" with "V").
          iRevert "H". iApply "X"; iPureIntro.
          - rewrite firstn_length. lia.
          - rewrite app_length firstn_length skipn_length /=. lia. } } }
    { case_bool_decide; try iIntros "[]".
      rewrite split_at_firstn_skipn.
      iApply (eval_frame_strong with "[PRS]").
      { iSplitL; eauto.
        rewrite big_opL_map.
        iApply big_opL_all.
        iModIntro.
        iIntros (te); destruct te; iApply wp_arg_frame. }
      { subst.
        iIntros (?? HH).
        rewrite !split_at_firstn_skipn.
        iIntros "H" (?) "A".
        iSpecialize ("H" with "A").
        revert HH.
        rewrite app_length map_length app_length map_length combine_length firstn_length skipn_length.
        intro.
        iRevert "H"; iApply "X"; iPureIntro.
        - rewrite firstn_length. lia.
        - rewrite app_length firstn_length skipn_length /=. lia. } }
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
