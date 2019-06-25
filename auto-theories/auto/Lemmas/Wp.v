(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.

From Cpp Require Import
     Ast Sem.
From Cpp.Auto Require Import
     Definitions Discharge.
From bedrock.auto.Lemmas Require Import
     Eval PLogic.

Local Ltac work :=
  discharge fail idtac fail fail eauto.

Lemma wp_rhs_local (ty : type) : forall ti resolve ρ x Q,
    Exists v, (tlocal ρ x (tprim (drop_qualifiers ty) v) ** ltrue) //\\ Q v empSP
    |-- wp_rhs (resolve:=resolve) ti ρ (Ecast Cl2r (Lvalue, Evar (Lname x) ty) ty) Q.
Proof.
  unfold tlocal. intros.
  work.
  rewrite bilexistsscL2.
  rewrite landexistsD1.
  work.
  rewrite <- wp_rhs_cast_l2r.
  rewrite <- wp_lhs_lvar.
  work.
  { eapply landL1.
    unfold tlocal_at.
    rewrite sepSPA.
    eapply scME. reflexivity. eapply ltrueR. }
  { unfold tlocal_at; simpl.
    eapply landL1.
    instantiate (1:=v).
    work. }
  { eapply landL2. reflexivity. }
Qed.

(* this is the common case for member access
 *)
Lemma wp_rhs_dot : forall resolve ti x0 obj f fty z Q,
    wp_lhs (resolve:=resolve) ti x0 obj (fun base free =>

       Exists val,
         (_at (_offsetL (_field f) (_eq base)) (tprim (drop_qualifiers fty) val) ** ltrue) //\\
       Q val free)
    |-- wp_rhs (resolve:=resolve) ti x0 (Ecast Cl2r (Lvalue, Emember obj f fty) z) Q.
Proof. Admitted.

Lemma wp_lhs_assign_member_ignore : forall resolve ti r f t obj e t' Q,
    wp_lhs (resolve:=resolve) ti r obj (fun base free =>
    wp_rhs (resolve:=resolve) ti r e (fun v' free' =>
        _at (_offsetL (_field f) (_eq base)) (uninit (drop_qualifiers t)) **
        (_at (_offsetL (_field f) (_eq base)) (tprim (drop_qualifiers t) v') -*
        Q (free ** free'))))
    |-- wp_lhs (resolve:=resolve) ti r (Eassign (Emember obj f t) e t') (fun _ free => Q free).
Proof. Admitted.


Lemma wp_lhs_assign_member : forall resolve ti r f t obj e t' Q,
    wp_lhs (resolve:=resolve) ti r obj (fun base free =>
    wp_rhs (resolve:=resolve) ti r e (fun v' free' =>
        Exists addr, (_offsetL (_field f) (_eq base) &~ addr ** ltrue) //\\
        _at (_eq addr) (tany (drop_qualifiers t)) **
        (_at (_eq addr) (tprim (drop_qualifiers t) v') -* Q addr (free ** free'))))
    |-- wp_lhs (resolve:=resolve) ti r (Eassign (Emember obj f t) e t') Q.
Proof. Admitted.


Theorem wp_call_glob : forall resolve vc ti ρ f ret ts es K PQ F F' ty ty' ty'',
   (vc = Lvalue \/ vc = Rvalue) ->
   F |-- (|> cglob (resolve:=resolve) f ti (SFunction ret ts PQ)) ** ltrue ->
   F
   |-- wps (wpAnys (resolve:=resolve) ti ρ) es (fun vs free => applyEach ts vs PQ (fun wpp _ =>
            WppD wpp (fun r => K r free))) empSP ** F' ->
   F
   |-- wp_rhs (resolve:=resolve) ti ρ
         (Ecall (Ecast Cfunction2pointer (vc, Evar (Gname f) ty) ty') es ty'')
         K ** F'.
Proof. Admitted.

Lemma wp_member_call_glob:
  forall (resolve : genv) ti ρ (gn : globname) this (ret : type)
    ty
    (ts : list type) es (K : val -> FreeTemps -> mpred)
    (PQ : val -> arrowFrom val ts WithPrePost) (F F' : mpred)
    cls q,
    F |-- (|> cglob (resolve:=resolve) gn ti (SMethod cls q ret ts PQ)) ** ltrue ->
    F
    |-- wp_lhs (resolve:=resolve) ti ρ this (fun this =>
          wps (wpAnys (resolve:=resolve) ti ρ) es (fun (vs : list val) free =>
            applyEach ts vs (PQ this) (fun wpp _ =>
              WppD wpp (fun r => K r free)))) ** F' ->
    F
    |-- wp_rhs (resolve:=resolve) ti ρ (Emember_call false gn this es ty) K ** F'.
Proof. Admitted.

Theorem wp_constructor_glob : forall resolve ti ρ cname cls ts es K PQ F F' ty,
   F |-- (|> cglob (resolve:=resolve) cname ti (SConstructor cls ts PQ)) ** ltrue ->
   F
   |-- wps (wpAnys (resolve:=resolve) ti ρ) es (fun vs free =>
             (* note(gmm): this is cancelling the `uninitialized_ty`
              * which is inserted into the pre-condition by `SConstructor` *)
             Forall a, applyEach ts vs (PQ a) (fun wpp _ =>
               WppD wpp (fun _ => K a free))) empSP ** F' ->
   F
   |-- wp_rhs (resolve:=resolve) ti ρ
         (Econstructor cname es ty)
         K ** F'.
Proof.
(*
      intros.
      rewrite H; clear H.
      rewrite <- wp_call.
      rewrite <- wp_rhs_cast_function2pointer.
      simplify_wp.
      unfold cglob.
      discharge ltac:(canceler fail eauto) eauto.
      rewrite wps_frame.
      rewrite sepSPC.
      rewrite wps_frame.
      eapply Proper_wps_entails; eauto.
      red. intros.
      rewrite sepSPC.
      etransitivity.
      eapply triple'_apply with (vs:=a).
      reflexivity.
      discharge auto.
      eapply spec_later_weaken.
*)
Admitted.

Theorem wp_decl_class
: forall resolve ti ρ x ty es cls cname (k : Kpreds -> mpred) ts PQ F F' Q dname PQ',
    F |-- (|> cglob (resolve:=resolve) cname ti (SConstructor cls ts PQ)) ** ltrue ->
    F |-- (|> cglob (resolve:=resolve) dname ti (SDestructor cls PQ')) ** ltrue ->
    F
    |-- wps (wpAnys (resolve:=resolve) ti ρ) es (fun vs free =>
             (* note(gmm): this is cancelling the `uninitialized_ty`
              * which is inserted into the pre-condition by `SConstructor` *)
             Forall a, applyEach ts vs (PQ a) (fun wpp _ =>
               WppD wpp
                    (fun _ => free ** (_local ρ x &~ a -* k (Kat_exit (fun Q' =>
                       WppD (PQ' a)
                            (fun _ =>
                               (* note(gmm): this is canceling the dead memory
                                * that is inserted by `SDestructor` *)
                               _local ρ x &~ a ** Q')) Q))))) empSP ** F' ->
    F
    |-- wp_decl (resolve:=resolve) ti ρ
                x (Tref cls) (Some (Econstructor cname es ty)) k Q ** F'.
Proof. Admitted.

Theorem wp_destroy
: forall resolve ti this cls F F' Q PQ' dt,
    F |-- (|> cglob (resolve:=resolve) (dtor_name dt cls) ti (SDestructor cls PQ')) ** ltrue ->
    F
    |-- (WppD (PQ' this) (fun _ => Q) ** F') ->
    F
    |-- destroy (resolve:=resolve) ti dt cls this Q ** F'.
Proof. Admitted.

Lemma wp_rhs_cast_noop:
  forall (resolve : genv) (ti : thread_info) (ρ : region)
    (ty : type) (e : Expr) (Q : val -> FreeTemps -> mpred),
  wp_rhs (resolve:=resolve) ti ρ e Q |-- wp_rhs (resolve:=resolve) ti ρ (Ecast Cnoop (Rvalue, e) ty) Q.
Proof. intros. eapply wpe_cast_noop with (m:=Rvalue). Qed.

Lemma wp_lhs_cast_noop:
  forall (resolve : genv) (ti : thread_info) (ρ : region)
    (ty : type) (e : Expr) (Q : val -> FreeTemps -> mpred),
  wp_lhs (resolve:=resolve) ti ρ e Q |-- wp_lhs (resolve:=resolve) ti ρ (Ecast Cnoop (Lvalue, e) ty) Q.
Proof. intros; eapply wpe_cast_noop with (m:=Lvalue). Qed.

Theorem wp_decl_reference : forall resolve ρ x ty ti init k Q,
    wp_lhs (resolve:=resolve) ti ρ init (fun a free =>
             _local ρ x &~ a -* (free ** k (Kfree (_local ρ x &~ a) Q)))
    |-- wp_decl (resolve:=resolve) ti ρ x (Treference ty) (Some init) k Q.
Proof. reflexivity. Qed.


Theorem wp_decl_pointer : forall resolve ρ x ty ti init k Q,
    match init with
    | None =>
      Forall a, tlocal_at ρ x a (uninit (Tpointer ty))
              -* k (Kfree (tlocal ρ x (tany (Tpointer ty))) Q)
    | Some init =>
      wp_rhs (resolve:=resolve) ti ρ init (fun v free =>
                 Forall a, tlocal_at ρ x a (tprim (Tpointer ty) v)
              -* (free ** k (Kfree (tlocal ρ x (tany (Tpointer ty))) Q)))
    end
    |-- wp_decl (resolve:=resolve) ti ρ x (Tpointer ty) init k Q.
Proof.
  simpl; intros. unfold tlocal.
  destruct init.
  { eapply Proper_wp_rhs. red. red. intros.
    work.
    eapply wandSPE.
    2:{ eapply sepSPC. }
    eapply lforallL with (x0:=a1).
    eapply wandSP_lentails_m.
    { reflexivity. }
    work. }
  { work.
    eapply wandSPE.
    2:{ eapply sepSPC. }
    eapply lforallL.
    reflexivity. }
Qed.

Theorem wp_decl_int : forall resolve ρ x a b ti init k Q,
    match init with
    | None =>
      tlocal ρ x (uninit (Tint a b)) -* k (Kfree (tlocal ρ x (tany (Tint a b))) Q)
    | Some init =>
      wp_rhs (resolve:=resolve) ti ρ init (fun v free =>
                 tlocal ρ x (tprim (Tint a b) v)
              -* (free ** k (Kfree (tlocal ρ x (tany (Tint a b))) Q)))
    end
    |-- wp_decl (resolve:=resolve) ti ρ x (Tint a b) init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl__int : forall resolve ρ x ti init k Q,
    match init with
    | None =>
      tlocal ρ x (uninit T_int) -* k (Kfree (tlocal ρ x (tany T_int)) Q)
    | Some init =>
      wp_rhs (resolve:=resolve) ti ρ init (fun v free =>
                 tlocal ρ x (tprim T_int v)
              -* (free ** k (Kfree (tlocal ρ x (tany T_int)) Q)))
    end
    |-- wp_decl (resolve:=resolve) ti ρ x T_int init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl__ulong : forall resolve ρ x ti init k Q,
    match init with
    | None =>
      tlocal ρ x (uninit T_ulong) -* k (Kfree (tlocal ρ x (tany T_ulong)) Q)
    | Some init =>
      wp_rhs (resolve:=resolve) ti ρ init (fun v free =>
                 tlocal ρ x (tprim T_ulong v)
              -* (free ** k (Kfree (tlocal ρ x (tany T_ulong)) Q)))
    end
    |-- wp_decl (resolve:=resolve) ti ρ x T_ulong init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl__int32 : forall resolve ρ x ti init k Q,
    match init with
    | None =>
      tlocal ρ x (uninit T_int32) -* k (Kfree (tlocal ρ x (tany T_int32)) Q)
    | Some init =>
      wp_rhs (resolve:=resolve) ti ρ init (fun v free =>
                 tlocal ρ x (tprim T_int32 v)
              -* (free ** k (Kfree (tlocal ρ x (tany T_int32)) Q)))
    end
    |-- wp_decl (resolve:=resolve) ti ρ x T_int32 init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_char : forall resolve ρ x a b ti init k Q,
    (let clean := tlocal ρ x (tany (Tchar a b)) in
    match init with
    | None =>
      tlocal ρ x (uninit (Tchar a b)) -* k (Kfree clean Q)
    | Some init =>
      wp_rhs (resolve:=resolve) ti ρ init (fun v free =>
                 tlocal ρ x (tprim (Tchar a b) v)
              -* (free ** k (Kfree clean Q)))
    end)
    |-- wp_decl (resolve:=resolve) ti ρ x (Tchar a b) init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_bool : forall resolve ρ x ti init k Q,
    (let clean := k (Kfree (tlocal ρ x (tany Tbool)) Q) in
    match init with
    | None =>
      tlocal ρ x (uninit Tbool) -* clean
    | Some init =>
      wp_rhs (resolve:=resolve) ti ρ init (fun v free =>
                 tlocal ρ x (tprim Tbool v)
              -* (free ** clean))
    end)
    |-- wp_decl (resolve:=resolve) ti ρ x Tbool init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_qualified : forall resolve ρ x q ty ti init k Q,
    wp_decl (resolve:=resolve) ti ρ x ty init k Q
    |-- wp_decl (resolve:=resolve) ti ρ x (Tqualified q ty) init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_const : forall resolve ρ x ty ti init k Q,
    wp_decl (resolve:=resolve) ti ρ x ty init k Q
    |-- wp_decl (resolve:=resolve) ti ρ x (Qconst ty) init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_mut : forall resolve ρ x ty ti init k Q,
    wp_decl (resolve:=resolve) ti ρ x ty init k Q
    |-- wp_decl (resolve:=resolve) ti ρ x (Qmut ty) init k Q.
Proof. reflexivity. Qed.

(* conditions *)
Lemma wp_lhs_condition : forall resolve ti ρ ty tst th el Q,
    wp_rhs (resolve:=resolve) ti ρ tst (fun v1 free =>
       if is_true v1
       then wp_lhs (resolve:=resolve) ti ρ th (fun v free' => Q v (free ** free'))
       else wp_lhs (resolve:=resolve) ti ρ el (fun v free' => Q v (free ** free')))
    |-- wp_lhs (resolve:=resolve) ti ρ (Eif tst th el ty) Q.
Proof. intros; eapply wp_condition with (m:=Lvalue). Qed.

Lemma wp_rhs_condition : forall resolve ti ρ ty tst th el Q,
    wp_rhs (resolve:=resolve) ti ρ tst (fun v1 free =>
      if is_true v1
      then wp_rhs (resolve:=resolve) ti ρ th (fun v free' => Q v (free ** free'))
      else wp_rhs (resolve:=resolve) ti ρ el (fun v free' => Q v (free ** free')))
    |-- wp_rhs (resolve:=resolve) ti ρ (Eif tst th el ty) Q.
Proof. intros; eapply wp_condition with (m:=Rvalue). Qed.

Lemma wp_skip : forall (resolve : genv) (ti : thread_info) (ρ : region)
  (Q : Kpreds),
    Q.(k_normal) |-- wp (resolve:=resolve) ti ρ Sskip Q.
Proof. unfold Sskip. intros. rewrite <- wp_seq. reflexivity. Qed.

Lemma wp_return_lhs : forall resolve ti r Q e,
    wp_lhs (resolve:=resolve) ti r e (finish (fun res : val => k_return Q (Some res)))
    |-- wp (resolve:=resolve) ti r (Sreturn (Some (Lvalue, e))) Q.
Proof. intros. eapply wp_return_val with (c:=Lvalue). Qed.

Lemma wp_return_rhs : forall resolve ti r Q e,
    wp_rhs (resolve:=resolve) ti r e (finish (fun res : val => k_return Q (Some res)))
    |-- wp (resolve:=resolve) ti r (Sreturn (Some (Rvalue, e))) Q.
Proof. intros. eapply wp_return_val with (c:=Rvalue). Qed.

Theorem wp_lhs_member : forall {resolve} ti r  ty e f Q,
    wp_lhs (resolve:=resolve) ti r e (fun base free =>
        with_addr (_offsetL (_field f) (_eq base)) (fun addr => Q addr free))
    |-- wp_lhs (resolve:=resolve) ti r (Emember e f ty) Q.
Proof.
  intros. rewrite <- wp_lhs_member.
  eapply Proper_wp_lhs. red. red. intros.
  rewrite with_addr_defn. reflexivity.
Qed.

Theorem wp_lhs_subscript : forall {resolve} ti r e i t Q,
    wp_rhs (resolve:=resolve) ti r e (fun base free =>
        wp_rhs (resolve:=resolve) ti r i (fun idx free' =>
          Exists i, [| idx = Vint i |] **
          with_addr (_offsetL (_sub (drop_qualifiers t) i) (_eq base)) (fun addr => Q addr (free' ** free))))
      |-- wp_lhs (resolve:=resolve) ti r (Esubscript e i t) Q.
Proof.
  intros. rewrite <- wp_lhs_subscript.
  eapply Proper_wp_rhs; red; red; intros.
  eapply Proper_wp_rhs; red; red; intros.
  lift_ex_l fail.
  rewrite with_addr_defn.
  work. eapply landL1. reflexivity.
  eapply landL2. reflexivity.
Qed.

Lemma wp_rhs_unop_wp : forall {resolve} ti r o e ty Q,
    wp_rhs (resolve:=resolve) ti r e (fun v free =>
      wp_eval_unop o (drop_qualifiers ty) (drop_qualifiers ty) v (fun v' => Q v' free))
    |-- wp_rhs (resolve:=resolve) ti r (Eunop o e ty) Q.
Proof.
  intros.
  setoid_rewrite wp_eval_unop_defn.
  apply wp_rhs_unop.
Qed.

Lemma wp_rhs_binop_wp : forall {resolve} ti r o e1 e2 ty Q,
    wp_rhs (resolve:=resolve) ti r e1 (fun v1 free1 =>
      wp_rhs (resolve:=resolve) ti r e2 (fun v2 free2 =>
        wp_eval_binop o (drop_qualifiers (Typing.type_of e1)) (drop_qualifiers (Typing.type_of e2)) (drop_qualifiers ty) v1 v2 (fun v' => Q v' (free1 ** free2))))
    |-- wp_rhs (resolve:=resolve) ti r (Ebinop o e1 e2 ty) Q.
Proof.
  intros.
  setoid_rewrite wp_eval_binop_defn.
  apply wp_rhs_binop.
Qed.

Lemma wp_lhs_preinc_wp : forall {resolve} ti r e ty Q,
    wp_lhs (resolve:=resolve) ti r e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (drop_qualifiers ty) v') **
        wp_eval_binop Badd (drop_qualifiers (Typing.type_of e)) (drop_qualifiers (Typing.type_of e)) (drop_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q a free))
    |-- wp_lhs (resolve:=resolve) ti r (Epreinc e ty) Q.
Proof.
  intros.
  rewrite <-wp_lhs_preinc.
  eapply Proper_wp_lhs; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

Lemma wp_lhs_predec_wp : forall {resolve} ti r e ty Q,
    wp_lhs (resolve:=resolve) ti r e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (drop_qualifiers ty) v') **
        wp_eval_binop Bsub (drop_qualifiers (Typing.type_of e)) (drop_qualifiers (Typing.type_of e)) (drop_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q a free))
    |-- wp_lhs (resolve:=resolve) ti r (Epredec e ty) Q.
Proof.
  intros.
  rewrite <-wp_lhs_predec.
  eapply Proper_wp_lhs; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

Lemma wp_rhs_postinc_wp : forall {resolve} ti r e ty Q,
    wp_lhs (resolve:=resolve) ti r e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (drop_qualifiers ty) v') **
        wp_eval_binop Badd (drop_qualifiers (Typing.type_of e)) (drop_qualifiers (Typing.type_of e)) (drop_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q v' free))
    |-- wp_rhs (resolve:=resolve) ti r (Epostinc e ty) Q.
Proof.
  intros.
  rewrite <-wp_rhs_postinc.
  eapply Proper_wp_lhs; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

Lemma wp_rhs_postdec_wp : forall {resolve} ti r e ty Q,
    wp_lhs (resolve:=resolve) ti r e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (drop_qualifiers ty) v') **
        wp_eval_binop Bsub (drop_qualifiers (Typing.type_of e)) (drop_qualifiers (Typing.type_of e)) (drop_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q v' free))
    |-- wp_rhs (resolve:=resolve) ti r (Epostdec e ty) Q.
Proof.
  intros.
  rewrite <-wp_rhs_postdec.
  eapply Proper_wp_lhs; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.
