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

Section with_resolve.
  Context {resolve : genv}.
  Context (ti : thread_info) (ρ : region).

  Notation wp_rhs := (@wp_rhs resolve ti ρ).
  Notation wp_lhs := (@wp_lhs resolve ti ρ).
  Notation wp := (@wp resolve ti ρ).
  Notation wp_decl := (@wp_decl resolve ti ρ).
  Notation wp_eval_binop := (@wp_eval_binop resolve).
  Notation wp_eval_unop := (@wp_eval_unop resolve).

Lemma wp_rhs_local (ty : type) : forall x Q,
    Exists v, (tlocal ρ x (tprim (drop_qualifiers ty) v) ** ltrue) //\\ Q v empSP
    |-- wp_rhs (Ecast Cl2r (Lvalue, Evar (Lname x) ty) ty) Q.
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
Lemma wp_rhs_dot : forall obj f fty z Q,
    wp_lhs obj (fun base free =>

       Exists val,
         (_at (_offsetL (_field f) (_eq base)) (tprim (drop_qualifiers fty) val) ** ltrue) //\\
       Q val free)
    |-- wp_rhs (Ecast Cl2r (Lvalue, Emember obj f fty) z) Q.
Proof. Admitted.

Lemma wp_lhs_assign_member_ignore : forall f t obj e t' Q,
    wp_lhs obj (fun base free =>
    wp_rhs e (fun v' free' =>
        _at (_offsetL (_field f) (_eq base)) (uninit (drop_qualifiers t)) **
        (_at (_offsetL (_field f) (_eq base)) (tprim (drop_qualifiers t) v') -*
        Q (free ** free'))))
    |-- wp_lhs (Eassign (Emember obj f t) e t') (fun _ free => Q free).
Proof. Admitted.


Lemma wp_lhs_assign_member : forall f t obj e t' Q,
    wp_lhs obj (fun base free =>
    wp_rhs e (fun v' free' =>
        Exists addr, (_offsetL (_field f) (_eq base) &~ addr ** ltrue) //\\
        _at (_eq addr) (tany (drop_qualifiers t)) **
        (_at (_eq addr) (tprim (drop_qualifiers t) v') -* Q addr (free ** free'))))
    |-- wp_lhs (Eassign (Emember obj f t) e t') Q.
Proof. Admitted.


Theorem wp_call_glob : forall vc f ret ts es K PQ F F' ty ty' ty'',
   (vc = Lvalue \/ vc = Rvalue) ->
   F |-- (|> cglob (resolve:=resolve) f ti (SFunction ret ts PQ)) ** ltrue ->
   F
   |-- wps (wpAnys (resolve:=resolve) ti ρ) es (fun vs free => applyEach ts vs PQ (fun wpp _ =>
            WppD wpp (fun r => K r free))) empSP ** F' ->
   F
   |-- wp_rhs
         (Ecall (Ecast Cfunction2pointer (vc, Evar (Gname f) ty) ty') es ty'')
         K ** F'.
Proof. Admitted.

Lemma wp_member_call_glob:
  forall (gn : globname) this (ret : type)
    ty
    (ts : list type) es (K : val -> FreeTemps -> mpred)
    (PQ : val -> arrowFrom val ts WithPrePost) (F F' : mpred)
    cls q,
    F |-- (|> cglob (resolve:=resolve) gn ti (SMethod cls q ret ts PQ)) ** ltrue ->
    F
    |-- wp_lhs this (fun this =>
          wps (wpAnys (resolve:=resolve) ti ρ) es (fun (vs : list val) free =>
            applyEach ts vs (PQ this) (fun wpp _ =>
              WppD wpp (fun r => K r free)))) ** F' ->
    F
    |-- wp_rhs (Emember_call false gn this es ty) K ** F'.
Proof. Admitted.

Theorem wp_constructor_glob : forall cname cls ts es K PQ F F' ty,
   F |-- (|> cglob (resolve:=resolve) cname ti (SConstructor cls ts PQ)) ** ltrue ->
   F
   |-- wps (wpAnys (resolve:=resolve) ti ρ) es (fun vs free =>
             (* note(gmm): this is cancelling the `uninitialized_ty`
              * which is inserted into the pre-condition by `SConstructor` *)
             Forall a, applyEach ts vs (PQ a) (fun wpp _ =>
               WppD wpp (fun _ => K a free))) empSP ** F' ->
   F
   |-- wp_rhs (Econstructor cname es ty) K ** F'.
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
: forall x ty es cls cname (k : Kpreds -> mpred) ts PQ F F' Q dname PQ',
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
    |-- wp_decl x (Tref cls) (Some (Econstructor cname es ty)) k Q ** F'.
Proof. Admitted.

Theorem wp_destroy
: forall this cls F F' Q PQ' dt,
    F |-- (|> cglob (resolve:=resolve) (dtor_name dt cls) ti (SDestructor cls PQ')) ** ltrue ->
    F
    |-- (WppD (PQ' this) (fun _ => Q) ** F') ->
    F
    |-- destroy (resolve:=resolve) ti dt cls this Q ** F'.
Proof. Admitted.

Lemma wp_rhs_cast_noop:
  forall (ty : type) (e : Expr) (Q : val -> FreeTemps -> mpred),
  wp_rhs e Q |-- wp_rhs (Ecast Cnoop (Rvalue, e) ty) Q.
Proof. intros. eapply wpe_cast_noop with (m:=Rvalue). Qed.

Lemma wp_lhs_cast_noop:
  forall (ty : type) (e : Expr) (Q : val -> FreeTemps -> mpred),
  wp_lhs e Q |-- wp_lhs (Ecast Cnoop (Lvalue, e) ty) Q.
Proof. intros; eapply wpe_cast_noop with (m:=Lvalue). Qed.

Theorem wp_decl_reference : forall x ty init k Q,
    wp_lhs init (fun a free => _local ρ x &~ a -* (free ** k (Kfree (_local ρ x &~ a) Q)))
    |-- wp_decl x (Treference ty) (Some init) k Q.
Proof. reflexivity. Qed.


Theorem wp_decl_pointer : forall x ty init k Q,
    match init with
    | None =>
      Forall a, tlocal_at ρ x a (uninit (Tpointer ty))
              -* k (Kfree (tlocal ρ x (tany (Tpointer ty))) Q)
    | Some init =>
      wp_rhs init (fun v free =>
                 Forall a, tlocal_at ρ x a (tprim (Tpointer ty) v)
              -* (free ** k (Kfree (tlocal ρ x (tany (Tpointer ty))) Q)))
    end
    |-- wp_decl x (Tpointer ty) init k Q.
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

Theorem wp_decl_int : forall x a b init k Q,
    match init with
    | None =>
      tlocal ρ x (uninit (Tint a b)) -* k (Kfree (tlocal ρ x (tany (Tint a b))) Q)
    | Some init =>
      wp_rhs init (fun v free =>
                 tlocal ρ x (tprim (Tint a b) v)
              -* (free ** k (Kfree (tlocal ρ x (tany (Tint a b))) Q)))
    end
    |-- wp_decl x (Tint a b) init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl__int : forall x init k Q,
    match init with
    | None =>
      tlocal ρ x (uninit T_int) -* k (Kfree (tlocal ρ x (tany T_int)) Q)
    | Some init =>
      wp_rhs init (fun v free =>
                 tlocal ρ x (tprim T_int v)
              -* (free ** k (Kfree (tlocal ρ x (tany T_int)) Q)))
    end
    |-- wp_decl x T_int init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl__ulong : forall x init k Q,
    match init with
    | None =>
      tlocal ρ x (uninit T_ulong) -* k (Kfree (tlocal ρ x (tany T_ulong)) Q)
    | Some init =>
      wp_rhs init (fun v free =>
                 tlocal ρ x (tprim T_ulong v)
              -* (free ** k (Kfree (tlocal ρ x (tany T_ulong)) Q)))
    end
    |-- wp_decl x T_ulong init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl__int32 : forall x init k Q,
    match init with
    | None =>
      tlocal ρ x (uninit T_int32) -* k (Kfree (tlocal ρ x (tany T_int32)) Q)
    | Some init =>
      wp_rhs init (fun v free =>
                 tlocal ρ x (tprim T_int32 v)
              -* (free ** k (Kfree (tlocal ρ x (tany T_int32)) Q)))
    end
    |-- wp_decl x T_int32 init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_char : forall x a b init k Q,
    (let clean := tlocal ρ x (tany (Tchar a b)) in
    match init with
    | None =>
      tlocal ρ x (uninit (Tchar a b)) -* k (Kfree clean Q)
    | Some init =>
      wp_rhs init (fun v free =>
                 tlocal ρ x (tprim (Tchar a b) v)
              -* (free ** k (Kfree clean Q)))
    end)
    |-- wp_decl x (Tchar a b) init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_bool : forall x init k Q,
    (let clean := k (Kfree (tlocal ρ x (tany Tbool)) Q) in
    match init with
    | None =>
      tlocal ρ x (uninit Tbool) -* clean
    | Some init =>
      wp_rhs init (fun v free =>
                 tlocal ρ x (tprim Tbool v)
              -* (free ** clean))
    end)
    |-- wp_decl x Tbool init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_qualified : forall x q ty init k Q,
    wp_decl x ty init k Q
    |-- wp_decl x (Tqualified q ty) init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_const : forall x ty init k Q,
    wp_decl x ty init k Q
    |-- wp_decl x (Qconst ty) init k Q.
Proof. reflexivity. Qed.

Theorem wp_decl_mut : forall x ty init k Q,
    wp_decl x ty init k Q
    |-- wp_decl x (Qmut ty) init k Q.
Proof. reflexivity. Qed.

(* conditions *)
Lemma wp_lhs_condition : forall ty tst th el Q,
    wp_rhs tst (fun v1 free =>
       if is_true v1
       then wp_lhs th (fun v free' => Q v (free ** free'))
       else wp_lhs el (fun v free' => Q v (free ** free')))
    |-- wp_lhs (Eif tst th el ty) Q.
Proof. intros; eapply wp_condition with (m:=Lvalue). Qed.

Lemma wp_rhs_condition : forall ty tst th el Q,
    wp_rhs tst (fun v1 free =>
      if is_true v1
      then wp_rhs th (fun v free' => Q v (free ** free'))
      else wp_rhs el (fun v free' => Q v (free ** free')))
    |-- wp_rhs (Eif tst th el ty) Q.
Proof. intros; eapply wp_condition with (m:=Rvalue). Qed.

Lemma wp_skip : forall (Q : Kpreds),
    Q.(k_normal) |-- wp Sskip Q.
Proof. unfold Sskip. intros. rewrite <- wp_seq. reflexivity. Qed.

Lemma wp_return_lhs : forall Q e,
    wp_lhs e (finish (fun res : val => k_return Q (Some res)))
    |-- wp (Sreturn (Some (Lvalue, e))) Q.
Proof. intros. eapply wp_return_val with (c:=Lvalue). Qed.

Lemma wp_return_rhs : forall Q e,
    wp_rhs e (finish (fun res : val => k_return Q (Some res)))
    |-- wp (Sreturn (Some (Rvalue, e))) Q.
Proof. intros. eapply wp_return_val with (c:=Rvalue). Qed.

Theorem wp_lhs_member : forall ty e f Q,
    wp_lhs e (fun base free =>
        with_addr (_offsetL (_field f) (_eq base)) (fun addr => Q addr free))
    |-- wp_lhs (Emember e f ty) Q.
Proof.
  intros. rewrite <- wp_lhs_member.
  eapply Proper_wp_lhs. red. red. intros.
  rewrite with_addr_defn. reflexivity.
Qed.

Theorem wp_lhs_subscript : forall e i t Q,
    wp_rhs e (fun base free =>
        wp_rhs i (fun idx free' =>
          Exists i, [| idx = Vint i |] **
          with_addr (_offsetL (_sub (drop_qualifiers t) i) (_eq base)) (fun addr => Q addr (free' ** free))))
      |-- wp_lhs (Esubscript e i t) Q.
Proof.
  intros. rewrite <- wp_lhs_subscript.
  eapply Proper_wp_rhs; red; red; intros.
  eapply Proper_wp_rhs; red; red; intros.
  lift_ex_l fail.
  rewrite with_addr_defn.
  work. eapply landL1. reflexivity.
  eapply landL2. reflexivity.
Qed.

Lemma wp_rhs_unop_wp : forall o e ty Q,
    wp_rhs e (fun v free =>
      wp_eval_unop o (drop_qualifiers (type_of e)) (drop_qualifiers ty) v (fun v' => Q v' free))
    |-- wp_rhs (Eunop o e ty) Q.
Proof.
  intros.
  setoid_rewrite wp_eval_unop_defn.
  eapply wp_rhs_unop.
Qed.

Lemma wp_rhs_binop_wp : forall o e1 e2 ty Q,
    wp_rhs e1 (fun v1 free1 =>
      wp_rhs e2 (fun v2 free2 =>
        wp_eval_binop o (drop_qualifiers (Typing.type_of e1)) (drop_qualifiers (Typing.type_of e2)) (drop_qualifiers ty) v1 v2 (fun v' => Q v' (free1 ** free2))))
    |-- wp_rhs (Ebinop o e1 e2 ty) Q.
Proof.
  intros.
  setoid_rewrite wp_eval_binop_defn.
  apply wp_rhs_binop.
Qed.

Lemma wp_lhs_preinc_wp : forall e ty Q,
    match companion_type (Typing.type_of e) with
    | Some cty =>
    wp_lhs e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (drop_qualifiers ty) v') **
        wp_eval_binop Badd (drop_qualifiers (Typing.type_of e)) cty (drop_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q a free))
    | None => lfalse
    end
    |-- wp_lhs (Epreinc e ty) Q.
Proof.
  intros.
  rewrite <-wp_lhs_preinc.
  destruct (companion_type (type_of e)); auto.
  eapply Proper_wp_lhs; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

Lemma wp_lhs_predec_wp : forall e ty Q,
    match companion_type (Typing.type_of e) with
    | Some cty =>
    wp_lhs e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (drop_qualifiers ty) v') **
        wp_eval_binop Bsub (drop_qualifiers (Typing.type_of e)) cty (drop_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q a free))
    | None => lfalse
    end
    |-- wp_lhs (Epredec e ty) Q.
Proof.
  intros.
  rewrite <-wp_lhs_predec.
  destruct (companion_type (type_of e)); auto.
  eapply Proper_wp_lhs; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

Lemma wp_rhs_postinc_wp : forall e ty Q,
    match companion_type (type_of e) with
    | Some cty =>
    wp_lhs e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (drop_qualifiers ty) v') **
        wp_eval_binop Badd (drop_qualifiers (Typing.type_of e)) cty (drop_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q v' free))
    | None => lfalse
    end
    |-- wp_rhs (Epostinc e ty) Q.
Proof.
  intros.
  rewrite <-wp_rhs_postinc.
  destruct (companion_type (type_of e)); auto.
  eapply Proper_wp_lhs; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

Lemma wp_rhs_postdec_wp : forall e ty Q,
    match companion_type (type_of e) with
    | Some cty =>
    wp_lhs e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (drop_qualifiers ty) v') **
        wp_eval_binop Bsub (drop_qualifiers (Typing.type_of e)) cty (drop_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q v' free))
    | None => lfalse
    end
    |-- wp_rhs (Epostdec e ty) Q.
Proof.
  intros.
  rewrite <-wp_rhs_postdec.
  destruct (companion_type (type_of e)); auto.
  eapply Proper_wp_lhs; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

End with_resolve.
