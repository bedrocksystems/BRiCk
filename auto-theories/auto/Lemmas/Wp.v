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
From Cpp.Syntax Require Import CompilationUnit Expr Types Typing.

Local Ltac work :=
  discharge fail idtac fail fail eauto.

Section with_resolve.
  Context {resolve : genv}.
  Context (ti : thread_info) (ρ : region).

  Notation wp_prval := (@wp_prval resolve ti ρ).
  Notation wp_rval := (@wp_rval resolve ti ρ).
  Notation wp_lval := (@wp_lval resolve ti ρ).
  Notation wp_xval := (@wp_xval resolve ti ρ).
  Notation wp_args := (@wp_args resolve ti ρ).
  Notation wp_init := (@wp_init resolve ti ρ).
  Notation wp := (@wp resolve ti ρ).
  Notation wp_decl := (@wp_decl resolve ti ρ).
  Notation wp_eval_binop := (@wp_eval_binop resolve).
  Notation wp_eval_unop := (@wp_eval_unop resolve).

  Definition find_constant (nm : globname) (m : compilation_unit) : option Expr :=
    match CompilationUnit.lookup_global m nm with
    | Some (Gconstant _ e) => Some e
    | _ => None
    end.

  Definition find_struct (nm : globname) (m : compilation_unit) : option Struct :=
    match CompilationUnit.lookup_global m nm with
    | Some (Gstruct s) => Some s
    | _ => None
    end.

  Theorem find_struct_ok : forall nm m s,
      find_struct nm m = Some s ->
      denoteModule m |-- denoteModule m ** denoteGlobal nm (Gstruct s).
  Proof.
    destruct m; simpl.
    unfold find_struct. unfold lookup_global.
    intros.
    simpl in *.
    unfold denoteModule. simpl.
    work.
  Qed.

  (* accessing constants *)
  Theorem wp_prval_const : forall m ty cnst e Q R P,
    P |-- denoteModule m ** ltrue ->
    find_constant cnst m = Some e ->
    P |-- wp_prval e Q ** R ->
    P |-- wp_prval (Econst_ref (Gname cnst) ty) Q ** R.
  Proof.
    intros.
  Admitted.

  (* Variable access *)
  Theorem wp_prval_cast_l2r_l : forall ty e Q,
      wp_lval e (fun a free =>
           Exists v, (_at (_eq a) (tprim (erase_qualifiers ty) v) **
                     (_at (_eq a) (tprim (erase_qualifiers ty) v) -* Q v free)))
      |-- wp_prval (Ecast Cl2r (Lvalue, e) ty) Q.
  Proof.
    intros. rewrite <- wp_prval_cast_l2r_l.
    eapply Proper_wp_lval. red. red. intros.
    eapply lexists_lentails_m. intro.
    work.
    admit. (* perm_left ltac:(idtac; perm_right ltac:(idtac; eapply wand_apply)).
    work. *)
  Admitted.

  Theorem wp_prval_cast_l2r_x : forall ty e Q,
      wp_xval e (fun a free =>
                   Exists v, (_at (_eq a) (tprim (erase_qualifiers ty) v) **
                             (_at (_eq a) (tprim (erase_qualifiers ty) v) -* Q v free)))
      |-- wp_prval (Ecast Cl2r (Xvalue, e) ty) Q.
  Proof.
    intros. rewrite <- wp_prval_cast_l2r_x.
    eapply Proper_wp_xval. red. red. intros.
    eapply lexists_lentails_m. intro.
    work.
    admit. (* perm_left ltac:(idtac; perm_right ltac:(idtac; eapply wand_apply)).
    work. *)
  Admitted.

  Lemma wp_prval_local (ty : type) : forall x Q,
    Exists p, Exists v,
      tlocal_at ρ x p (tprim (erase_qualifiers ty) v) **
      (tlocal_at ρ x p (tprim (erase_qualifiers ty) v) -* Q v empSP)
    |-- wp_prval (Ecast Cl2r (Lvalue, Evar (Lname x) ty) ty) Q.
  Proof.
    intros. unfold tlocal_at.
    work.
    rewrite <- wp_prval_cast_l2r_l.
    rewrite <- wp_lval_lvar.
    work.
    rewrite (sepSPC (addr_of _ _)), sepSPA.
    apply wandSPL; work.
  Qed.

  (* this is the common case for member access
   *)
  Lemma wp_prval_dot : forall obj f fty z Q,
      wp_lval obj (fun base free => Exists val,
         (_at (_offsetL (_field f) (_eq base)) (tprim (erase_qualifiers fty) val) **
         (_at (_offsetL (_field f) (_eq base)) (tprim (erase_qualifiers fty) val) -*
          Q val free)))
      |-- wp_prval (Ecast Cl2r (Lvalue, Emember obj f fty) z) Q.
  Proof.
    intros. rewrite <- wp_prval_cast_l2r_l. rewrite <- wp_lval_member.
    apply Proper_wp_lval. intro. intro. work.
    - admit.
    - admit.
  Admitted.


  (* member assignment *)
  Lemma wp_lval_assign_member_ignore : forall f t obj e t' Q,
      wp_lval obj (fun base free => wp_prval e (fun v' free' =>
         _at (_offsetL (_field f) (_eq base)) (uninit (erase_qualifiers t)) **
        (_at (_offsetL (_field f) (_eq base)) (tprim (erase_qualifiers t) v') -*
         Q (free ** free'))))
      |-- wp_lval (Eassign (Emember obj f t) e t') (fun _ free => Q free).
  Proof. Admitted.

  Lemma wp_lval_assign_member : forall f t obj e t' Q,
      wp_lval obj (fun base free => wp_prval e (fun v' free' =>
         Exists addr, (_offsetL (_field f) (_eq base) &~ addr ** ltrue) //\\
           _at (_eq addr) (tany (erase_qualifiers t)) **
           (_at (_eq addr) (tprim (erase_qualifiers t) v') -* Q addr (free ** free'))))
      |-- wp_lval (Eassign (Emember obj f t) e t') Q.
  Proof. Admitted.

  (* casting *)
  Theorem wp_prval_cast_tovoid : forall vc e ty Q,
      wpe (resolve:=resolve) ti ρ vc e (fun _ => Q (Vint 0))
      |-- wp_prval (Ecast C2void (vc,e) ty) Q.
  Proof.
    intros. etransitivity; [ | eapply  wpe_cast_tovoid with (vc':=Rvalue) ].
    reflexivity.
  Qed.

  Theorem wp_rval_xval_materialize : forall ty e Q,
    wp_xval (Ematerialize_temp e ty) Q
    |-- wp_rval (Ematerialize_temp e ty) Q.
  Proof. intros. eapply lorR2. reflexivity. Qed.


  (* function calls *)
  Theorem wp_prval_call_glob : forall vc f ret ts es K PQ F F' ty ty' ty'',
      match vc with
      | Lvalue | Rvalue => True
      | _ => False
      end ->
      F |-- (|> cglob (resolve:=resolve) f ti (SFunction ret ts PQ)) ** ltrue ->
      F |-- wp_args es (fun vs free => applyEach ts vs PQ (fun wpp _ =>
               WppD wpp (fun r => K r free))) ** F' ->
      F |-- wp_prval (Ecall (Ecast Cfunction2pointer (vc, Evar (Gname f) ty) ty') es ty'')
                     K ** F'.
  (* note(gmm): this incorporates both the C and the C++ calling rules *)
  Proof. Admitted.

  Theorem wp_xval_call_glob : forall vc f ret ts es K PQ F F' ty ty' ty'',
      match vc with
      | Lvalue | Rvalue => True
      | _ => False
      end ->
      F |-- (|> cglob (resolve:=resolve) f ti (SFunction ret ts PQ)) ** ltrue ->
      F |-- wp_args es (fun vs free => applyEach ts vs PQ (fun wpp _ =>
               WppD wpp (fun r => K r free))) ** F' ->
      F |-- wp_xval (Ecall (Ecast Cfunction2pointer (vc, Evar (Gname f) ty) ty') es ty'')
                    K ** F'.
  (* note(gmm): this incorporate both the C and the C++ calling rules *)
  Proof. Admitted.

  Theorem wp_init_call_glob:
    forall (vc : ValCat)
      (f : globname) (ret : type) (ts : list type) (es : list (ValCat * Expr))
      (K : FreeTemps -> mpred) (PQ : arrowFrom val ts WithPrePost) addr
      (F F' : mpred) (ty ty' ty'' ty''' : type),
      match vc with
      | Xvalue => False
      | _ => True
      end ->
      F |-- (|> cglob (resolve:=resolve) f ti (SFunction ret ts PQ)) ** ltrue ->
      F |-- wp_args es (fun (vs : list val) (free : FreeTemps) =>
           applyEach ts vs PQ
                     (fun (wpp : WithPrePost) (_ : list (type * val)) =>
                        _at (_eq addr) (uninit (erase_qualifiers ty''')) **
                            WppD wpp (fun r : val => [| r = addr |] -* K free))) ** F' ->
      F |-- wp_init ty''' addr
        (Ecall (Ecast Cfunction2pointer (vc, Evar (Gname f) ty) ty') es ty'') K ** F'.
  Proof. Admitted.

  (* member calls (non-virtual) *)
  Lemma wp_prval_member_call_glob:
    forall (gn : globname) this (ret : type)
      ty
      (ts : list type) es (K : val -> FreeTemps -> mpred)
      (PQ : val -> arrowFrom val ts WithPrePost) (F F' : mpred)
      cls q,
      F |-- (|> cglob (resolve:=resolve) gn ti (SMethod cls q ret ts PQ)) ** ltrue ->
      F |-- wp_lval this (fun this free' => wp_args es (fun (vs : list val) free =>
               applyEach ts vs (PQ this) (fun wpp _ =>
                    WppD wpp (fun r => free' ** K r free)))) ** F' ->
      F |-- wp_prval (Emember_call false gn this es ty) K ** F'.
  Proof. Admitted.

  Lemma wp_xval_member_call_glob:
    forall (gn : globname) this (ret : type)
      ty
      (ts : list type) es (K : val -> FreeTemps -> mpred)
      (PQ : val -> arrowFrom val ts WithPrePost) (F F' : mpred)
      cls q,
      F |-- (|> cglob (resolve:=resolve) gn ti (SMethod cls q ret ts PQ)) ** ltrue ->
      F |-- wp_lval this (fun this free' => wp_args es (fun (vs : list val) free =>
               applyEach ts vs (PQ this) (fun wpp _ =>
                    WppD wpp (fun r => free' ** K r free)))) ** F' ->
      F |-- wp_xval (Emember_call false gn this es ty) K ** F'.
  Proof. Admitted.

  Theorem wp_init_member_call_glob:
    forall (vc : ValCat)
      (f : obj_name) this (ret : type) (ts : list type) (es : list (ValCat * Expr))
      (K : FreeTemps -> mpred) (PQ : arrowFrom val ts WithPrePost) addr
      (F F' : mpred) (ty ty' : type),
      match vc with
      | Xvalue => False
      | _ => True
      end ->
      F |-- (|> cglob (resolve:=resolve) f ti (SFunction ret ts PQ)) ** ltrue ->
      F |-- wp_args es (fun (vs : list val) (free : FreeTemps) =>
           applyEach ts vs PQ
                     (fun (wpp : WithPrePost) (_ : list (type * val)) =>
                        _at (_eq addr) (uninit (erase_qualifiers ty')) **
                            WppD wpp (fun r : val => [| r = addr |] -* K free))) ** F' ->
      F |-- wp_init ty' addr (Emember_call false f this es ty) K ** F'.
  Proof. Admitted.

  (* constructors *)
  Theorem wp_init_ctor_glob : forall loc cname cls ts es K PQ F F' ty,
      F |-- (|> cglob (resolve:=resolve) cname ti (SConstructor cls ts PQ)) ** ltrue ->
      F |-- wp_args es (fun vs free => applyEach ts vs (PQ loc) (fun wpp _ =>
               _at (_eq loc) (uninit (Tref cls)) **
               (* ^ note: this is because SConstructor inserts the
                * [uninit] fact, so we have to add it here *)
               WppD wpp (fun _ => K free))) ** F' ->
      F |-- wp_init (Tref cls) loc (Econstructor cname es ty) K ** F'.
  Proof. Admitted.

  (* destructors *)
  Theorem wp_destroy
    : forall this cls F F' Q PQ' dt,
      F |-- (|> cglob (resolve:=resolve) dt ti (SDestructor cls PQ')) ** ltrue ->
      F |-- (WppD (PQ' this) (fun _ => Q) ** F') ->
      F |-- destruct_obj (resolve:=resolve) ti dt cls this Q ** F'.
  Proof. Admitted.

  (* todo(gmm): destroy an array? *)

  (* declarations *)
  Theorem wp_decl_class_dtor
    : forall x ty es cls cname (k : Kpreds -> mpred) ts PQ F F' Q PQ' dtor,
      F |-- (|> cglob (resolve:=resolve) cname ti (SConstructor cls ts PQ)) ** ltrue ->
      F |-- (|> cglob (resolve:=resolve) dtor ti (SDestructor cls PQ')) ** ltrue ->
      F |-- wp_args es (fun vs free =>
               (* note(gmm): this is cancelling the `uninitialized_ty`
                * which is inserted into the pre-condition by `SConstructor` *)
               Forall a, applyEach ts vs (PQ a) (fun wpp _ =>
                 WppD wpp (fun _ => free ** (_local ρ x &~ a -* k (Kat_exit (fun Q' =>
                     let wpp := PQ' a in
                     WppD wpp (fun _ =>
                             (* note(gmm): this is canceling the dead memory
                              * that is inserted by `SDestructor` *)
                             _local ρ x &~ a ** Q')) Q))))) ** F' ->
      F |-- wp_decl x (Tref cls) (Some (Econstructor cname es ty)) (Some dtor) k Q ** F'.
  Proof. Admitted.

  Theorem wp_decl_class_no_dtor
    : forall x ty es cls cname (k : Kpreds -> mpred) ts PQ F F' Q,
      F |-- (|> cglob (resolve:=resolve) cname ti (SConstructor cls ts PQ)) ** ltrue ->
      F |-- wp_args es (fun vs free =>
               (* note(gmm): this is cancelling the `uninitialized_ty`
                * which is inserted into the pre-condition by `SConstructor` *)
               Forall a, applyEach ts vs (PQ a) (fun wpp _ =>
                 WppD wpp
                      (fun _ => free ** (_local ρ x &~ a -* k (Kat_exit (fun Q' =>
                                                                        _local ρ x &~ a ** _at (_eq a) (tany (Tref cls)) ** Q') Q))))) ** F' ->
      F |-- wp_decl x (Tref cls) (Some (Econstructor cname es ty)) None k Q ** F'.
  Proof. Admitted.

(*

(** STOPPED *)

Lemma wp_prval_cast_noop:
  forall (ty : type) (e : Expr) (Q : val -> FreeTemps -> mpred),
  wp_prval e Q |-- wp_prval (Ecast Cnoop (Rvalue, e) ty) Q.
Proof. intros. eapply wpe_cast_noop with (m:=Rvalue). Qed.

Lemma wp_lval_cast_noop:
  forall (ty : type) (e : Expr) (Q : val -> FreeTemps -> mpred),
  wp_lval e Q |-- wp_lval (Ecast Cnoop (Lvalue, e) ty) Q.
Proof. intros; eapply wpe_cast_noop with (m:=Lvalue). Qed.

Theorem wp_decl_reference : forall x ty init k Q,
    wp_lval init (fun a free => _local ρ x &~ a -* (free ** k (Kfree (_local ρ x &~ a) Q)))
    |-- wp_decl x (Treference ty) (Some init) k Q.
Proof. reflexivity. Qed.


Theorem wp_decl_pointer : forall x ty init k Q,
    match init with
    | None =>
      Forall a, tlocal_at ρ x a (uninit (Tpointer ty))
              -* k (Kfree (tlocal ρ x (tany (Tpointer ty))) Q)
    | Some init =>
      wp_prval init (fun v free =>
                 Forall a, tlocal_at ρ x a (tprim (Tpointer ty) v)
              -* (free ** k (Kfree (tlocal ρ x (tany (Tpointer ty))) Q)))
    end
    |-- wp_decl x (Tpointer ty) init k Q.
Proof.
  simpl; intros. unfold tlocal.
  destruct init.
  { eapply Proper_wp_prval. red. red. intros.
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
      wp_prval init (fun v free =>
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
      wp_prval init (fun v free =>
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
      wp_prval init (fun v free =>
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
      wp_prval init (fun v free =>
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
      wp_prval init (fun v free =>
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
      wp_prval init (fun v free =>
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
Lemma wp_lval_condition : forall ty tst th el Q,
    wp_prval tst (fun v1 free =>
       if is_true v1
       then wp_lval th (fun v free' => Q v (free ** free'))
       else wp_lval el (fun v free' => Q v (free ** free')))
    |-- wp_lval (Eif tst th el ty) Q.
Proof. intros; eapply wp_condition with (m:=Lvalue). Qed.

Lemma wp_prval_condition : forall ty tst th el Q,
    wp_prval tst (fun v1 free =>
      if is_true v1
      then wp_prval th (fun v free' => Q v (free ** free'))
      else wp_prval el (fun v free' => Q v (free ** free')))
    |-- wp_prval (Eif tst th el ty) Q.
Proof. intros; eapply wp_condition with (m:=Rvalue). Qed.

Lemma wp_skip : forall (Q : Kpreds),
    Q.(k_normal) |-- wp Sskip Q.
Proof. unfold Sskip. intros. rewrite <- wp_seq. reflexivity. Qed.

Lemma wp_return_lhs : forall Q e,
    wp_lval e (finish (fun res : val => k_return Q (Some res)))
    |-- wp (Sreturn (Some (Lvalue, e))) Q.
Proof. intros. eapply wp_return_val with (c:=Lvalue). Qed.

Lemma wp_return_rhs : forall Q e,
    wp_prval e (finish (fun res : val => k_return Q (Some res)))
    |-- wp (Sreturn (Some (Rvalue, e))) Q.
Proof. intros. eapply wp_return_val with (c:=Rvalue). Qed.

Theorem wp_lval_member : forall ty e f Q,
    wp_lval e (fun base free =>
        with_addr (_offsetL (_field f) (_eq base)) (fun addr => Q addr free))
    |-- wp_lval (Emember e f ty) Q.
Proof.
  intros. rewrite <- wp_lval_member.
  eapply Proper_wp_lval. red. red. intros.
  rewrite with_addr_defn. reflexivity.
Qed.

Theorem wp_lval_subscript : forall e i t Q,
    wp_prval e (fun base free =>
        wp_prval i (fun idx free' =>
          Exists i, [| idx = Vint i |] **
          with_addr (_offsetL (_sub (drop_qualifiers t) i) (_eq base)) (fun addr => Q addr (free' ** free))))
      |-- wp_lval (Esubscript e i t) Q.
Proof.
  intros. rewrite <- wp_lval_subscript.
  eapply Proper_wp_prval; red; red; intros.
  eapply Proper_wp_prval; red; red; intros.
  lift_ex_l fail.
  rewrite with_addr_defn.
  work. eapply landL1. reflexivity.
  eapply landL2. reflexivity.
Qed.

(* primitive operators *)

Lemma wp_prval_unop_wp : forall o e ty Q,
    wp_prval e (fun v free =>
      wp_eval_unop o (erase_qualifiers (type_of e)) (erase_qualifiers ty) v (fun v' => Q v' free))
    |-- wp_prval (Eunop o e ty) Q.
Proof.
  intros.
  setoid_rewrite wp_eval_unop_defn.
  eapply wp_prval_unop.
Qed.

Lemma wp_prval_binop_wp : forall o e1 e2 ty Q,
    wp_prval e1 (fun v1 free1 =>
      wp_prval e2 (fun v2 free2 =>
        wp_eval_binop o (erase_qualifiers (Typing.type_of e1)) (erase_qualifiers (Typing.type_of e2)) (erase_qualifiers ty) v1 v2 (fun v' => Q v' (free1 ** free2))))
    |-- wp_prval (Ebinop o e1 e2 ty) Q.
Proof.
  intros.
  setoid_rewrite wp_eval_binop_defn.
  apply wp_prval_binop.
Qed.

Lemma wp_lval_preinc_wp : forall e ty Q,
    match companion_type (Typing.type_of e) with
    | Some cty =>
    wp_lval e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (erase_qualifiers ty) v') **
        wp_eval_binop Badd (erase_qualifiers (Typing.type_of e)) cty (erase_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (erase_qualifiers ty) v'') -* Q a free))
    | None => lfalse
    end
    |-- wp_lval (Epreinc e ty) Q.
Proof.
  intros.
  rewrite <-wp_lval_preinc.
  destruct (companion_type (type_of e)); auto.
  eapply Proper_wp_lval; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

Lemma wp_lval_predec_wp : forall e ty Q,
    match companion_type (Typing.type_of e) with
    | Some cty =>
    wp_lval e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (erase_qualifiers ty) v') **
        wp_eval_binop Bsub (erase_qualifiers (Typing.type_of e)) cty (erase_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (erase_qualifiers ty) v'') -* Q a free))
    | None => lfalse
    end
    |-- wp_lval (Epredec e ty) Q.
Proof.
  intros.
  rewrite <-wp_lval_predec.
  destruct (companion_type (type_of e)); auto.
  eapply Proper_wp_lval; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

Lemma wp_prval_postinc_wp : forall e ty Q,
    match companion_type (type_of e) with
    | Some cty =>
    wp_lval e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (erase_qualifiers ty) v') **
        wp_eval_binop Badd (erase_qualifiers (Typing.type_of e)) cty (erase_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (erase_qualifiers ty) v'') -* Q v' free))
    | None => lfalse
    end
    |-- wp_prval (Epostinc e ty) Q.
Proof.
  intros.
  rewrite <-wp_prval_postinc.
  destruct (companion_type (type_of e)); auto.
  eapply Proper_wp_lval; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

Lemma wp_prval_postdec_wp : forall e ty Q,
    match companion_type (type_of e) with
    | Some cty =>
    wp_lval e (fun a free =>
      Exists v',
        _at (_eq a) (tprim (erase_qualifiers ty) v') **
        wp_eval_binop Bsub (erase_qualifiers (Typing.type_of e)) cty (erase_qualifiers ty) v' (Vint 1%Z) (fun v'' =>
          _at (_eq a) (tprim (erase_qualifiers ty) v'') -* Q v' free))
    | None => lfalse
    end
    |-- wp_prval (Epostdec e ty) Q.
Proof.
  intros.
  rewrite <-wp_prval_postdec.
  destruct (companion_type (type_of e)); auto.
  eapply Proper_wp_lval; red; red; intros.
  setoid_rewrite wp_eval_binop_defn.
  work.
Qed.

*)

End with_resolve.
