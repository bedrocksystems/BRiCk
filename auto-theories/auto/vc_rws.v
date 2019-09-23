(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(* Automation for code *)
Require Import LtacIter.LtacIter.

From Cpp Require Export Ast Sem.
Require Cpp.Auto.Lemmas.

From Cpp.Auto Require Export Discharge Definitions.

Global Opaque wp_decl.

(* we are working in a fairly rich separation logic, however, the fragment that
 * shows up in practice is relatively small.
 *)
Create HintDb wp_pre discriminated.

Hint Resolve Lemmas.wp_prval_dot Lemmas.wp_prval_local (* Lemmas.wp_lval_assign_member *) : wp_pre.

Local Ltac t :=
  discharge fail idtac fail fail idtac.

Create HintDb wp_all discriminated.

Hint Rewrite <-
     @wp_seq
     Lemmas.wp_return_lval
     Lemmas.wp_return_rval
     Lemmas.wp_return_xval
     @wp_return_void @wp_expr
     @wp_if_decl
     @wp_if
     @wp_for_init
     @wp_while_decl
     @wp_continue
     @wp_break
     Lemmas.wp_skip
     @wp_prval_atomic

     @wp_prval_binop
     @wp_prval_unop
     @wp_prval_bool
     @wp_lval_assign
     @wp_lval_bop_assign
     @wp_lval_lvar
     @wp_lval_gvar
     @wp_prval_seqand
     @wp_prval_seqor
     @wp_prval_int
     @wp_lval_deref
     @wp_prval_addrof
     Lemmas.wp_prval_cast_l2r_l
     Lemmas.wp_prval_cast_l2r_x
     @wp_prval_cast_integral
     @wp_prval_cast_int2bool
     @wp_prval_cast_ptr2bool
     @wp_prval_cast_null
     @wp_xval_cast_noop
     @wp_lval_cast_noop
     @wp_xval_lval_cast_noop
     @wp_lval_xval_cast_noop
     @wp_prval_cast_noop
     @wp_prval_cast_bitcast
     @wp_prval_cast_array2pointer
     @wp_null
     @wp_lval_member
     @wp_prval_this
     @wp_prval_alignof
     @wp_prval_alignof_e
     @wp_prval_sizeof
     @wp_prval_sizeof_e
     @wp_prval_postinc
     @wp_prval_postdec
     @wp_lval_preinc
     @wp_lval_predec
     Lemmas.wp_lval_condition
     Lemmas.wp_prval_condition
     @wp_prval_cast_user
     @wp_prval_cast_reinterpret
     @wp_prval_clean
     @wp_lval_temp
     @wp_lval_subscript

     Lemmas.wp_decl_mut
     Lemmas.wp_decl_const
     Lemmas.wp_decl_int
     Lemmas.wp_decl__int
     Lemmas.wp_decl__int32
     Lemmas.wp_decl__ulong
     Lemmas.wp_decl_char
     Lemmas.wp_decl_pointer
     Lemmas.wp_decl_reference

     Lemmas.wp_init_mut

     @wpd_deinit
  : wp_all.
Hint Rewrite <- @wp_init_clean : wp_all.
Hint Rewrite <- @wp_init_const @wp_init_mut : wp_all.
Hint Rewrite <- @wp_xval_temp : wp_all.
Hint Rewrite <- @wp_init_cast_noop : wp_all.
Hint Rewrite <- @wp_init_bind_temp : wp_all.
Hint Rewrite <- @Lemmas.wp_prval_cast_tovoid : wp_all.
Hint Rewrite <- @wp_xval_member @wp_prval_member @wp_lval_member : wp_all.

Hint Rewrite <- @Lemmas.wp_rval_xval_materialize @wp_prval_materialize : wp_all.


Hint Rewrite <- @Lemmas.wpi_initialize : wp_all.


Require Import Coq.Classes.Morphisms.

(* note(gmm): the following morphisms seem to be necessary *)
Global Instance lexists_ok : Proper (pointwise_relation val (Basics.flip lentails) ==> Basics.flip lentails) (@lexists mpred _ _).
Proof.
  red. red. intros. red.
  eapply lexists_lentails_m.
  eapply H.
Qed.
Global Instance lentails_ok : Proper (lentails ==> Basics.flip lentails ==> Basics.flip Basics.impl) (@lentails mpred _).
Proof.
  red. red. red. intros. red. intros. red.
  intros.
  etransitivity. eauto. etransitivity; eauto.
Qed.

Global Instance lentails_ok_R : forall P, Proper (lentails --> Basics.flip Basics.impl) (@lentails mpred _ P).
Proof.
  red. red. red. intros. red. intros.
  etransitivity. eauto. eapply H.
Qed.
Global Instance : subrelation eq (Basics.flip (@lentails mpred _)).
Proof. repeat red. intros. subst. reflexivity. Qed.
Global Instance : Transitive (Basics.flip (@lentails mpred _)).
Proof. do 2 red. intros. etransitivity. eapply H0. eapply H. Qed.

Global Instance :
  forall (resolve : genv) (ti : thread_info) (r : region) (e : Stmt) K,
  @Proper mpred
    (@lentails mpred ILogicOps_mpred)
    (@wp resolve ti r e K).
Proof. red. intros. reflexivity. Qed.
Global Instance : forall P, Proper (@lentails mpred _ --> Basics.flip Basics.impl) (@lentails mpred _ P).
Proof. red. red. red. red. intros. etransitivity; [ eapply H0 | eapply H ]. Qed.


Global Instance : Proper (lentails ==> Basics.flip lentails ==> Basics.flip lentails) (@wandSP mpred _).
Proof. red. red. red. red. unfold Basics.flip. intros.
       rewrite H. rewrite H0. reflexivity.
Qed.
Global Instance : forall P, Proper (Basics.flip lentails ==> Basics.flip lentails) (@wandSP mpred _ P).
Proof. red. red. red. unfold Basics.flip. intros.
       rewrite H. reflexivity.
Qed.
Global Instance lforall_ok : Proper (pointwise_relation val (Basics.flip lentails) ==> Basics.flip lentails) (@lforall mpred _ _).
Proof. red. red. red. intros.
       eapply lforall_lentails_m. apply H.
Qed.

Declare Reduction red_wpe :=
  cbn beta iota zeta delta [
        drop_qualifiers erase_qualifiers
        wp_args wp_block wp_decls wpAny wpe wp_initialize
        Qmut Qconst T_int
        is_aggregate is_pointer type_of
        k_normal k_break k_return k_continue
        Kloop Kseq Kfree Kat_exit val_return void_return
        init_path init_type init_init Wp.SP
        not_mine destructor_for ].

Declare Reduction red_wpe_n :=
  cbv beta iota zeta delta [ Wp.SP ].

Remove Hints Equivalence_Symmetric Equivalence_PER SepAlg.sa_type : typeclass_instances.
Global Instance : Params (@sepSP) 2.
Global Instance : Params (@land) 2.
Global Instance : Params (@lor) 2.
Global Instance : Params (@wandSP) 2.
Global Instance : Params (@empSP) 0.
Global Instance : Params (@ltrue) 0.
Global Instance : Params (@lfalse) 0.


Ltac simplify_all :=
  rewrite_strat (topdown (hints wp_all; eval red_wpe_n; eval red_wpe)).

Ltac simplify_one :=
  rewrite_strat (outermost (hints wp_all; eval red_wpe_n; eval red_wpe)).

(*
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Local Open Scope string_scope.

Goal forall resolve ti r Q,
    |-- wp_lval (resolve:=resolve) ti r
        (Eassign
           (Ederef
              (Ecast (CCcast Cl2r)
                     (Lvalue, Eassign
                                (Evar
                                   (Lname  "x")
                                   (Qmut
                                      (Tpointer
                                         (Qmut T_int))))
                                (Eaddrof
                                   (Evar
                                      (Lname  "y")
                                      (Qmut T_int))
                                   (Qmut
                                      (Tpointer
                                         (Qmut T_int))))
                                (Qmut
                                   (Tpointer
                                      (Qmut T_int))))
                     (Qmut
                        (Tpointer
                           (Qmut T_int))))
              (Qmut T_int))
           (Eint 3
                 (Qmut T_int))
           (Qmut T_int))%Z Q.
Proof.
  intros.
  Time simplify_all.
Abort.
*)
