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

Hint Resolve Lemmas.wp_rval_dot Lemmas.wp_rval_local Lemmas.wp_lval_assign_member : wp_pre.

Local Ltac t :=
  discharge fail idtac fail fail idtac.

Ltac find_left tac :=
  let rec perm :=
      lazymatch goal with
      | |- (?A ** ?B) ** ?C |-- _ => first
          [ simple eapply Discharge.focus_ll; perm
          | simple eapply Discharge.focus_lr; perm ]
      | |- _ => tac
      end
  in
  lazymatch goal with
  | |- _ ** _ |-- _ => first
    [ perm | simple eapply Discharge.focus_lswap; perm ]
  | |- empSP |-- _ => fail
  | |- _ |-- _ => simple eapply Discharge.focus_lstart; tac
  end.

(* this tactic solves goals of the form
 *
 *   F |-- |> cglob' f ti s ** ltrue
 *
 * which arise from various forms of calls.
 *)
Ltac find_spec :=
  let try_this_one :=
      first [ simple eapply Lemmas.cglob_by_cglob_gen;
              solve [ reflexivity
                    | eapply (@Lemmas.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ]
            | simple eapply Lemmas.cglob_by_ti_cglob_gen;
              solve [ reflexivity
                    | eapply (@Lemmas.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ]
            | simple eapply Lemmas.cglob_by_later_cglob_gen;
              solve [ reflexivity
                    | eapply (@Lemmas.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ]
            | simple eapply Lemmas.cglob_by_later_ti_cglob_gen;
              solve [ reflexivity
                    | eapply (@Lemmas.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ]
            | simple eapply Lemmas.cglob_by_make_signature_ti_gen;
              [ reflexivity
              | solve [ reflexivity
                      | eapply (@Lemmas.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ] ]
            | simple eapply Lemmas.cglob_by_later_make_signature_ti_gen;
              [ reflexivity
              | solve [ reflexivity
                      | eapply (@Lemmas.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ] ]
            ]
  in
  solve [ find_left try_this_one ].

Require Import LtacIter.LtacIter.

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
     @wp_rval_atomic

     @wp_rval_binop
     @wp_rval_unop
     @wp_rval_bool
     @wp_lval_assign
     @wp_lval_bop_assign
     @wp_lval_lvar
     @wp_lval_gvar
     @wp_rval_seqand
     @wp_rval_seqor
     @wp_rval_int
     @wp_lval_deref
     @wp_rval_addrof
     Lemmas.wp_rval_cast_l2r
     @wp_rval_cast_integral
     @wp_rval_cast_int2bool
     @wp_rval_cast_ptr2bool
     @wp_rval_cast_null
     @wpe_cast_noop
     Lemmas.wp_rval_cast_noop
     Lemmas.wp_lval_cast_noop
     @wp_rval_cast_bitcast
     @wp_rval_cast_array2pointer
     @wp_null
     @wp_lval_member
     @wp_rval_this
     @wp_rval_alignof
     @wp_rval_alignof_e
     @wp_rval_sizeof
     @wp_rval_sizeof_e
     @wp_rval_postinc
     @wp_rval_postdec
     @wp_lval_preinc
     @wp_lval_predec
     Lemmas.wp_lval_condition
     Lemmas.wp_rval_condition
     @wp_rval_cast_user
     @wp_rval_cast_reinterpret
     @wp_rval_clean
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

Declare Reduction red_wpe :=
  cbn beta iota zeta delta [ drop_qualifiers wp_args wp_block Qmut Qconst T_char T_int is_aggregate type_of k_normal k_break k_return k_continue Kloop Kseq Kfree Kat_exit val_return void_return wpe init_path init_type init_init wp_decls wpAny ].

Declare Reduction red_SP :=
  cbv beta iota zeta delta [ SP ].

Ltac simplifying :=
  rewrite_strat (topdown (hints wp_all; eval red_SP; eval red_wpe)).


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
  Time simplifying.
Abort.
*)
