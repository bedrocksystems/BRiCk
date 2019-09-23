(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(* Automation for high-level verification conditions *)
From Cpp Require Export Parser Sem.
From Cpp Require Auto.Lemmas Auto.type.

From Cpp.Auto Require Export Discharge Definitions.

Require Import bedrock.auto.find_spec.

Ltac simplify_simpl :=
  try unfold SP;
  simpl k_return;
  simpl k_continue;
  simpl k_break;
  simpl k_normal;
  unfold wpAny;
  unfold wpAnys;
  unfold wp_dtor ;
  unfold wp_ctor ;
  simpl wpe;
  simpl wps;
  simpl wpis;
  simpl wpds;
  simpl wp_args;
  simpl offset_for ;
  simpl drop_qualifiers;
  simpl erase_qualifiers;
  simpl is_aggregate;
  simpl is_pointer;
  simpl wp_block;
  unfold not_mine; simpl;
  simpl destructor_for;
  simpl companion_type.

Ltac simplify_wp_prval e :=
  lazymatch e with
  | Eatomic _ _ _ => rewrite <- wp_prval_atomic
  | Ebinop _ ?e1 _ _ => rewrite <- wp_prval_binop; continue_prval e1
  | Eunop _ ?e _ => rewrite <- wp_prval_unop; continue_prval e
  | Ebool _ => rewrite <- wp_prval_bool
  | Eseqand ?e1 _ _ => rewrite <- wp_prval_seqand; continue_prval e1
  | Eseqor ?e1 _ _ => rewrite <- wp_prval_seqor; continue_prval e1
  | Eint _ _ => rewrite <- wp_prval_int
  | Eaddrof ?e _ => rewrite <- wp_prval_addrof; continue_lval e
  | Ecast (CCcast C2void) (?L, ?e) _ =>
    rewrite <- Lemmas.wp_prval_cast_tovoid ;
    lazymatch L with
    | Lvalue => continue_lval e
    | Rvalue => continue_prval e
    | Xvalue => continue_xval e
    end
  | Ecast (CCcast Cl2r) (Lvalue, Emember ?o _ _) _ => rewrite <- Lemmas.wp_prval_dot; continue_lval o
  | Ecast (CCcast Cl2r) (Lvalue, Evar (Lname _) _) _ => rewrite <- Lemmas.wp_prval_local
  | Ecast (CCcast Cl2r) (Lvalue, ?e) _ => rewrite <- Lemmas.wp_prval_cast_l2r_l; continue_lval e
  | Ecast (CCcast Cl2r) (Xvalue, ?e) _ => rewrite <- Lemmas.wp_prval_cast_l2r_x; continue_xval e
  | Ecast (CCcast Carray2pointer) (Lvalue, ?e) _ => rewrite <- wp_prval_cast_array2pointer; continue_lval e
  | Ecast ?c (Rvalue, ?e) _ =>
    lazymatch c with
    | CCcast Cintegral => rewrite <- wp_prval_cast_integral
    | CCcast Cint2bool => rewrite <- wp_prval_cast_int2bool
    | CCcast Cptr2bool => rewrite <- wp_prval_cast_ptr2bool
    | CCcast Cnull2ptr => rewrite <- wp_prval_cast_null
    | CCcast Cnoop => rewrite <- wp_prval_cast_noop
    | CCcast Cbitcast => rewrite <- wp_prval_cast_bitcast
    | Cuser _ => rewrite <- wp_prval_cast_user
    | Creinterpret _ => rewrite <- wp_prval_cast_reinterpret
    end; continue_prval e
  | Enull => rewrite <- wp_null
  | Ethis _ => rewrite <- wp_prval_this
  | Ealign_of (inl _) _ => rewrite <- wp_prval_alignof
  | Ealign_of (inr _) _ => rewrite <- wp_prval_alignof_e
  | Esize_of (inl _) _ => rewrite <- wp_prval_sizeof
  | Esize_of (inr _) _ => rewrite <- wp_prval_sizeof_e
  | Epostinc _ _ => rewrite <- wp_prval_postinc; simpl
  | Epostdec _ _ => rewrite <- wp_prval_postdec; simpl
  | Eandclean ?e _ => rewrite <- wp_prval_clean; continue_prval e
  | Ebind_temp ?e _ _ => rewrite <- wp_prval_materialize ; continue_init e
  end

with simplify_wp_xval e :=
  lazymatch e with
  | Eandclean ?e _ => rewrite <- wp_xval_clean ; continue_xval e
  | Ecast (CCcast Cnoop) (Xvalue, ?e) _ => rewrite <- wp_xval_cast_noop; continue_xval e
  | Ecast (CCcast Cnoop) (Lvalue, ?e) _ => rewrite <- wp_xval_lval_cast_noop; continue_lval e
  | Emember ?e _ _ => rewrite <- wp_xval_member ; continue_rval e
  | Ematerialize_temp ?e _ => rewrite <- wp_xval_temp ; simpl destructor_for
  | Esubscript _ _ _ => rewrite <- wp_xval_subscript ; simpl
  end

with simplify_wp_rval e :=
    rewrite <- Lemmas.wp_rval_xval_materialize ; continue_xval e

with simplify_wp_lval e :=
  lazymatch e with
  | Eassign (Emember ?o _ _) _ _ => rewrite <- Lemmas.wp_lval_assign_member; continue_lval o
  | Eassign ?l _ _ => rewrite <- wp_lval_assign; continue_lval l
  | Eassign_op _ _ _ _ => rewrite <- wp_lval_bop_assign
  | Evar (Lname _) _ => rewrite <- wp_lval_lvar
  | Evar (Gname _) _ => rewrite <- wp_lval_gvar
  | Ederef ?e _ => rewrite <- wp_lval_deref; continue_prval e
  | Ecast (CCcast Cnoop) (Lvalue, ?e) _ =>
    rewrite <- wp_lval_cast_noop; continue_lval e
  | Ecast (CCcast Cnoop) (Xvalue, ?e) _ =>
    rewrite <- wp_lval_xval_cast_noop; continue_lval e
  | Emember ?e _ _ => rewrite <- wp_lval_member; continue_lval e
  | Epreinc _ _ => rewrite <- wp_lval_preinc; simpl
  | Epredec _ _ => rewrite <- wp_lval_predec; simpl
  | Eif ?e _ _ _ => rewrite <- Lemmas.wp_lval_condition; continue_prval e
  | Ematerialize_temp ?e _ => rewrite <- wp_lval_temp; continue_prval e
  | Esubscript ?e _ _ => rewrite <- wp_lval_subscript; continue_prval e
  end

with simplify_wp_init e :=
    first [ rewrite <- Lemmas.wp_init_mut
          | rewrite <- wp_init_const
          | rewrite <- Lemmas.wpi_initialize
          | rewrite <- wp_init_clean
          | rewrite <- wp_init_bind_temp ]

with continue_prval e := try (simplify_simpl; simplify_wp_prval e)
with continue_rval e := try (simplify_simpl; simplify_wp_rval e)
with continue_lval e := try (simplify_simpl; simplify_wp_lval e)
with continue_xval e := try (simplify_simpl; simplify_wp_xval e)
with continue_init e := try (simplify_simpl; simplify_wp_init e)
.

(*
Ltac simplify_wpe e :=
  lazymatch e with
  | Ecast (CCcast Cnoop) (_, ?e) _ => rewrite <- wpe_cast_noop; try (simplify_simpl; simplify_wpe e)
  end.
*)

Ltac simplify_wp_ e :=
  lazymatch e with
  | Sseq _ => rewrite <- wp_seq
  | Sreturn (Some (Lvalue, ?e)) => rewrite <- Lemmas.wp_return_lval; continue_lval e
  | Sreturn (Some (Rvalue, ?e)) => rewrite <- Lemmas.wp_return_rval; simpl is_aggregate; continue_prval e
  | Sreturn (Some (Xvalue, ?e)) => rewrite <- Lemmas.wp_return_xval; continue_xval e
  | Sreturn None => rewrite <- wp_return_void
  | Sexpr _ _ => rewrite <- wp_expr
  | Sif (Some _) _ _ _ => rewrite <- wp_if_decl
  | Sif None ?e _ _ => rewrite <- wp_if; try (simplify_simpl; simplify_wp_prval e)
  | Sfor (Some _) _ _ _ => rewrite <- wp_for_init
  | Swhile (Some _) _ _ => rewrite <- wp_while_decl
  | Scontinue => rewrite <- wp_continue
  | Sbreak => rewrite <- wp_break
  | Sskip => rewrite <- Lemmas.wp_skip
  end.

Ltac simplify_wp_decl t :=
  lazymatch t with
  | Qmut ?t => rewrite <- Lemmas.wp_decl_mut; try (simplify_simpl; simplify_wp_decl t)
  | Qconst ?t => rewrite <- Lemmas.wp_decl_const; try (simplify_simpl; simplify_wp_decl t)
  | Tint _ _ => rewrite <- Lemmas.wp_decl_int
  | T_int => rewrite <- Lemmas.wp_decl__int
  | T_int32 => rewrite <- Lemmas.wp_decl__int32
  | T_ulong => rewrite <- Lemmas.wp_decl__ulong
  | Tchar _ _ => rewrite <- Lemmas.wp_decl_char
  | Tpointer _ => rewrite <- Lemmas.wp_decl_pointer
  | Treference _ => rewrite <- Lemmas.wp_decl_reference
  end.


Ltac simplify_wp' g :=
  lazymatch g with
  | ?g1 ** ?g2 => first [ simplify_wp' g1 | simplify_wp' g2 ]
  | ?g1 //\\ ?g2 => first [ simplify_wp' g1 | simplify_wp' g2 ]
  | _ -* ?g => simplify_wp' g
  | lexists (fun _x : _ => ?g) _ => simplify_wp' g
  | lforall (fun _x : _ => ?g) _ => simplify_wp' g
  | wp _ _ ?e _ => simplify_wp_ e
  | wp_prval _ _ ?e _ => simplify_wp_prval e
  | wp_lval _ _ ?e _ => simplify_wp_lval e
  | wp_xval _ _ ?e _ => simplify_wp_xval e
  | wp_rval _ _ ?e _ => simplify_wp_rval e
  | wp_decl _ _ _ ?t _ _ _ _ => simplify_wp_decl t
  | @wp_init _ _ _ _ _ ?e _ => simplify_wp_init e
  | wpd _ _ _ _ _ _ => rewrite <- wpd_deinit
  | wpi _ _ _ _ _ _ => rewrite <- wpi_initialize
  end.

Ltac simplify_wp :=
  match goal with
  | [ |- _ |-- ?g ] => simplify_wp' g
  end.

Local Ltac find_spec := find_spec.find_spec.

Ltac simplifying :=
  let with_context := idtac;
      let try_it L := idtac;
          perm_right ltac:(idtac; simple eapply L; [ find_spec | simpl wps ])
      in
      lazymatch goal with
      | |- _ |-- ?R =>
        match R with
        | context [ wp_prval _ _ (Ecall _ _ _) _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_prval_call_glob;
                           [ exact I | find_spec | simpl wp_args ])
        | context [ wp_xval _ _ (Ecall _ _ _) _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_xval_call_glob;
                           [ exact I | find_spec | simpl wp_args ])
        | context [ wp_prval _ _ (Emember_call _ _ _ _ _) _ ] =>
          try_it Lemmas.wp_prval_member_call_glob
        | context [ wp_xval _ _ (Emember_call _ _ _ _ _) _ ] =>
          try_it Lemmas.wp_xval_member_call_glob
        | context [ wp_init _ _ _ _ (Econstructor _ _ _) _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_init_ctor_glob;
                           [ find_spec | simpl wps ])
        | context [ wp_init _ _ _ _ (Ecall _ _ _) _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_init_call_glob;
                           [ exact I | find_spec | simpl wp_args ])
        | context [ wp_decl _ _ _ (Tref _) _ _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_decl_class_dtor;
                           [ find_spec | find_spec | simpl wp_args ])
        | context [ wp_decl _ _ _ (Tref _) _ _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_decl_class_no_dtor;
                           [ find_spec | simpl wps ])
        | context [ @destruct_obj _ _ _ _ _ _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_destroy;
                           [ find_spec | simpl ])
        | context [ @wp_prval _ _ _ (Econst_ref _ _) _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_prval_const;
                           [ solve [ perm_left ltac:(idtac; eapply Lemmas.exactly_this_one) ] | reflexivity | ])
        end
      end
  in
  repeat (simplify_simpl;
          first [ progress simplify_wp
                (* calls *)
                | with_context
                ]); simplify_simpl.
