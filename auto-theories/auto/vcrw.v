(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(* Automation for high-level verification conditions *)
From Cpp Require Export Parser Sem.
From Cpp Require Auto.Lemmas Auto.type Auto.vc.

From Cpp.Auto Require Export Discharge Definitions.

Ltac simplify_simpl :=
  try unfold finish;
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
  simpl wpi_init;
  simpl wpis;
  simpl wpds;
  simpl offset_for ;
  simpl wp_block;
  simpl companion_type.

Ltac simplify_wp_rhs e :=
  lazymatch e with
  | Eatomic _ _ _ => rewrite <- wp_rhs_atomic
  | Ebinop _ ?e1 _ _ => rewrite <- wp_rhs_binop; try (simplify_simpl; simplify_wp_rhs e1)
  | Eunop _ ?e _ => rewrite <- wp_rhs_unop; try (simplify_simpl; simplify_wp_rhs e)
  | Ebool _ => rewrite <- wp_rhs_bool
  | Eseqand ?e1 _ _ => rewrite <- wp_rhs_seqand; try (simplify_simpl; simplify_wp_rhs e1)
  | Eseqor ?e1 _ _ => rewrite <- wp_rhs_seqor; simplify_wp_rhs e1
  | Eint _ _ => rewrite <- wp_rhs_int
  | Eaddrof ?e _ => rewrite <- wp_rhs_addrof; simplify_wp_lhs e
  | Ecast (CCcast Cl2r) (Lvalue, Emember ?o _ _) _ => rewrite <- Lemmas.wp_rhs_dot; try (simplify_simpl; simplify_wp_lhs o)
  | Ecast (CCcast Cl2r) (Lvalue, Evar (Lname _) _) _ => rewrite <- Lemmas.wp_rhs_local
  | Ecast (CCcast Cl2r) (Lvalue, ?e) _ => rewrite <- wp_rhs_cast_l2r; try (simplify_simpl; simplify_wp_lhs e)
  | Ecast (CCcast Carray2pointer) (Lvalue, ?e) _ => rewrite <- wp_rhs_cast_array2pointer; try (simplify_simpl; simplify_wp_lhs e)
  | Ecast ?c (Rvalue, ?e) _ =>
    lazymatch c with
    | CCcast Cintegral => rewrite <- wp_rhs_cast_integral
    | CCcast Cint2bool => rewrite <- wp_rhs_cast_int2bool
    | CCcast Cptr2bool => rewrite <- wp_rhs_cast_ptr2bool
    | CCcast Cnull2ptr => rewrite <- wp_rhs_cast_null
    | CCcast Cnoop => rewrite <- Lemmas.wp_rhs_cast_noop
    | CCcast Cbitcast => rewrite <- wp_rhs_cast_bitcast
    | Cuser _ => rewrite <- wp_rhs_cast_user
    | Creinterpret _ => rewrite <- wp_rhs_cast_reinterpret
    end; simplify_wp_rhs e
  | Enull => rewrite <- wp_null
  | Ethis _ => rewrite <- wp_rhs_this
  | Ealign_of (inl _) _ => rewrite <- wp_rhs_alignof
  | Ealign_of (inr _) _ => rewrite <- wp_rhs_alignof_e
  | Esize_of (inl _) _ => rewrite <- wp_rhs_sizeof
  | Esize_of (inr _) _ => rewrite <- wp_rhs_sizeof_e
  | Epostinc _ _ => rewrite <- wp_rhs_postinc; simpl
  | Epostdec _ _ => rewrite <- wp_rhs_postdec; simpl
  | Eandclean ?e _ => rewrite <- wp_rhs_clean; try (simplify_simpl; simplify_wp_rhs e)
  end

with simplify_wp_lhs e :=
  lazymatch e with
  | Eassign (Emember ?o _ _) _ _ => rewrite <- Lemmas.wp_lhs_assign_member; try (simplify_simpl; simplify_wp_lhs o)
  | Eassign ?l _ _ => rewrite <- wp_lhs_assign; try (simplify_simpl; simplify_wp_lhs l)
  | Eassign_op _ _ _ _ => rewrite <- wp_lhs_bop_assign
  | Evar (Lname _) _ => rewrite <- wp_lhs_lvar
  | Evar (Gname _) _ => rewrite <- wp_lhs_gvar
  | Ederef ?e _ => rewrite <- wp_lhs_deref; simplify_wp_rhs e
  | Ecast (CCcast Cnoop) (Lvalue, ?e) _ => rewrite <- Lemmas.wp_lhs_cast_noop; try (simplify_simpl; simplify_wp_lhs e)
  | Emember ?e _ _ => rewrite <- wp_lhs_member; try (simplify_simpl; simplify_wp_lhs e)
  | Epreinc _ _ => rewrite <- wp_lhs_preinc; simpl
  | Epredec _ _ => rewrite <- wp_lhs_predec; simpl
  | Eif ?e _ _ _ => rewrite <- Lemmas.wp_lhs_condition; try (simplify_simpl; simplify_wp_rhs e)
  | Ematerialize_temp ?e _ => rewrite <- wp_lhs_temp; try (simplify_simpl; simplify_wp_rhs e)
  | Esubscript ?e _ _ => rewrite <- wp_lhs_subscript; try (simplify_simpl; simplify_wp_rhs e)
  end.

Ltac simplify_wpe e :=
  lazymatch e with
  | Ecast (CCcast Cnoop) (_, ?e) _ => rewrite <- wpe_cast_noop; try (simplify_simpl; simplify_wpe e)
  end.

Ltac simplify_wp_ e :=
  lazymatch e with
  | Sseq _ => rewrite <- wp_seq
  | Sreturn (Some (Lvalue, ?e)) => rewrite <- Lemmas.wp_return_lhs; try (simplify_simpl; simplify_wp_lhs e)
  | Sreturn (Some (Rvalue, ?e)) => rewrite <- Lemmas.wp_return_rhs; try (simplify_simpl; simplify_wp_rhs e)
  | Sreturn None => rewrite <- wp_return_void
  | Sexpr _ _ => rewrite <- wp_expr
  | Sif (Some _) _ _ _ => rewrite <- wp_if_decl
  | Sif None ?e _ _ => rewrite <- wp_if; try (simplify_simpl; simplify_wp_rhs e)
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
  | wp_rhs _ _ ?e _ => simplify_wp_rhs e
  | wp_lhs _ _ ?e _ => simplify_wp_lhs e
  | wp_decl _ _ _ ?t _ _ _ => simplify_wp_decl t
  | wpd _ _ _ _ _ _ => rewrite <- wpd_deinit
  | wpi _ _ _ _ _ _ => rewrite <- wpi_initialize
  end.

Ltac simplify_wp :=
  match goal with
  | [ |- _ |-- ?g ] => simplify_wp' g
  end.

Local Ltac find_spec := vc.find_spec.

Ltac simplifying :=
  let with_context := idtac;
      let try_it L := idtac;
          perm_right ltac:(idtac; simple eapply L; [ find_spec | simpl wps ])
      in
      lazymatch goal with
      | |- _ |-- ?R =>
        match R with
        | context [ wp_rhs _ _ (Ecall _ _ _) _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_call_glob;
                           [ exact I | find_spec | simpl wps ])
        | context [ wp_rhs _ _ (Emember_call _ _ _ _ _) _ ] =>
          try_it Lemmas.wp_member_call_glob
        | context [ wp_rhs _ _ (Econstructor _ _ _) _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_constructor_glob;
                           [ find_spec | simpl wps ])
        | context [ wp_decl _ _ _ (Tref _) _ _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_decl_class;
                           [ find_spec | find_spec | simpl wps ])
        | context [ @destroy _ _ _ _ _ _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_destroy;
                           [ find_spec | simpl ])
        | context [ @wp_rhs _ _ _ (Econst_ref _ _) _ ] =>
          perm_right ltac:(idtac; simple eapply Lemmas.wp_rhs_const;
                           [ solve [ perm_left ltac:(idtac; eapply Lemmas.exactly_this_one) ] | reflexivity | ])
        end
      end
  in
  repeat (simplify_simpl;
          first [ progress simplify_wp
                (* calls *)
                | with_context
                ]); simplify_simpl.
