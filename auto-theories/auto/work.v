(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(* Automation for code *)
Require Import Coq.micromega.Lia.

Require Import LtacIter.LtacIter.

From Cpp Require Import Parser Sem.
From Cpp.Auto Require Lemmas type.

From Cpp.Auto Require Import Discharge Definitions.
From bedrock.auto.Lemmas Require
     Eval Functions PLogic Util Wp.

(* we are working in a fairly rich separation logic, however, the fragment that
 * shows up in practice is relatively small.
 *)
Create HintDb wp_pre discriminated.

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
      first [ simple eapply auto.Lemmas.Functions.cglob'_by_cglob'_gen;
              solve [ reflexivity
                    | eapply (@Lemmas.Functions.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ]
            | simple eapply Lemmas.Functions.cglob'_by_ti_cglob'_gen;
              solve [ reflexivity
                    | eapply (@Lemmas.Functions.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ]
            | simple eapply Lemmas.Functions.cglob'_by_later_cglob'_gen;
              solve [ reflexivity
                    | eapply (@Lemmas.Functions.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ]
            | simple eapply Lemmas.Functions.cglob'_by_later_ti_cglob'_gen;
              solve [ reflexivity
                    | eapply (@Lemmas.Functions.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ]
            ]
  in
  solve [ find_left try_this_one ].

Require Import LtacIter.LtacIter.

Create HintDb size_of discriminated.
Hint Resolve size_of_int size_of_char size_of_bool size_of_pointer : size_of.

Ltac size_of :=
  try subst;
  first [ eapply size_of_int
        | eapply size_of_char
        | eapply size_of_bool
        | eapply size_of_pointer

        | solve [ eauto with size_of ]
        ].

Create HintDb learning.
Hint Resolve Lemmas.PLogic.learn_bounds_at_tuint
             Lemmas.Util.only_provable_intro_mpred : learning.

Ltac learn_here :=
  idtac;
  let go l := (eapply l; try solve [ eauto with typeclass_instances ]; [ Discharge.learn ]) in
  first [ eapply refine_tprim_ptr;
              lazymatch goal with
              | |- forall x, Vptr x = Vptr _ -> _ => fail
              | |- _ => let H := fresh in intros ? H; destruct H
              end
        | lazymatch goal with
          | |- _at _ (tprim (Tint _ _) ?v) ** _ |-- _ =>
            lazymatch v with
            | Vint _ => simple apply Lemmas.PLogic.learn_bounds_at_int_Vint; Discharge.learn
            | _ => simple apply Lemmas.PLogic.learn_bounds_at_int_val; do 2 intro; try subst v; Discharge.learn
            end
          | |- tlocal_at _ _ _ (tprim (Tint _ _) ?v) ** _ |-- _ =>
            lazymatch v with
            | Vint _ => simple apply Lemmas.PLogic.learn_bounds_tlocal_at_Vint; Discharge.learn
            | _ => simple apply Lemmas.PLogic.learn_bounds_tlocal_at_val; do 2 intro; try subst v; intro; Discharge.learn
            end
          | |- tlocal _ _ (tprim (Tint _ _) ?v) ** _ |-- _ =>
            lazymatch v with
            | Vint _ => simple apply Lemmas.PLogic.learn_bounds_tlocal_Vint; Discharge.learn
            | _ => simple apply Lemmas.PLogic.learn_bounds_tlocal_val; do 3 intro; try subst v; Discharge.learn
            end
          end
        | first_of [ db:learning ] go
        | simple eapply Lemmas.PLogic.tlocal_at_tlocal_fwd; intro
        | simple eapply Lemmas.PLogic._at_offsetR_fwd
        | simple eapply Lemmas.PLogic._at_sepSP_fwd
        | simple eapply Lemmas.PLogic._at_empSP_fwd
        | simple eapply Lemmas.PLogic._at_lexists_fwd
        | simple eapply Lemmas.PLogic._at_pureR_fwd
        | simple eapply Lemmas.PLogic._at_is_null_fwd
        | simple eapply Lemmas.PLogic._at_is_nonnull_fwd
        | simple eapply Lemmas.PLogic._at_eq_tref_fwd
        | eapply Lemmas.PLogic.uninit_class_fwd ;
          [ solve [ find_left ltac:(eapply Lemmas.Util.exactly_this_one) ] | reflexivity | simpl ]
        | lazymatch goal with
          | |- _at (_eq _) _ ** _ |-- _ => fail
          | |- _ => simple eapply Lemmas.PLogic._at_eq_fwd; intros
          end
        ].

Ltac learn :=
  idtac;
  repeat perm_left learn_here; repeat Auto.type.learn.

Create HintDb rep.
Hint Resolve tprim_tptr tprim_tint tprim_tuint tprim_any tptr_any tint_any tuint_any : rep.

Ltac work_fwd := idtac; learn_here.

Ltac work_bwd :=
  idtac;
  lazymatch goal with
  | |- _ |-- ?X ** _ =>
    tryif is_evar X
    then fail
    else
      first [ simple eapply Lemmas.PLogic._at_sepSP_bwd
            | simple eapply Lemmas.PLogic._at_empSP_bwd
            | simple eapply Lemmas.PLogic._at_lexists_bwd
            | simple eapply Lemmas.PLogic._at_pureR_bwd
            | simple eapply Lemmas.PLogic._at_offsetR_bwd
            | simple eapply Lemmas.PLogic._at_is_null_bwd
            | simple eapply Lemmas.PLogic._at_is_nonnull_bwd
            | simple eapply Lemmas.PLogic._at_eq_tref_bwd
            | simple eapply Lemmas.PLogic.tany_class_bwd ;
              [ solve [ find_left ltac:(eapply Lemmas.Util.exactly_this_one) ] | reflexivity | simpl ]
            | lazymatch goal with
              | |- _ |-- _at (_eq _) _ ** _ => fail
              | |- _ => simple eapply Lemmas.PLogic._at_eq_bwd; eexists
              end
            ]
  end.

Ltac work_tac :=
  idtac;
  try lazymatch goal with
      | |- @eq val _ _ => f_equal
      end ;
  lazymatch goal with
  | |- ?A = ?B =>
    solve [ reflexivity
          | lia ]
  | |- ?X =>
    tryif has_evar X then fail
    else solve [ eauto with has_type
               | reflexivity
               | Auto.type.has_type
               | size_of
               | lia ]
  end.

Ltac work_rep_tac :=
  solve [ reflexivity
        | first_of [ db:rep ] ltac:(fun l => eapply l)
        ].

Ltac work_ctac :=
  idtac;
  lazymatch goal with
  | |- ?Y ** _ |-- ?X ** _ =>
    tryif is_evar X
    then fail
    else first [ lazymatch goal with
                 | |- _ |-- _at ?X _ ** _ =>
                   tryif has_evar X then fail 1
                   else first [ eapply _at_cancel; [ solve [ work_rep_tac ] | ]
                              | simple eapply Lemmas.PLogic.tlocal_at__at; [ solve [ work_rep_tac ] | ]
                              ]
                 | |- _ |-- _local _ ?X &~ _ ** _ =>
                   tryif has_evar X then fail 1
                   else first [ simple eapply Lemmas.PLogic.tlocal_at__local ]
                 end
               | simple eapply tlocal_at_tlocal; [ solve [ work_rep_tac ] | ]
               | simple eapply tlocal_at_tlocal_at; [ solve [ work_rep_tac ] | ]
               | simple eapply Lemmas.PLogic._local_tlocal
               | simple eapply Lemmas.PLogic._local_tlocal_at
               | simple eapply Lemmas.Functions.ti_cglob'_cglob'_cancel
               | simple eapply Lemmas.Functions.ti_cglob'_later_cglob'_cancel
               | simple eapply Lemmas.Util.cancel_with_later
               | lazymatch goal with
                 | |- @lforall _ _ _ _ ** _ |-- _ =>
                   first [ eapply Lemmas.Util.appeal_to_universal_arrow
                         | eapply Lemmas.Util.appeal_to_universal_arrow_void ];
                   [ Discharge.lift_ex_r work_bwd ]
                 end
               ]
  end.

Ltac work :=
  discharge ltac:(work_fwd) ltac:(repeat Auto.type.learn) ltac:(work_bwd) ltac:(work_ctac) ltac:(work_tac).