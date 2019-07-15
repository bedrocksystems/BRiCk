(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

Section discharge.

  Context {L : Type}.

  Context {ILogicOps_L : ILogicOps L}.
  Context {ILogic_L : ILogic L}.

  Context {BILogicOps_L : BILogicOps L}.
  Context {BILogic_L : BILogic L}.

  Context {EmbedOp_Prop_L : EmbedOp Prop L}.
  Context {Embed_Prop_L : Embed Prop L}.

  (* Context {ILLOperators_L : ILLOperators L}. *)
  (* Context {ILLater_L : ILLater L}. *)

  Definition only_provable (P : Prop) : L := embed P //\\ empSP.
  Notation "'[|'  P  '|]'" := (only_provable P).

  Lemma only_provable_only : forall P (Q : Prop),
      Q ->
      P |-- empSP ->
      P |-- [| Q |].
  Proof.
    intros.
    unfold only_provable.
    apply landR; auto.
    eapply embedPropR. auto.
  Qed.

  Lemma provable_star : forall P (Q : Prop) R,
      Q ->
      P |-- R ->
      P |-- [| Q |] ** R.
  Proof.
    intros.
    unfold only_provable.
    rewrite <- empSPL.
    eapply scME; auto.
    apply landR; auto.
    eapply embedPropR. auto.
  Qed.

  Lemma provable_intro : forall (P : Prop) Q R,
      (P -> Q |-- R) ->
      [| P |] ** Q |-- R.
  Proof.
    intros.
    unfold only_provable.
    rewrite embedPropExists.
    rewrite landexistsDL1.
    rewrite bilexistsscL2.
    apply lexistsL. intros.
    rewrite <- H; auto.
    rewrite <- (empSPL Q) at 2.
    eapply scME; eauto.
    eapply landL2. reflexivity.
  Qed.


  Local Lemma focus_ll : forall a b c d : L,
      a ** (b ** c) |-- d ->
      (a ** b) ** c |-- d.
  Proof. intros. rewrite <- H.
         rewrite sepSPA. reflexivity.
  Qed.
  Local Lemma focus_lr : forall a b c d : L,
      b ** (a ** c) |-- d ->
      (a ** b) ** c |-- d.
  Proof. intros. rewrite <- H.
         rewrite <- (sepSPC b a).
         rewrite sepSPA. reflexivity.
  Qed.
  Local Lemma drop_emp : forall a b,
      a |-- b -> empSP ** a |-- b.
  Proof.
    intros. rewrite empSPL. assumption.
  Qed.
  Local Lemma focus_lswap : forall a b c : L,
      a ** c |-- b ->
      c ** a |-- b.
  Proof. intros. rewrite <- H.
         rewrite sepSPC.
         reflexivity.
  Qed.

  Local Lemma focus_lift_embed_l : forall a b c (P : Prop),
      (P -> a ** b |-- c) ->
      (embed P //\\ a) ** b |-- c.
  Proof.
    intros.
    rewrite <- embedPropExists'.
    rewrite landexistsDL1.
    rewrite bilexistsscL2.
    eapply lexistsL.
    intros.
    eapply H in x.
    rewrite <- x.
    rewrite landtrueL.
    reflexivity.
  Qed.
  Local Lemma focus_lift_embed_r : forall a b c (P : Prop),
      (P -> a ** b |-- c) ->
      (a //\\ embed P) ** b |-- c.
  Proof.
    intros.
    rewrite <- embedPropExists'.
    rewrite landexistsDL2.
    rewrite bilexistsscL2.
    eapply lexistsL.
    intros.
    eapply H in x.
    rewrite <- x.
    rewrite landtrueR.
    reflexivity.
  Qed.


  Local Lemma focus_lstart : forall a b : L,
      a ** empSP |-- b ->
      a |-- b.
  Proof. intros. rewrite <- H. rewrite empSPR. reflexivity. Qed.

  Ltac perm_left tac :=
    let rec perm :=
        lazymatch goal with
        | |- (embed _ //\\ _) ** _ |-- _ =>
          simple eapply focus_lift_embed_l; intro
        | |- (_ //\\ embed _) ** _ |-- _ =>
          simple eapply focus_lift_embed_r; intro
        | |- empSP ** _ |-- _ =>
          simple eapply drop_emp
        | |- (?A ** ?B) ** ?C |-- _ =>
          first [ simple eapply focus_ll ; perm
                | simple eapply focus_lr ; perm  ]
        | |- _ => tac
        end
    in
    lazymatch goal with
    | |- _ ** _ |-- _ =>
      first [ perm
            | simple eapply focus_lswap ; perm ]
    | |- empSP |-- _ => fail
    | |- _ |-- _ =>
      simple eapply focus_lstart; tac
    end.

  Local Lemma focus_rl : forall a b c d : L,
      d |-- a ** (b ** c) ->
      d |-- (a ** b) ** c.
  Proof. intros. rewrite H. rewrite sepSPA. reflexivity. Qed.
  Local Lemma focus_rr : forall a b c d : L,
      d |-- b ** (a ** c) ->
      d |-- (a ** b) ** c.
  Proof. intros. rewrite H. rewrite (sepSPC a b).
         rewrite sepSPA. reflexivity.
  Qed.
  Local Lemma focus_rswap : forall a b c : L,
      b |-- c ** a ->
      b |-- a ** c.
  Proof. intros. rewrite H. rewrite sepSPC. reflexivity. Qed.
  Local Lemma focus_rstart : forall a b : L,
      b |-- a ** empSP ->
      b |-- a.
  Proof. intros. rewrite H. rewrite empSPR. reflexivity. Qed.
  Local Lemma drop_emp_r : forall a b,
      a |-- b -> a |-- empSP ** b.
  Proof. intros. rewrite empSPL. assumption. Qed.

  Ltac perm_right tac :=
    let rec perm :=
        lazymatch goal with
        | |- _ |-- empSP ** _ =>
          simple eapply drop_emp_r
        | |- _ |-- (?A ** ?B) ** ?C =>
          first [ simple eapply focus_rl ; perm
                | simple eapply focus_rr ; perm  ]
        | |- _ => tac
        end
    in
    lazymatch goal with
    | |- _ |-- _ ** _ =>
      first [ perm
            | simple eapply focus_rswap; perm ]
    | |- _ |-- empSP => fail
    | |- _ |-- _ =>
      simple eapply focus_rstart; tac
    end.


  Local Lemma sep_cancel : forall a b c,
      b |-- c ->
      a ** b |-- a ** c.
  Proof. intros; eapply scME; auto. Qed.

  (** `cancel` tries to remove common spacial conjuncts from both sides
   *  of an entailment
   *)
  Ltac cancel tac :=
    let try_remove := idtac;
                      lazymatch goal with
                      | |- ?B ** _ |-- ?X ** _ =>
                        first [ is_evar X ; fail 1
                              | tac ]
                      | |- ?X => idtac "goal didn't match" X
                      end
    in
    let protect :=
        idtac;
        lazymatch goal with
        | |- _ |-- ?X ** _ =>
          tryif is_evar X then fail else perm_left try_remove
        end
    in
    repeat (perm_right protect);
    try reflexivity;
    lazymatch goal with
    | |- _ |-- ltrue => simple eapply ltrueR
    | _ => idtac
    end.

  (* some test cases *)
  Goal forall a b c d, a ** b ** d ** c |-- (b ** a ** c) ** d.
  Proof.
    intros.
    cancel ltac:(eapply sep_cancel).
  Qed.

  Goal forall a b c d, exists y, a ** b ** d ** c |-- b ** y.
  Proof.
    intros. eexists.
    cancel ltac:(eapply sep_cancel).
  Qed.

  Goal forall a b c d, exists y, a ** b ** d ** c |-- y ** b.
  Proof.
    intros. eexists.
    cancel ltac:(eapply sep_cancel).
  Qed.

  Local Lemma sep_lexistsR1 : forall P T (Q : T -> L) R x,
      P |-- Q x ** R ->
      P |-- (Exists x : T, Q x) ** R.
  Proof.
    intros. rewrite H.
    rewrite <- bilexistsscR2.
    eapply lexistsR. reflexivity.
  Qed.
  Local Lemma sep_lexistsL1 : forall P T (Q : T -> L) R,
      (forall x, Q x ** R |-- P) ->
      (Exists x : T, Q x) ** R |-- P.
  Proof.
    intros. rewrite bilexistsscL2.
    eapply lexistsL. auto.
  Qed.

  Lemma limplPropR : forall (P : Prop) (a b : L),
      (P -> a |-- b) ->
      a |-- embed P -->> b.
  Proof.
    intros. eapply limplAdj.
    rewrite <- embedPropExists'.
    rewrite landexistsDL2.
    apply lexistsL.
    intros.
    rewrite landtrueR.
    auto.
  Qed.

  Lemma wandSP_app : forall P Q,
      empSP |-- P ->
      P -* Q |-- Q.
  Proof.
    intros.
    rewrite <- H.
    rewrite <- (empSPL (empSP -* Q)).
    eapply sepSPAdj'.
    reflexivity.
  Qed.

  Lemma wandSP_cancel : forall P Q R F,
      R |-- P ** F ->
      (P -* Q) ** R |-- Q ** F.
  Proof.
    intros.
    rewrite H; clear H.
    rewrite <- sepSPA.
    eapply scME; [ | reflexivity ].
    rewrite sepSPC.
    eapply sepSPAdj'.
    reflexivity.
  Qed.

  Lemma use_universal_arrow : forall {T} P Q F F' x,
      F |-- P x ** F' ->
      (Forall res : T, P res -* Q res) ** F |-- Q x ** F'.
  Proof.
    intros.
    rewrite sepSPC. rewrite bilforallscR.
    eapply (lforallL x).
    rewrite H.
    cancel ltac:(eapply sep_cancel).
    eapply sepSPAdj'. reflexivity.
  Qed.


  Lemma use_forall_unused : forall t : Type, t -> forall P, (Forall x : t, P) |-- P.
  Proof.
    intros; eapply lforallL. assumption. reflexivity.
  Qed.

  Lemma emp_wand_fwd : forall P Q R,
      P ** Q |-- R ->
      (empSP -* P) ** Q |-- R.
  Proof.
    intros. rewrite <- H.
    eapply scME; eauto.
    rewrite <- empSPR. eapply sepSPAdj. reflexivity.
  Qed.

  Lemma emp_wand_bwd : forall P Q R,
      Q |-- P ** R ->
      Q |-- (empSP -* P) ** R.
  Proof.
    intros.
    rewrite H. eapply scME; eauto.
    eapply wandSPI. rewrite empSPR. reflexivity.
  Qed.

  Lemma embed_land_l : forall (P : Prop) (Q R : L),
      (P -> Q |-- R) ->
      embed P //\\ Q |-- R.
  Proof. intros.
         rewrite embedPropExists.
         rewrite landexistsDL1.
         eapply lexistsL; intros.
         rewrite <- H; eauto.
         eapply landL2. reflexivity.
  Qed.

  Lemma embed_land_r : forall (P : Prop) (Q R : L),
      (P -> Q |-- R) ->
      Q //\\ embed P |-- R.
  Proof. intros.
         rewrite embedPropExists.
         rewrite landexistsDL2.
         eapply lexistsL; intros.
         rewrite <- H; eauto.
         eapply landL1. reflexivity.
  Qed.

End discharge.

(** `perm_left tac` runs on goals of the form `P |-- Q`
 *  it permutes `P` converting it into `A ** (...)` where
 *  A is "atomic" and runs `tac`. If `tac` fails, then the
 *  permutation continues.
 *  - no guarantee is given for the associativity or commutativity
 *    of the remaining conjuncts if the tactic succeeds
 *)
Ltac perm_left tac :=
  let rec perm :=
      lazymatch goal with
      | |- (embed _ //\\ _) ** _ |-- _ =>
        simple eapply focus_lift_embed_l; intro
      | |- (_ //\\ embed _) ** _ |-- _ =>
        simple eapply focus_lift_embed_r; intro
      | |- empSP ** _ |-- _ =>
        simple eapply drop_emp
      | |- (?A ** ?B) ** ?C |-- _ =>
        first [ simple eapply focus_ll ; perm
              | simple eapply focus_lr ; perm  ]
      | |- _ => tac
      end
  in
  lazymatch goal with
  | |- _ ** _ |-- _ =>
    first [ perm
          | simple eapply focus_lswap ; perm ]
  | |- empSP |-- _ => fail
  | |- _ |-- _ =>
    simple eapply focus_lstart; tac
  end.


Ltac perm_right tac := idtac;
  let rec perm :=
      lazymatch goal with
      | |- _ |-- empSP ** _ =>
        simple eapply drop_emp_r
      | |- _ |-- (?A ** ?B) ** ?C =>
        first [ simple eapply focus_rl ; perm
              | simple eapply focus_rr ; perm  ]
      | |- _ => tac
      end
  in
  lazymatch goal with
  | |- _ |-- _ ** _ =>
    first [ perm
          | simple eapply focus_rswap; perm ]
  | |- _ |-- empSP => fail
  | |- _ |-- _ =>
    simple eapply focus_rstart; tac
  end.

Ltac canceler ctac tac := idtac;
  lazymatch goal with
  | |- _ |-- ?X ** _ =>
    tryif is_evar X
    then fail
    else first [ ctac
               | eapply sep_cancel
               (* note(gmm): we shouldn't try to prove things like this during
                * cancellation because if `tac` takes a long time, then we will
                * try to prove the same thing multiple times.
                *)
               | simple eapply provable_star; [ solve [ tac ] | ] ]
  end.


(** `cancel` tries to remove common spacial conjuncts from both sides
 *  of an entailment
 *)
Ltac cancel ctac tac :=
  idtac;
  repeat (perm_right ltac:(idtac; lazymatch goal with
                                  | |- _ |-- ltrue ** _ => fail
                                    (* ^ this prevents canceling an `ltrue` *)
                                  | |- _ |-- only_provable _ ** _ =>
                                    simple eapply provable_star; [ solve [ tac ] | ]
                                  | |- _ |-- ?X ** _ =>
                                    tryif is_evar X then fail
                                    else perm_left ltac:(idtac; ctac)
                                  end));
  try reflexivity;
  lazymatch goal with
  | |- _ |-- ltrue => simple eapply ltrueR
  | _ => idtac
  end.

Module tests.
Section with_L.
  Context {L : Type}.

  Context {ILogicOps_L : ILogicOps L}.
  Context {ILogic_L : ILogic L}.

  Context {BILogicOps_L : BILogicOps L}.
  Context {BILogic_L : BILogic L}.

  Context {EmbedOp_Prop_L : EmbedOp Prop L}.
  Context {Embed_Prop_L : Embed Prop L}.
  (* some test cases *)
  Goal forall a b c d, a ** b ** d ** c |-- (b ** a ** c) ** d.
  Proof.
    intros.
    cancel ltac:(eapply sep_cancel) eauto.
  Qed.

  Goal forall a b c d, exists y, a ** b ** d ** c |-- b ** y.
  Proof.
    intros. eexists.
    cancel ltac:(eapply sep_cancel) eauto.
  Qed.

  Goal forall a b c d, exists y, a ** b ** d ** c |-- y ** b.
  Proof.
    intros. eexists.
    cancel ltac:(eapply sep_cancel) eauto.
  Qed.

  Goal forall a b c d, exists y, a ** b ** d ** c |-- y.
  Proof.
    intros. eexists.
    cancel ltac:(eapply sep_cancel) eauto.
  Qed.

(*
  Axiom N : nat -> L.

  Fixpoint each (n : nat) : L :=
    match n with
    | 0 => empSP
    | S n => N n ** each n
    end.
  Fixpoint each' (n : nat) : L :=
    match n with
    | 0 => empSP
    | S n => each' n ** N n
    end%list.

  Goal each 100 |-- each' 100.
    simpl.
    Set Ltac Profiling.
    Reset Ltac Profile.
    let tac := fail in
    let ctac := fail in
    cancel ltac:(simple eapply sep_cancel) ltac:(idtac; fail).
    Show Ltac Profile.
  Time Qed.
End perf.
*)
End with_L.
End tests.

(* lift existential quantifiers from the left-hand side *)
Ltac lift_ex_l fwd :=
  repeat (perm_left ltac:(first [ simple eapply provable_intro; intro
                                | lazymatch goal with
                                  | |- (Exists x : _, _) ** _ |-- _ =>
                                    let x' := fresh x in
                                    simple eapply sep_lexistsL1; intro x'
                                  end
                                | simple eapply emp_wand_fwd
                                | fwd ])).

(* lift existential quantifiers from the right-hand side *)
Ltac lift_ex_r bwd := idtac;
  lazymatch goal with
  | |- _ |-- ?X =>
    tryif is_evar X then reflexivity
    else
      (repeat simple eapply lexistsR ;
       repeat (perm_right ltac:(idtac;
                                lazymatch goal with
                                | |- _ |-- (Exists x : ?T, _) ** _ =>
                                  let x' := fresh x in
                                  evar (x' : T);
                                  refine (sep_lexistsR1 _ _ _ _ x' _);
                                  (* ^ note(jmgrosen): I couldn't get eapply to work here. *)
                                  subst x'
                                | |- _ |-- (empSP -* _) ** _ =>
                                  simple eapply emp_wand_bwd
                                | |- _ |-- ?Y ** _ =>
                                  tryif is_evar Y then fail
                                  else bwd
                                end)))
  end.

Ltac solve_pure tac :=
  repeat (perm_right ltac:(simple eapply provable_star; [ solve [ tac ] | ])).

Ltac discharge_fwd fwd fwd_post bwd ctac tac :=
  lift_ex_l fwd; try fwd_post.
Ltac discharge_bwd fwd fwd_post bwd ctac tac :=
  lift_ex_r bwd.
Ltac discharge_cancel fwd fwd_post bwd ctac tac :=
  let ctac' := idtac;
               first [ ctac
                     | eapply use_universal_arrow ]
  in
  cancel ltac:(idtac; canceler ltac:(idtac; ctac') ltac:(idtac; tac)) ltac:(idtac; tac).
Ltac discharge_step kont fwd fwd_post bwd ctac tac :=
  lazymatch goal with
  | |- embed _ //\\ _ |-- _ =>
    simple eapply embed_land_l ; intro; kont
  | |- _ //\\ embed _ |-- _ =>
    simple eapply embed_land_r ; intro; kont
  | |- _ |-- _ //\\ _ =>
    simple eapply landR ; kont
  | |- _ |-- _ -* _ =>
    simple eapply wandSPI ; kont
  | |- _ |-- embed _ =>
    try solve [ simple eapply embedPropR ; tac ]
  | |- _ |-- only_provable _ =>
    try (simple eapply only_provable_only ;
         [ solve [ tac ] | kont ])
  | |- _ |-- (Forall x : _, _) =>
    let x' := fresh x in
    simple eapply lforallR; intro x'; kont
  | |- _ |-- (@embed _ _ _ _) -->> _ =>
    simple eapply limplPropR; intro
  | |- _ => idtac
  end.
Ltac discharge_1 fwd fwd_post bwd ctac tac :=
  discharge_step idtac fwd fwd_post bwd ctac tac.

(* `discharge fwd bwd ctac tac` attempts to solve separation logic goals.
 * - `fwd` simplifies the pre-condition
 * - `fwd_post` runs after forward reasoning
 * - `bwd` simplifies the post-condition
 * - `ctac` is the tactic used for cancellation, a reasonable default is
 *   `canceler fail tac`.
 * - `tac` is the tactic used for solving "pure" propositional assertions.
 *)
Ltac discharge fwd fwd_post bwd ctac tac :=
  let rec discharge :=
      discharge_fwd fwd fwd_post bwd ctac tac ;
      discharge_bwd fwd fwd_post bwd ctac tac ;
      discharge_cancel fwd fwd_post bwd ctac tac ;
      discharge_step discharge fwd fwd_post bwd ctac tac
  in discharge.
