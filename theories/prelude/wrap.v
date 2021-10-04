(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.countable.
From bedrock.prelude Require Import numbers.

(* a generic wrapper for types isomorphic to N *)
Record WrapN {Phant : Set} : Set := { unwrapN : N }.
Arguments WrapN Phant : clear implicits.
(* using the wrapper means we define these instances only once. *)

Lemma cancel_unwrapN {Phant} (x : WrapN Phant) :
  {| unwrapN := unwrapN x |} = x.
Proof. by case: x. Qed.

(* this instance is useful in combination with [Refine1_Cancel]. *)
#[global] Instance cancel_Build_WrapN_unwrapN {Phant} :
  Cancel eq (Build_WrapN Phant) unwrapN.
Proof. exact cancel_unwrapN. Qed.

#[global] Instance wrapN_eq_decision {Phant} : EqDecision (WrapN Phant).
Proof. solve_decision. Defined.

#[global] Instance wrapN_countable {Phant} : Countable (WrapN Phant) :=
  inj_countable' unwrapN (Build_WrapN _) (cancel _ _).

#[global] Instance wrapN_inhabited {Phant} : Inhabited (WrapN Phant) :=
  populate {| unwrapN := 0 |}.

#[global] Instance unwrapN_inj Phant : Inj eq eq (@unwrapN Phant).
Proof. intros [] [] ?. by simplify_eq/=. Qed.

#[global] Instance Build_WrapN_inj Phant : Inj eq eq (Build_WrapN Phant).
Proof. by intros ?? [=]. Qed.

#[global] Declare Scope wrapN_scope.
#[global] Delimit Scope wrapN_scope with wrapN.
(* ^ it would be nicer to have one delimiting key per instantiation of WrapN,
    but that doesn't seem possible? *)
#[global] Bind Scope wrapN_scope with WrapN.

Module wrapN_notations.
  Class WrapNAdd {T U R : Set} := wrapN_add : T -> U -> R.
  Instance wrapNN_add {Phant} : @WrapNAdd (WrapN Phant) N (WrapN Phant) :=
    fun w n => Build_WrapN Phant (unwrapN w + n).
  Instance NwrapN_add {Phant} : @WrapNAdd N (WrapN Phant) (WrapN Phant) :=
    fun n w => Build_WrapN Phant (unwrapN w + n).
  Instance wrapNwrapN_add {Phant} : @WrapNAdd (WrapN Phant) (WrapN Phant) (WrapN Phant) :=
    fun w1 w2 => Build_WrapN Phant (unwrapN w1 + unwrapN w2).
  Notation "0" := (Build_WrapN _ 0) (only parsing) : wrapN_scope.
  Infix "+" := wrapN_add (only parsing) : wrapN_scope.
End wrapN_notations.

Import wrapN_notations.

Section seqW.
  Context {Phant : Set}.
  Implicit Types (w : WrapN Phant).
  #[local] Open Scope wrapN_scope.

  Lemma wrapN_add_0N_r w : w + 0%N = w.
  Proof. by rewrite /wrapN_add /wrapNN_add N.add_0_r cancel_unwrapN. Qed.
  Lemma wrapN_add_0w_r w : w + 0 = w.
  Proof. by rewrite /wrapN_add /wrapNwrapN_add N.add_0_r cancel_unwrapN. Qed.

  Definition wrapN_succ w : WrapN Phant :=
    Build_WrapN _ $ N.succ $ unwrapN w.

  Lemma unwrapN_succ_inj w : unwrapN (wrapN_succ w) = N.succ (unwrapN w).
  Proof. done. Qed.

  Definition seqW w (sz : N) : list (WrapN Phant) :=
    Build_WrapN _ <$> seqN (unwrapN w) sz.

  Lemma cons_seqW len start :
    start :: seqW (wrapN_succ start) len = seqW start (N.succ len).
  Proof. by rewrite /seqW -cons_seqN fmap_cons cancel_unwrapN. Qed.

  (* Lifts [seqN_S_end_app] *)
  Lemma seqW_S_end_app w n : seqW w (N.succ n) = seqW w n ++ [w + n].
  Proof. by rewrite /seqW seqN_S_end_app fmap_app. Qed.

  Lemma cons_seqW' [len start] sstart :
    sstart = wrapN_succ start ->
    start :: seqW sstart len = seqW start (N.succ len).
  Proof. move->. apply cons_seqW. Qed.

  Lemma seqW_S_end_app' [w n] sn :
    sn = N.succ n ->
    seqW w sn = seqW w n ++ [w + n].
  Proof. move->. apply seqW_S_end_app. Qed.
End seqW.

Module Type wrapper.
  Variant Phant := Build_Phant.

  Definition t := WrapN Phant.
  #[global] Bind Scope wrapN_scope with t.

  Definition of_N : N -> t := Build_WrapN Phant.
  Definition to_N : t -> N := unwrapN.
  Lemma of_to_N x : of_N (to_N x) = x.
  Proof. apply cancel_unwrapN. Qed.
End wrapper.

Module Type succ_wrapper (Import W : wrapper).
  Notation succ := (wrapN_succ (Phant := Phant) : t -> t) (only parsing).
  Notation seqW := (seqW (Phant := Phant) : (t -> N -> list t)) (only parsing).
End succ_wrapper.
