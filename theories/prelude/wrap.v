(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.countable.

(* a generic wrapper for types isomorphic to N *)
Record WrapN {Phant : Set} : Set := { unwrapN : N }.
Arguments WrapN Phant : clear implicits.
(* using the wrapper means we define these instances only once. *)

(* this instance is useful in combination with [Refine1_Cancel]. *)
#[global] Instance cancel_Build_WrapN_unwrapN {Phant} :
  Cancel eq (Build_WrapN Phant) unwrapN.
Proof. by intros []. Qed.

#[global] Instance wrapN_eq_decision {Phant} : EqDecision (WrapN Phant).
Proof. solve_decision. Defined.

#[global] Instance wrapN_countable {Phant} : Countable (WrapN Phant) :=
  inj_countable' unwrapN (Build_WrapN _) (cancel _ _).

#[global] Instance wrapN_inhabited {Phant} : Inhabited (WrapN Phant) :=
  populate {| unwrapN := 0 |}.

#[global] Instance unwrapN_inj Phant : Inj eq eq (@unwrapN Phant).
Proof. intros [] [] ?. by simplify_eq/=. Qed.


Module wrapN_notations.
  Declare Scope wrapN_scope.
  Delimit Scope wrapN_scope with wrapN.
  (* ^ it would be nicer to have one delimiting key per instantiation of WrapN,
     but that doesn't seem possible? *)
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
