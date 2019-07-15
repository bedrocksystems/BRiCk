(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)

(* a "language" of triggers *)

(* [require_not_provable P Q] is the same as [Q] if [P] is not provable
 * otherwise, it fails.
 *)
Definition require_not_provable (P : Type) (Q : Prop) : Prop := Q.

(* [subst_everything P] is the same as [P] and then [subst] runs *)
Definition subst_everything (P : Prop) : Prop := P.

(* [subst_var x P] is the same as [P] and then [subst x] runs.
 * (note that [x] *must* be an indentifier or this will fail)
 *)
Definition subst_var {T : Type} (x : T) (P : Prop) : Prop := P.

(* [require_ident x P] is the same as [P] if [x] is an identifier,
 * otherwise, it fails.
 *)
Definition require_ident {T : Type} (x : T) (P : Prop) : Prop := P.

Local Ltac doesn't_know P :=
  lazymatch goal with
  | _ : P |- _ => fail
  | |- _ =>
    lazymatch P with
    | ?X = ?X => fail
    | True => fail
    | require_not_provable ?R _ =>
      assert_fails (assert R by eauto)
    | _ => idtac
    end
  end.

Local Ltac forget_first :=
  let X := fresh in intro X ; clear X.

Ltac learn :=
  let rec go k_prog k_noprog :=
      lazymatch goal with
      | |- ?P -> ?Q =>
        (* ^ this will match dependent products if ?Q is not there *)
        tryif (doesn't_know P)
        then (let H := fresh in intro H; cbv [require_not_provable] in H; go k_prog k_prog)
        else (forget_first; go k_prog k_noprog)
      | |- forall x, _ => intro; go k_prog k_noprog
      | |- subst_everything _ => red; subst; go k_prog k_noprog
      | |- @subst_var _ ?X _ => red; subst X; go k_prog k_noprog
      | |- require_ident _ ?X _ => red; is_var X; go k_prog k_noprog
      | |- _ => k_noprog
      end
  in
  go ltac:(idtac) ltac:(idtac; fail).
