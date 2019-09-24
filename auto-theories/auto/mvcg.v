(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(* Automation for verification of modules.
 *)
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import
     Ast Sem Util
     Auto.Definitions
     Auto.Lemmas
     Auto.Discharge
     Signature.

Require Import bedrock.auto.drop_to_emp.

Section find_in_module.
  Variable nm : obj_name.

  Variant CodeType : Set :=
  | CTmethod (_ : Method)
  | CTctor (_ : Ctor)
  | CTdtor (_ : Dtor)
  | CTfunction (_ : Func).

  Definition find_code (m : compilation_unit) : option CodeType :=
    match lookup_symbol m nm with
    | Some (Ofunction f) =>
      match f.(f_body) with
      | None => None
      | _ => Some (CTfunction f)
      end
    | Some (Omethod f)  =>
      match f.(m_body) with
      | None => None
      | _ => Some (CTmethod f)
      end
    | Some (Oconstructor f) =>
      match f.(c_body) with
      | None => None
      | _ => Some (CTctor f)
      end
    | Some (Odestructor f)  =>
      match f.(d_body) with
      | None => None
      | _ => Some (CTdtor f)
      end
    | _ => None
    end.

End find_in_module.

Lemma make_signature_ticptr_cons : forall s x ss,
    s.(s_spec) = ticptr x ->
    make_signature (s :: ss) |-- make_signature ss.
Proof. Admitted.
Hint Rewrite make_signature_ticptr_cons using reflexivity : done_proof.

(* (* todo(gmm): these are new definitions *) *)
(* Lemma cut_spec' (s : specification) P Q sp : *)
(*   s.(s_spec) = ticptr sp -> *)
(*   P |-- _at (_global s.(s_name)) s.(s_spec) ** ltrue -> *)
(*   P ** make_signature (s :: nil) |-- Q -> *)
(*   P |-- Q. *)
(* Proof. Admitted. *)

(* Lemma verify_ticptr : forall resolve cu nm sp what P, *)
(*     find_code nm cu = Some what -> *)
(*     match what with *)
(*     | CTmethod meth => *)
(*       forall ti, denoteModule cu ** P |-- @method_ok resolve meth ti sp *)
(*     | CTctor ctor => *)
(*       forall ti, denoteModule cu ** P |-- @ctor_ok resolve ctor ti sp *)
(*     | CTdtor dtor => *)
(*       forall ti, denoteModule cu ** P |-- @dtor_ok resolve dtor ti sp *)
(*     | CTfunction func => *)
(*       match func.(f_body) with *)
(*       | None => False *)
(*       | Some body => *)
(*         forall ti, *)
(*             denoteModule cu ** P |-- @func_ok resolve func.(f_return) func.(f_params) body ti sp *)
(*       end *)
(*     end -> *)
(*     denoteModule cu ** P |-- _at (_global nm) (ticptr sp) ** ltrue. *)
(* Proof. Admitted. *)

(* Ltac cut_spec spec := *)
(*   lazymatch goal with *)
(*   | resolve : genv |- _ => *)
(*     perm_left ltac:(idtac; eapply (cut_spec' spec); *)
(*                     [ reflexivity *)
(*                     | eapply (@verify_ticptr resolve); [ reflexivity | simpl; intros ] | ]) *)
(*   end. *)



Ltac start_module :=
  repeat eapply wandSPI.

(*
Inductive Subtract {T} (xs : list T) : list T -> list T -> bool -> Prop :=
| Sub_nil : Subtract xs nil nil false
| Sub_found {y ys zs b} (_ : In y xs) (_ : Subtract xs ys zs b)
  : Subtract xs (y :: ys) zs true
| Sub_other {y ys zs b} (_ : Subtract xs ys zs b)
  : Subtract xs (y :: ys) (y :: zs) b
.

Lemma make_signature_cons : forall a b,
    make_signature (a :: b) -|- _at (_global a.(s_name)) a.(s_spec) ** make_signature b.
Proof.
  intros. Transparent make_signature.
  unfold make_signature.
  simpl. reflexivity.
  Opaque make_signature.
Qed.

(* note(gmm): this definition assumes that everything inside of a make_signature
 * is persistent, we could enforce this with a persistence modality in make_signature
 *)
Lemma signature_reduce : forall ss ss' ss'',
    Subtract ss ss' ss'' true ->
    forall P Q,
    make_signature ss ** P |-- make_signature ss'' ** Q ->
    make_signature ss ** P |-- make_signature ss' ** Q.
Proof.
  induction 1; auto.
  { intros. rewrite make_signature_cons.
    admit. }
  { admit. }
Admitted.

Lemma signature_nil : forall P Q,
    P |-- Q ->
    P |-- make_signature nil ** Q.
Proof.
  intros. rewrite make_signature_nil. rewrite empSPL. apply H.
Qed.

Ltac solve_subtract :=
  first [ simple eapply Sub_found; [ simpl; tauto | solve_subtract ]
        | simple eapply Sub_other; [ solve_subtract ]
        | simple eapply Sub_nil
        ].
*)

Lemma cut_spec {resolve} (SP : mpred) : forall nm fs,
    SP = _at (_global nm) (ticptr fs) ->
    forall cu what, find_code nm cu = Some what ->
    (* note(gmm): this obligation isn't complete with respect to global
     * variables, but it should still be sound-ish (modulo persistence)
     *)
    forall P,
    match what with
    | CTmethod meth =>
      forall ti, denoteModule cu ** P |-- @method_ok resolve meth ti fs
    | CTctor ctor =>
      forall ti, denoteModule cu ** P |-- @ctor_ok resolve ctor ti fs
    | CTdtor dtor =>
      forall ti, denoteModule cu ** P |-- @dtor_ok resolve dtor ti fs
    | CTfunction func =>
      match func.(f_body) with
      | None => False
      | Some body =>
        forall ti,
            denoteModule cu ** P |-- @func_ok resolve func.(f_return) func.(f_params) body ti fs
      end
    end -> forall Q,
    denoteModule cu ** SP ** P |-- Q ->
    denoteModule cu ** P |-- Q.
Proof.
Admitted.

Lemma verify_spec (remember : bool) {resolve} (SP : mpred) : forall nm fs,
    SP = _at (_global nm) (ticptr fs) ->
    forall cu what, find_code nm cu = Some what ->
    (* note(gmm): this obligation isn't complete with respect to global
     * variables, but it should still be sound-ish (modulo persistence)
     *)
    forall P,
    match what with
    | CTmethod meth =>
      forall ti, denoteModule cu ** P |-- @method_ok resolve meth ti fs
    | CTctor ctor =>
      forall ti, denoteModule cu ** P |-- @ctor_ok resolve ctor ti fs
    | CTdtor dtor =>
      forall ti, denoteModule cu ** P |-- @dtor_ok resolve dtor ti fs
    | CTfunction func =>
      match func.(f_body) with
      | None => False
      | Some body =>
        forall ti,
            denoteModule cu ** P |-- @func_ok resolve func.(f_return) func.(f_params) body ti fs
      end
    end -> forall Q,
    denoteModule cu ** (if remember then SP ** P else P) |-- Q ->
    denoteModule cu ** P |-- SP ** Q.
Proof.
Admitted.

Ltac verify_spec sp :=
  lazymatch goal with
  | resolve : genv |- _ =>
    perm_right ltac:(idtac;
                     lazymatch goal with
                     | |- _ |-- sp ** _ =>
                       perm_left ltac:(idtac; eapply (@verify_spec true resolve sp _ _ eq_refl); [ reflexivity | intro; simpl | ])
                     end)
  end.

Ltac verify_forget_spec sp :=
  lazymatch goal with
  | resolve : genv |- _ =>
    perm_right ltac:(idtac;
                     lazymatch goal with
                     | |- _ |-- sp ** _ =>
                       perm_left ltac:(idtac; eapply (@verify_spec false resolve sp _ _ eq_refl); [ reflexivity | intro; simpl | ])
                     end)
  end.

Ltac cut_spec sp :=
  lazymatch goal with
  | resolve : genv |- _ =>
    perm_left ltac:(idtac; eapply (@cut_spec resolve sp _ _ eq_refl); [ reflexivity | intro; simpl | ])
  end.


Ltac finish_module :=
  try lazymatch goal with
      | |- _ |-- empSP =>
        drop_to_emp ;
        try (autorewrite with done_proof);
        repeat rewrite denoteModule_weaken ;
        repeat rewrite ti_cglob_weaken ;
        repeat rewrite cglob_weaken ;
        repeat rewrite later_cglob_ti ;
        repeat rewrite later_empSP ;
        repeat rewrite empSPR;
        solve [ discharge fail idtac fail fail idtac
              | lazymatch goal with
                | |- ?G => fail "failed to solve " G
                end ]
      end.

Global Opaque make_signature.
