Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

Require Import Cpp.Auto.

Require Demo.A_hpp.
Require Import Demo.A_hpp_spec.

Opaque denoteModule.

(* soundness of the specification *)
Theorem A_hpp_sound : forall (resolve : genv),
    denoteModule A_hpp.module |-- A_hpp_spec resolve.
Proof.
  intros.
  unfold A_hpp_spec.
  work.

  verifyF_forget A__bar.
  { (* A::bar(int) *)
    rewrite denoteModule_weaken.
    unfold func_ok'. simpl.
    work.
    simplifying.
    repeat perm_left ltac:(idtac; perm_right ltac:(idtac; eapply wp_call_glob)).
    simplifying.
    unfold tlocal, tptsto.
    work. subst.
    eapply has_type_qual with (q:={| q_const:=false ; q_volatile:=false |}) in H1.
    generalize (has_type_int_bound H1). intro.
    work.
    simplifying.
    work. }

  rewrite denoteModule_weaken.
  rewrite cglob'_weaken.
  rewrite later_empSP.
  work.
Qed.
