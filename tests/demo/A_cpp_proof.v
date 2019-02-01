Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import Auto.

Require Demo.A_cpp.
Require Import Demo.A_cpp_spec.

(* this is an axiom *)
Axiom has_type_int_any : forall x, has_type (Vint x) T_int.
Axiom cglob'_emp : forall resolve a b, cglob' (resolve:=resolve)a b |-- empSP.

Opaque denoteModule.

(* soundness of the specification *)
Theorem A_cpp_sound : forall (resolve : genv),
    denoteModule A_cpp.module |-- A_cpp_spec resolve.
Proof.
  intros.
  unfold A_cpp_spec.
  work.

  verifyF_forget A_hpp_spec.A__foo.
  { (* A::foo(int) *)
    unfold  func_ok'. simpl.
    work.
    simplifying.
    repeat perm_left ltac:(idtac; perm_right ltac:(idtac; eapply wp_call_glob)).
    simplifying.
    unfold tlocal, tptsto.
    work. subst.
    simplifying.
    eapply landR.
    work.
    (* todo(gmm): figure out why replacing this with `work` diverges *)
    discharge ltac:(canceler ltac:(fail) tac) tac.
    eapply embedPropR.
    eapply eval_add.
    Unshelve. reflexivity. instantiate (1:=T_int).
    Unshelve.  eapply has_type_int_any.
    simpl.
    work.
    rewrite denoteModule_weaken.
    rewrite cglob'_emp.
    rewrite later_empSP.
    work. }
  
  rewrite denoteModule_weaken.
  rewrite cglob'_emp.
  rewrite later_empSP.
  work.
Qed.
