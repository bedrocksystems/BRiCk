Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import Auto.

Require Demo.A_cpp.
Require Import Demo.A_cpp_spec.

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
    repeat work.
    simplifying.
    unfold tlocal, tptsto.
    work. subst.
    simplifying.
    work. simpl.
    work.
    rewrite denoteModule_weaken.
    rewrite cglob'_weaken_any_ti.
    rewrite later_empSP.
    work. }

  finish_module.
Qed.
