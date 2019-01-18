From Cpp Require Import
     Ast HoareSemantics.
From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Demo Require
     A_hpp A_hpp_spec A_hpp_proof
     A_cpp A_cpp_spec A_cpp_proof.
Import A_hpp_spec.

Definition module_link (a b : list Decl) : list Decl := a ++ b.

Axiom denoteModule_link : forall nss a b,
    denoteModule nss (module_link a b) -|- denoteModule nss a ** denoteModule nss b.

(* todo(gmm): I'm a bit confused about the appropriate specification of linking
 *)
Lemma wand_apply : forall A B : mpred,
    A |-- (A -* B) ** B.
Proof.
  intros.
Abort.

Lemma lob_link : forall A B : mpred,
    ((|> A) -* B) ** ((|> B) -* A) |-- A ** B.
Proof.
  intros.
  eapply sepSPAdj'.
  rewrite <- empSPL.
  eapply sepSPAdj.
  rewrite <- (landtrueR empSP).
  apply landL2.
  eapply spec_lob.
Abort.
    (* |>A ==> B
     * |>B ==> A
     * A //\\ B
     *)

Theorem A_o_sound (resolve : _)
: denoteModule nil (module_link A_hpp.module A_cpp.module)
  |-- cglob' (resolve:=resolve) A__foo A__foo_spec **
      cglob' (resolve:=resolve) A__bar A__bar_spec.
Proof.
  rewrite denoteModule_link.
  rewrite (A_cpp_proof.A_cpp_sound resolve).
  rewrite (A_hpp_proof.A_hpp_sound resolve).
  unfold A_hpp_spec.
  unfold A_cpp_spec.A_cpp_spec.
Abort. (* todo(gmm): finish this proof *)