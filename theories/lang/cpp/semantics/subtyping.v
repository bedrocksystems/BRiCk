(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)

(*
 * This file defines various class relationships that are used in C++,
 * mostly around sub-typing and virtual dispatch.
 *
 * todo: this should build on Tahina's work
 *   http://gallium.inria.fr/~tramanan/cpp/thesis/thesis.pdf
 *)
Require Import stdpp.fin_maps.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.genv.

Section extends.
  Context (σ : genv).

  (** [class_derives σ derived path]
      - [derived] is the derived class name
      - [path] is the path from the derived class (head of the list)
        to the base class (end of the list)
      An example,
      ```c++
      class A {};
      class B : public A {};
      class C : public B {};
      ```
      the following hold:
      - [class_derives "::A" []], [class_derives "::B" []], [class_derives "::C" []]
      - [class_derives "::B" ["::A"]], [class_derives "::C" ["::B"]]
      - [class_derives "::C" ["::B","::A"]]
   *)
  Inductive class_derives (derived : globname) : list globname -> Prop :=
  | Derives_here {st}
      {_ : σ.(genv_tu) !! derived = Some (Gstruct st)}
    : class_derives derived []

  | Derives_base {base st li rest}
      {_ : σ.(genv_tu) !! derived = Some (Gstruct st)}
      {_ : (base, li) ∈ st.(s_bases)}
      (_ : class_derives base rest)
    : class_derives derived (base :: rest)

  (* this does not currently support `virtual` inheritence. *)
  .

  (** [class_derives] is closed under prefixes. *)
  #[local]
  Lemma class_derives_drop path1 path2 : forall derived,
    class_derives derived (path1 ++ path2) ->
    class_derives derived path1.
  Proof.
    induction path1 => /= ? H.
    { inversion H; subst; try econstructor; eauto. }
    { inversion H; subst. econstructor; eauto. }
  Qed.

End extends.

Arguments Derives_here {_ _} _ _.
Arguments Derives_base {_ _} _.
Arguments class_derives {σ} derived path : rename.

(** The following instances enable TC resolution to prove
[class_derives σ derived base] when the translation unit [tu] and
class names [derived], [base] are ground.

The proofs use [iffLR] to avoid destructing [iff]. While verbose,
that's presumably faster. *)
Existing Class class_derives.
#[global] Hint Mode class_derives - + + : typeclass_instances.

Section tu.
  Variable tu : translation_unit.

  Fixpoint tu_class_derives (cls : globname) (path : list globname) : bool :=
    match tu !! cls with
    | Some (Gstruct st) =>
        match path with
        | nil => true
        | base :: rest =>
            if bool_decide (base ∈ (fst <$> st.(s_bases))) then
              tu_class_derives base rest
            else false
        end
    | _ => false
    end.

  Context {σ : genv} {M : tu ⊧ σ}.
  Theorem tu_class_derives_sound : forall path cls,
      tu_class_derives cls path -> class_derives cls path.
  Proof using M.
    induction path =>///=.
    { intros; case_match.
      { repeat case_match => //.
        apply glob_def_genv_compat_struct in Heqo.
        econstructor. eassumption. }
      { inversion H. } }
    { intros; repeat (case_bool_decide || case_match) =>//.
      apply glob_def_genv_compat_struct in Heqo.
      eapply elem_of_list_fmap_2 in H0.
      destruct H0 as [?[??]].
      destruct x; simpl in H; subst.
      econstructor; try eassumption.
      by apply IHpath. }
  Qed.
End tu.

#[global] Hint Extern 0 (class_derives _ _) =>
  eapply tu_class_derives_sound; [ eassumption | vm_compute; exact I ] : typeclass_instances.

(*
#[global] Instance class_derives_here tu σ derived st :
  tu ⊧ σ ->
  TCEq (tu !! derived) (Some (Gstruct st)) ->
  class_derives derived [].
Proof.
  intros. eapply Derives_here, glob_def_genv_compat_struct.
  by apply (iffLR (TCEq_eq _ _)).
Defined.

#[global] Instance class_derives_base tu σ rest derived base st li :
  tu ⊧ σ ->
  TCEq (tu !! derived) (Some (Gstruct st)) ->
  TCElemOf (base, li) st.(s_bases) ->
  class_derives base rest ->
  class_derives derived (base :: rest).
Proof.
  intros. eapply Derives_base; last done.
  - eapply glob_def_genv_compat_struct.
    by apply (iffLR (TCEq_eq _ _)).
  - by apply (iffLR (TCElemOf_iff _ _)).
Defined.
*)
