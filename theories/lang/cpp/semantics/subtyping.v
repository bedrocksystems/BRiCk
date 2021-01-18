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
Require Import bedrock.lang.cpp.semantics.values.

Section extends.
  Context (σ : genv).

  (** [class_derives mdc cls] is a/the proof that [mdc] is a derived class
      of [cls] (equivalently, [cls] is a base class of [mdc])

      note that this definition is in [Set] allowing us to compute over it.
   *)
  Inductive class_derives (derived : globname) : globname -> Set :=
  | Derives_here {st}
      {_ : σ.(genv_tu).(globals) !! derived = Some (Gstruct st)}
    : class_derives derived derived

  | Derives_base base {st li result}
      {_ : σ.(genv_tu).(globals) !! derived = Some (Gstruct st)}
      {_ : In (base, li) st.(s_bases)}
      (_ : class_derives base result)
    : class_derives derived result

  (* this could be extended for virtuals *)
  .

End extends.

Arguments Derives_here {_ _} _ _.
Arguments Derives_base {_ _} _.
Arguments class_derives σ derived base : rename.

(** The following instances enable TC resolution to prove
[class_derives σ derived base] when the translation unit [tu] and
class names [derived], [base] are ground.

The proofs use [iffLR] to avoid destructing [iff]. While verbose,
that's presumably faster. *)
Existing Class class_derives.
Global Hint Mode class_derives + + + : typeclass_instances.

Global Instance class_derives_here tu σ derived st :
  tu ⊧ σ ->
  TCEq (tu.(globals) !! derived) (Some (Gstruct st)) ->
  class_derives σ derived derived.
Proof.
  intros. eapply Derives_here, genv_compat_lookup_Some_type.
  - done.
  - by apply (iffLR (TCEq_eq _ _)).
Defined.

Global Instance class_derives_base tu σ derived base st li result :
  tu ⊧ σ ->
  TCEq (tu.(globals) !! derived) (Some (Gstruct st)) ->
  TCElemOf (base, li) st.(s_bases) ->
  class_derives σ base result ->
  class_derives σ derived result.
Proof.
  intros. eapply Derives_base.
  - eapply genv_compat_lookup_Some_type.
    done. by apply (iffLR (TCEq_eq _ _)).
  - by apply (iffLR (elem_of_list_In _ _)), (iffLR (TCElemOf_iff _ _)).
  - done.
Defined.
