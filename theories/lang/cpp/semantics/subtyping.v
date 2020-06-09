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
