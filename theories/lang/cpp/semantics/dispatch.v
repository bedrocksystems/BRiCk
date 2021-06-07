(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import stdpp.decidable.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.genv.
Require Import bedrock.lang.cpp.semantics.subtyping.

(** Dispatching to a virtual function contains two pieces:
    1. Finding the correct function to invoke
    2. Fixing up the dispatch object.
    Consider the following example
    [[[
    struct A { virtual void foo() = 0; };
    struct B : public A { virtual void foo() { } };

    A* a = new B();
    a->foo(); // same as [static_cast<B*>(a)->B::foo()]
    ]]]
    note that in order to dispatch to the overridden function
    the dispatch also introduces a [static_cast] to get a pointer
    of the correct type.
 *)
Record vhandle {σ : genv} : Set :=
  { (* the name of the method that implements the function
       [None] means that there is no body.
     *)
    vimpl      : option obj_name
  ; voverrider : globname
  ; vfrom      : globname
  ; (* the cast for the [this] parameter *)
    derivation : class_derives σ voverrider vfrom }.
Arguments vhandle σ : clear implicits.

Section dispatch.
  Context (σ : genv).

  Definition list_get {T} (t : obj_name) (l : list (obj_name * T)) : option T :=
    snd <$> List.find (fun '(t',_) => bool_decide (t = t')) l.

  (** [dispatch' mdc from deriv final = (impl, cand)]
      [impl] is the function to dispatch to and the fixup logic.
      [cand] is the name of the implementation, which might be further overridden.
   *)
  #[local] Fixpoint dispatch' `(d : !class_derives σ mdc from) (final : obj_name)
    : vhandle σ * obj_name :=
    match d with
    | Derives_here st _ =>
      ({| vimpl := mjoin (list_get final st.(s_virtuals))
        ; voverrider := mdc
        ; vfrom := from
        ; derivation := d |}, final)
    | Derives_base base st _ _ _ _ d' =>
      let result := dispatch' d' final in
      match list_get result.2 st.(s_overrides) with
      | None => result
      | Some cand' =>
        ({| vimpl := Some cand'
          ; voverrider := mdc
          ; vfrom := from
          ; derivation := d |}, cand')
      end
    end.

  (** [dispatch' mdc from deriv final] determines the function to
      dispatch to and the fixup logic when calling [final] on an object
      whose most derived class is [mdc].
   *)
  Definition dispatch `(d : !class_derives σ mdc from) (final : obj_name)
    : vhandle σ := (dispatch' d final).1.

End dispatch.
