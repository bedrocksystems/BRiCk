(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import stdpp.decidable.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.values.
Require Import bedrock.lang.cpp.semantics.subtyping.

Record vhandle {σ : genv} : Set :=
  { vimpl      : option obj_name
  ; voverrider : globname
  ; vfrom      : globname
  ; derivation : class_derives σ voverrider vfrom }.
Arguments vhandle σ : clear implicits.

Section dispatch.
  Context (σ : genv).

  Definition list_get {T} (t : obj_name) (l : list (obj_name * T)) : option T :=
    match
      List.find (fun '(t',_) =>
                   if decide (t = t') then true else false) l
    with
    | None => None
    | Some (_, k) => Some k
    end.

  Fixpoint dispatch `(d : class_derives σ mdc from) (final : obj_name)
    : vhandle σ * obj_name :=
    match d with
    | Derives_here st _ =>
      ({| vimpl := mjoin (list_get final st.(s_virtuals))
        ; voverrider := mdc
        ; vfrom := from
        ; derivation := d |}, final)
    | Derives_base base st _ _ _ _ d' =>
      let '(result, cand) := dispatch d' final in
      match list_get cand st.(s_overrides) with
      | None => (result, cand)
      | Some cand =>
        ({| vimpl := mjoin (list_get final st.(s_virtuals))
          ; voverrider := mdc
          ; vfrom := from
          ; derivation := d |}, cand)
      end
    end.

End dispatch.
