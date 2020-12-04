(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SSPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
(**
 * reflecting virtual function dispatch in the logic.
 *)
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import pred heap_pred path_pred.
Require Import bedrock.lang.cpp.logic.wp.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* the [Offset] to cast a [base] to a [derived] *)
  Fixpoint base_to_derived  `(d : class_derives σ derived base) : Offset :=
    match d with
    | Derives_here st _ => _id
    | Derives_base base st _ _ _ _ d =>
      _dot (base_to_derived d) (_derived (resolve:=σ) base derived)
    end.

  (* the [Offset] to cast a [derived] to a [base] *)
  Fixpoint derived_to_base `(d : class_derives σ derived base) : Offset :=
    match d with
    | Derives_here st _ => _id
    | Derives_base base st _ _ _ _ d =>
      _dot (_base (resolve:=σ) derived base) (derived_to_base d)
    end.

  Definition get_impl `(r : class_derives σ mdc tcls) (f : obj_name)
    : option (ptr * Offset) :=
    let override := (dispatch σ r f).1 in
    match override.(vimpl) with
    | None => None
    | Some s => match glob_addr σ s with
               | None => None
               | Some p => Some (p, base_to_derived override.(derivation))
               end
    end.

  (** [resolve_virtual σ this cls f Q] returns [Q fa this'] if resolving [f] on
   * [this] results in a function that is equivalent to calling the pointer [fa]
   * passing [this'] as the "this" argument.
   *)
  Definition resolve_virtual {σ : genv}
             (this : Loc) (cls : globname) (f : obj_name)
             (Q : forall (faddr this_addr : ptr), mpred) : mpred :=
    Exists σ' mdc (pf : class_derives σ' mdc cls),
        (* ^ we quantify over another program environment because class
             extension is open, the caller does not need to know the target
             function.
           - the [class_derives] fact *must* be in [σ'] because [mdc] might
             not exist in [σ].
         *)
      (Exists q, _at this (_identity σ' cls (Some mdc) q) **
                 [| class_compatible σ.(genv_tu) σ'.(genv_tu) cls |] ** ltrue) //\\
              (* ^ the [class_compatible σ' mdc cls] ensures that the virtual
                   tables the [cls] class are compatible between the (possibly
                   different) translation units.
               *)
      match get_impl pf f with
      | Some (fa, off) =>
        Exists p, _offsetL off this &~ p ** Q fa p
      | None => (* the function wasn't found or the implemenation was pure virtual *)
        lfalse
      end.

End with_cpp.
