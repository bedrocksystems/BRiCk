(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
(** this file defines the core logic (called [mpred]) that we use
    for C++.

    known issues:
    - currently the logic is sequentially consistent
    - the memory model is simplified from the standard C++ memory
      model.
 *)
From Coq.Classes Require Import
     RelationClasses Morphisms.

From iris.base_logic.lib Require Export iprop.
Require Import iris.bi.monpred.
From iris.bi.lib Require Import fractional.
Require Import iris.base_logic.lib.fancy_updates.
Require Import iris.base_logic.lib.own.
Require Import iris.base_logic.lib.cancelable_invariants.

From bedrock Require Export IrisBridge.
Export ChargeNotation.

From bedrock.lang.cpp Require Import ast semantics.

Set Default Proof Using "Type".

Module Type CPP_LOGIC_CLASS_BASE.
  Parameter cppG : gFunctors -> Type.
  Parameter has_inv : forall Σ, cppG Σ -> invG Σ.
  Parameter has_cinv : forall Σ, cppG Σ -> cinvG Σ.

  Existing Class cppG.

  Parameter _cpp_ghost : Type.
End CPP_LOGIC_CLASS_BASE.

Module Type CPP_LOGIC_CLASS_MIXIN (Import CC : CPP_LOGIC_CLASS_BASE).

  Class cpp_logic {thread_info : biIndex} : Type :=
  { _Σ       : gFunctors
  ; _ghost   : _cpp_ghost
  ; has_cppG :> cppG _Σ }.
  Arguments cpp_logic : clear implicits.
  Coercion _Σ : cpp_logic >-> gFunctors.

End CPP_LOGIC_CLASS_MIXIN.

Module Type CPP_LOGIC_CLASS := CPP_LOGIC_CLASS_BASE <+ CPP_LOGIC_CLASS_MIXIN.

Module Type CPP_LOGIC (Import CC : CPP_LOGIC_CLASS).

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    Definition mpred := iProp Σ.
    Canonical Structure mpredI : bi :=
      {| bi_car := mpred
       ; bi_later := bi_later
       ; bi_ofe_mixin := (iPropI Σ).(bi_ofe_mixin)
       ; bi_bi_mixin := (iPropI Σ).(bi_bi_mixin)
       ; bi_bi_later_mixin := (iPropI Σ).(bi_bi_later_mixin)
       |}.
    (* todo: Fix the warning generated from this definition *)

    (* Typeclasses Opaque mpred.
    Global Instance mpred_later_contractive : BiLaterContractive mpredI.
    Proof. apply _. Qed. *)

    (* valid pointers allow for accessing one past the end of a structure/array *)
    Parameter valid_ptr : ptr -> mpred.

    Axiom valid_ptr_persistent : forall p, Persistent (valid_ptr p).
    Axiom valid_ptr_affine : forall p, Affine (valid_ptr p).
    Axiom valid_ptr_timeless : forall p, Timeless (valid_ptr p).
    Existing Instance valid_ptr_persistent.
    Existing Instance valid_ptr_affine.
    Existing Instance valid_ptr_timeless.

    Axiom valid_ptr_nullptr : |-- valid_ptr nullptr.

    (**
    Typed points-to predicate. Fact [tptsto t q p v] asserts the following things:
    1. Pointer [p] points to value [v].
    2. We have fractional ownership [q] (in the separation logic sense).
    3. Pointer [p] points to a memory location with C++ type [t].
    However:
    1. Value [v] need not be initialized.
    2. Hence, [v] might not satisfy [has_type t v].

    We use this predicate both for pointers to actual memory and for pointers to
    C++ locations that are not stored in memory (as an optimization).
    *)
    Parameter tptsto : forall {σ:genv} (t : type) (q : Qp) (a : ptr) (v : val), mpred.

    Axiom tptsto_proper :
      Proper (genv_eq ==> eq ==> eq ==> eq ==> eq ==> (≡)) (@tptsto).
    Axiom tptsto_mono :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> (⊢)) (@tptsto).

    Axiom tptsto_timeless :
      forall {σ} ty q a v, Timeless (@tptsto σ ty q a v).
    Axiom tptsto_fractional :
      forall {σ} ty a v, Fractional (λ q, @tptsto σ ty q a v).
    Axiom tptsto_as_fractional :
      forall {σ} ty q a v, AsFractional (@tptsto σ ty q a v) (λ q, @tptsto σ ty q a v)%I q.

(* not currently sound wrt [simple_pred]
    Axiom tptsto_agree : forall {σ} ty q1 q2 a v1 v2,
      @tptsto σ ty q1 a v1 ** @tptsto σ ty q2 a v2 |-- [| v1 = v2 |].
*)

(* this isn't actually needed
    Axiom tptsto_valid_ptr : forall σ t q a v,
        @tptsto σ t q a v |-- @tptsto σ t q a v ** valid_ptr a.
*)

    (** this states that the pointer is a pointer to the given type,
        this is persistent. this implies,
        - the address is not null
        - the address is properly aligned (if it exists in memory)
     *)
    Parameter type_ptr: forall {resolve : genv} (c: type), ptr -> mpred.
    Axiom type_ptr_persistent : forall σ p ty,
      Persistent (type_ptr (resolve:=σ) ty p).

    (** [identity σ this mdc q p] state that [p] is a pointer to a (live)
        object of type [this] that is part of an object of type [mdc].
        - if [mdc = None] then this object identity is not initialized yet,
          e.g. because its base classes are still being constructed.

        the information is primarily used to dispatch virtual function calls.

        compilers can use the ownership here to represent dynamic dispatch
        tables.
     *)
    Parameter identity : forall {σ : genv}
        (this : globname) (most_derived : option globname),
        Qp -> ptr -> mpred.
    (** PDS: [Fractional], [AsFractional], [Timeless]? *)

    (** this allows you to forget an object identity, necessary for doing
        placement [new] over an existing object.
     *)
    Axiom identity_forget : forall σ mdc this p,
        @identity σ this (Some mdc) 1 p |-- @identity σ this None 1 p.

    (** the pointer points to the code

      note that in the presence of code-loading, function calls will
      require an extra side-condition that the code is loaded.
     *)
    Parameter code_at : genv -> Func -> ptr -> mpred.
    Parameter method_at : genv -> Method -> ptr -> mpred.
    Parameter ctor_at : genv -> Ctor -> ptr -> mpred.
    Parameter dtor_at : genv -> Dtor -> ptr -> mpred.

    Section with_genv.
      Context {σ : genv}.
      Local Notation code_at := (code_at σ) (only parsing).
      Local Notation method_at := (method_at σ) (only parsing).
      Local Notation ctor_at := (ctor_at σ) (only parsing).
      Local Notation dtor_at := (dtor_at σ) (only parsing).

      Axiom code_at_persistent : forall f p, Persistent (code_at f p).
      Axiom code_at_affine : forall f p, Affine (code_at f p).
      Axiom code_at_timeless : forall f p, Timeless (code_at f p).

      Axiom method_at_persistent : forall f p, Persistent (method_at f p).
      Axiom method_at_affine : forall f p, Affine (method_at f p).
      Axiom method_at_timeless : forall f p, Timeless (method_at f p).

      Axiom ctor_at_persistent : forall f p, Persistent (ctor_at f p).
      Axiom ctor_at_affine : forall f p, Affine (ctor_at f p).
      Axiom ctor_at_timeless : forall f p, Timeless (ctor_at f p).

      Axiom dtor_at_persistent : forall f p, Persistent (dtor_at f p).
      Axiom dtor_at_affine : forall f p, Affine (dtor_at f p).
      Axiom dtor_at_timeless : forall f p, Timeless (dtor_at f p).
    End with_genv.

    (** Physical representation of pointers. *)
    (** [pinned_ptr va p] states that dereferencing abstract pointer [p]
    implies dereferencing address [va].
    [pinned_ptr] will only hold on pointers that are associated to addresses,
    but other pointers exist. *)
    Parameter pinned_ptr : N -> ptr -> mpred.
    Axiom pinned_ptr_persistent : forall va p, Persistent (pinned_ptr va p).
    Axiom pinned_ptr_affine : forall va p, Affine (pinned_ptr va p).
    Axiom pinned_ptr_timeless : forall va p, Timeless (pinned_ptr va p).
    Axiom pinned_ptr_unique : forall va va' p,
        pinned_ptr va p ** pinned_ptr va' p |-- bi_pure (va = va').

  End with_cpp.

End CPP_LOGIC.

Declare Module LC : CPP_LOGIC_CLASS.
Declare Module L : CPP_LOGIC LC.
Export LC L.

Bind Scope bi_scope with mpred.
Bind Scope bi_scope with mpredI.
Bind Scope bi_scope with bi_car.

(** Instances from [LC] *)
Existing Instances LC.has_inv LC.has_cinv LC.has_cppG.

(** Instances from [L] *)
Existing Instances
  (** [valid_ptr] *)
  L.valid_ptr_persistent L.valid_ptr_affine L.valid_ptr_timeless

  (** [tptsto] *)
  L.tptsto_proper L.tptsto_mono
  L.tptsto_timeless
  L.tptsto_fractional L.tptsto_as_fractional

  (** [type_ptr] *)
  L.type_ptr_persistent

  (** [identity] *)
  (** PDS: [Fractional], [AsFractional], [Timeless]? *)

  (** [code_at] *)
  L.code_at_persistent L.code_at_affine L.code_at_timeless

  (** [method_at *)
  L.method_at_persistent L.method_at_affine L.method_at_timeless

  (** [ctor_at] *)
  L.ctor_at_persistent L.ctor_at_affine L.ctor_at_timeless

  (** [dtor_at] *)
  L.dtor_at_persistent L.dtor_at_affine L.dtor_at_timeless

  (** [pinned_ptr] *)
  L.pinned_ptr_persistent L.pinned_ptr_affine L.pinned_ptr_timeless.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  Global Instance tptsto_flip_mono :
    Proper (flip genv_leq ==> eq ==> eq ==> eq ==> eq ==> flip (⊢))
      (@tptsto _ Σ).
  Proof. repeat intro. exact: tptsto_mono. Qed.

  (** function specifications written in weakest pre-condition style.
   *)
  Record function_spec : Type :=
    { fs_cc : calling_conv
    ; fs_return : type
    ; fs_arguments : list type
    ; fs_spec : thread_info -> list val -> (val -> mpred) -> mpred
    }.
  Arguments function_spec : clear implicits.
  Arguments Build_function_spec : clear implicits.

  Definition type_of_spec `(fs : function_spec) : type :=
    normalize_type (Tfunction (cc:=fs.(fs_cc)) fs.(fs_return) fs.(fs_arguments)).

End with_cpp.
