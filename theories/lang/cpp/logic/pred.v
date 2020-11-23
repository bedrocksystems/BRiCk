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
Require Import bedrock.lang.prelude.base.
Require Export bedrock.lang.prelude.addr.

From iris.base_logic.lib Require Export iprop.
Require Import iris.bi.monpred.
From iris.bi.lib Require Import fractional.
Require Import iris.base_logic.lib.fancy_updates.
Require Import iris.base_logic.lib.own.
Require Import iris.base_logic.lib.cancelable_invariants.

Require Export bedrock.lang.bi.prelude.
Require Export bedrock.lang.bi.observe.
Export ChargeNotation.

From bedrock.lang.cpp Require Import ast semantics.

Module Type CPP_LOGIC_CLASS_BASE.
  Parameter cppG : gFunctors -> Type.
  Axiom has_inv : forall Σ, cppG Σ -> invG Σ.
  Axiom has_cinv : forall Σ, cppG Σ -> cinvG Σ.

  Global Existing Instances has_inv has_cinv.

  Existing Class cppG.

  Parameter _cpp_ghost : Type.
End CPP_LOGIC_CLASS_BASE.

Module Type CPP_LOGIC_CLASS_MIXIN (Import CC : CPP_LOGIC_CLASS_BASE).

  Class cpp_logic {thread_info : biIndex} : Type :=
  { _Σ       : gFunctors
  ; _ghost   : _cpp_ghost
  ; has_cppG : cppG _Σ
  }.
  Arguments cpp_logic : clear implicits.
  Coercion _Σ : cpp_logic >-> gFunctors.

  Global Existing Instance has_cppG.

  Section with_cpp.
    Context `{cpp_logic}.

    Definition mpred := iProp _Σ.
    Canonical Structure mpredO : ofeT
      := OfeT mpred (ofe_mixin (iPropO _Σ)).
    Canonical Structure mpredI : bi :=
    {|
      bi_car := mpred ;
      bi_ofe_mixin := bi_ofe_mixin (iPropI _Σ);
      bi_bi_mixin := bi_bi_mixin (iPropI _Σ);
      bi_bi_later_mixin := bi_bi_later_mixin (iPropI _Σ);
    |}.

    Definition mPrePredO : ofeT := iPrePropO _Σ.

    Definition mpred_unfold : mpredO -n> mPrePredO := iProp_unfold.
    Definition mpred_fold : mPrePredO -n> mpredO := iProp_fold.

    Definition mpred_fold_unfold :
      ∀ (P : mpred), mpred_fold (mpred_unfold P) ≡ P := iProp_fold_unfold.
    Definition mpred_unfold_fold :
      ∀ (P : mPrePredO), mpred_unfold (mpred_fold P) ≡ P := iProp_unfold_fold.

    (* TODO: generalize to a telescope version of -d> *)
    (* With something like -td> below:
      Definition laterPred `{cpp_logic} {T: tele} (Q : T -t> mpred) :
        laterO (T -td> mPrePredO) :=
        Next (λ args, mpred_unfold (tele_app Q args)). *)
    Definition mPrePredO_to_laterO (P : mpred) : laterO mPrePredO :=
      Next (mpred_unfold P).

    Definition mPrePredO_to_laterO_1 {A: ofeT}
      (P : ofe_car A -> mpred) : laterO (A -d> mPrePredO) :=
      Next (fun a => mpred_unfold (P a)).
  End with_cpp.

  Bind Scope bi_scope with bi_car.
  Bind Scope bi_scope with mpred.
  Bind Scope bi_scope with mpredI.
End CPP_LOGIC_CLASS_MIXIN.

Module Type CPP_LOGIC_CLASS := CPP_LOGIC_CLASS_BASE <+ CPP_LOGIC_CLASS_MIXIN.

Module Type CPP_LOGIC (Import CC : CPP_LOGIC_CLASS) (Import PTR : PTRS_FULL).

  (* TODO: unify with [raw_byte]. This should just be machine bytes. See also
    cpp2v-core#135. *)
  Parameter runtime_val : Type.

  (* XXX why does this not work in the module type. *)
  Bind Scope ptr_scope with ptr.
  Bind Scope offset_scope with offset.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    (* valid pointers allow for accessing one past the end of a structure/array *)
    Parameter valid_ptr : ptr -> mpred.

    Axiom valid_ptr_persistent : forall p, Persistent (valid_ptr p).
    Axiom valid_ptr_affine : forall p, Affine (valid_ptr p).
    Axiom valid_ptr_timeless : forall p, Timeless (valid_ptr p).
    Global Existing Instances valid_ptr_persistent valid_ptr_affine valid_ptr_timeless.

    Axiom valid_ptr_nullptr : |-- valid_ptr nullptr.

    (** Formalizes the notion of "provides storage",
    http://eel.is/c++draft/intro.object#def:provides_storage *)
    Parameter provides_storage : ptr -> ptr -> type -> mpred.

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

    Axiom tptsto_nonnull : forall {σ} ty q a,
      @tptsto σ ty q nullptr a |-- False.

    Axiom tptsto_proper :
      Proper (genv_eq ==> eq ==> eq ==> eq ==> eq ==> (≡)) (@tptsto).
    Axiom tptsto_mono :
      Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> (⊢)) (@tptsto).
    Global Existing Instances tptsto_proper tptsto_mono.

    Axiom tptsto_timeless :
      forall {σ} ty q a v, Timeless (@tptsto σ ty q a v).
    Axiom tptsto_fractional :
      forall {σ} ty a v, Fractional (λ q, @tptsto σ ty q a v).
    Global Existing Instances tptsto_timeless tptsto_fractional.

    Axiom tptsto_frac_valid : forall {σ} t (q : Qp) p v,
      Observe [| q ≤ 1 |]%Qc (@tptsto σ t q p v).
    Global Existing Instance tptsto_frac_valid.

    Axiom tptsto_agree : forall {σ} t q1 q2 p v1 v2,
      Observe2 [| v1 = v2 |] (@tptsto σ t q1 p v1) (@tptsto σ t q2 p v2).
    Global Existing Instance tptsto_agree.

    Axiom tptsto_valid_ptr : forall σ t q p v,
      Observe (valid_ptr p) (@tptsto σ t q p v).
    Global Existing Instance tptsto_valid_ptr.

    Axiom tptsto_nonvoid : forall {σ} ty (q : Qp) p v,
      Observe [| ty <> Tvoid |] (@tptsto σ ty q p v).
    Global Existing Instance tptsto_nonvoid.

    (** this states that the pointer is a pointer to the given type,
        this is persistent. this implies,
        - the address is not null
        - the address is properly aligned (if it exists in memory)
     *)
    Parameter type_ptr: forall {resolve : genv} (c: type), ptr -> mpred.
    Axiom type_ptr_persistent : forall σ p ty,
      Persistent (type_ptr (resolve:=σ) ty p).
    Global Existing Instance type_ptr_persistent.

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
    (** cpp2v-core#194: [Fractional], [AsFractional], [Timeless]? *)
    (** cpp2v-core#194: The fraction is valid? Agreement? *)

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

      Global Existing Instances
        code_at_persistent code_at_affine code_at_timeless
        method_at_persistent method_at_affine method_at_timeless
        ctor_at_persistent ctor_at_affine ctor_at_timeless
        dtor_at_persistent dtor_at_affine dtor_at_timeless.
    End with_genv.

    Parameter encodes : forall {σ:genv} (t : type) (v : val) (vs : list runtime_val), mpred.

    (** Virtual points-to. *)
    (** [vbyte va rv q] exposes the access to the underlying byte value, but
      still with the current address space where the address mapping is
      implicity within mpred.
      [vbyte] is an abstraction for the physical machine where the aspect of
      thread-local state is hidden. For example, the abstraction will model
      virtual-physical address translation, as well as weak memory behaviors of
      physical memory.
      The logic of [mpred] will be enriched orthogonally to have modalities and
      axioms to support lower-level interactions with such feature. For example,
      there will be a theory to support transferring ownership of physical bytes
      across address spaces. *)
    Parameter vbyte : forall (va : vaddr) (rv : runtime_val) (q : Qp), mpred.

    Axiom vbyte_fractional : forall va rv, Fractional (vbyte va rv).
    Axiom vbyte_timeless : forall va rv q, Timeless (vbyte va rv q).
    Global Existing Instances vbyte_fractional vbyte_timeless.
    (** cpp2v-core#194: The fraction is valid, agreement? *)

    Definition vbytes (a : vaddr) (vs : list runtime_val) (q : Qp) : mpred :=
      [∗list] o ↦ v ∈ vs, (vbyte (a+N.of_nat o)%N v q).

    (** Physical representation of pointers. *)
    (** [pinned_ptr va p] states that the abstract pointer [p] is tied to a
      virtual address [va].
      [pinned_ptr] will only hold on pointers that are associated to addresses,
      but other pointers exist. *)
    Parameter pinned_ptr : vaddr -> ptr -> mpred.
    Axiom pinned_ptr_persistent : forall va p, Persistent (pinned_ptr va p).
    Axiom pinned_ptr_affine : forall va p, Affine (pinned_ptr va p).
    Axiom pinned_ptr_timeless : forall va p, Timeless (pinned_ptr va p).
    Axiom pinned_ptr_unique : forall va va' p,
        Observe2 [| va = va' |] (pinned_ptr va p) (pinned_ptr va' p).
    Global Existing Instance pinned_ptr_unique.

    (* A pinned ptr allows access to the underlying bytes. The fupd is needed to
      update the C++ abstraction's ghost state. *)
    Axiom pinned_ptr_borrow : forall {σ} ty p v va (M: coPset),
      @tptsto σ ty 1 p v ** pinned_ptr va p ** [| p <> nullptr |] |--
        |={M}=> Exists vs, @encodes σ ty v vs ** vbytes va vs 1 **
                (Forall v' vs', @encodes  σ ty v' vs' -* vbytes va vs' 1 -*
                                |={M}=> @tptsto σ ty 1 p v').

    Axiom provides_storage_pinned_ptr : forall res newp aty va,
       provides_storage res newp aty ** pinned_ptr va res |-- pinned_ptr va newp.

    Global Existing Instances
      pinned_ptr_persistent pinned_ptr_affine pinned_ptr_timeless.
  End with_cpp.

End CPP_LOGIC.

Declare Module LC : CPP_LOGIC_CLASS.
Declare Module L : CPP_LOGIC LC PTRS_FULL_AXIOM.
Export LC L.

(* Pointer axioms. XXX Not modeled for now. *)
Module Type VALID_PTR_AXIOMS.
  Section with_cpp.
    Context `{cpp_logic} {σ : genv}.

    Axiom invalid_ptr_invalid :
      valid_ptr invalid_ptr |-- False.

    Axiom valid_ptr_field : ∀ p f,
      valid_ptr (p .., o_field σ f) |-- valid_ptr p.
    Axiom valid_ptr_sub : ∀ p ty i,
      0 <= i -> valid_ptr (p .., o_sub σ ty i) |-- valid_ptr p.
    Axiom valid_ptr_base : ∀ p base derived,
      valid_ptr (p .., o_base σ derived base) |-- valid_ptr p.
    Axiom valid_ptr_derived : ∀ p base derived,
      valid_ptr (p .., o_derived σ base derived) |-- valid_ptr p.

    Axiom o_sub_sub : ∀ p ty n1 n2,
      valid_ptr (p .., o_sub σ ty n1) |--
      [! p .., o_sub σ ty n1 .., o_sub σ ty n2 = p .., o_sub σ ty (n1 + n2) !]%ptr.

    (* We're ignoring virtual inheritance here, since we have no plans to
    support it for now, but this might hold there too. *)
    Axiom o_base_derived : forall p base derived,
      valid_ptr (p .., o_base σ derived base) |--
      [! p .., o_base σ derived base .., o_derived σ base derived = p !]%ptr.

    Axiom o_derived_base : forall p base derived,
      valid_ptr (p .., o_derived σ base derived) |--
      [! p .., o_derived σ base derived .., o_base σ derived base = p !]%ptr.

    (* Without the validity premise to the cancellation axioms ([o_sub_sub],
      [o_base_derived], [o_derived_base]) we could incorrectly deduce that
      [valid_ptr p] entails [valid_ptr (p ., o_base derived base ., o_derived
      base derived)] which entails [valid_ptr (p ., o_base derived base)].
    *)
  End with_cpp.
End VALID_PTR_AXIOMS.
Declare Module Export VALID_PTR : VALID_PTR_AXIOMS.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  Global Instance tptsto_flip_mono :
    Proper (flip genv_leq ==> eq ==> eq ==> eq ==> eq ==> flip (⊢))
      (@tptsto _ Σ).
  Proof. repeat intro. exact: tptsto_mono. Qed.

  Global Instance tptsto_as_fractional {σ} ty q a v :
    AsFractional (tptsto (σ := σ) ty q a v) (λ q, tptsto (σ := σ) ty q a v) q.
  Proof. split. done. apply _. Qed.

  Global Instance tptsto_observe_nonnull {σ} t q p v :
    Observe [| p <> nullptr |] (tptsto (σ := σ) t q p v).
  Proof.
    apply: observe_intro.
    destruct (ptr_eq_dec p nullptr); subst; last by eauto.
    rewrite {1}tptsto_nonnull. exact: bi.False_elim.
  Qed.

  Global Instance vbyte_as_fractional a v q :
    AsFractional (vbyte a v q) (vbyte a v) q.
  Proof. exact: Build_AsFractional. Qed.

  Global Instance vbytes_fractional a vs : Fractional (vbytes a vs).
  Proof. apply fractional_big_sepL=>o v. apply vbyte_fractional. Qed.
  Global Instance vbytes_as_fractional a vs q :
    AsFractional (vbytes a vs q) (vbytes a vs) q.
  Proof. exact: Build_AsFractional. Qed.
  (** cpp2v-core#194: The fraction is valid, agreement? *)

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
