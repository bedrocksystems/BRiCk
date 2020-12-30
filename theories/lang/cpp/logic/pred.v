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
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.fancy_updates.
Require Import iris.base_logic.lib.own.
Require Import iris.base_logic.lib.cancelable_invariants.

Require Export bedrock.lang.bi.prelude.
Require Export bedrock.lang.bi.observe.
Export ChargeNotation.

From bedrock.lang.cpp Require Import ast semantics.

Variant validity_type : Set := Strict | Relaxed.

Implicit Types (vt : validity_type) (σ resolve : genv).

(* Namespace for the invariants of the C++ abstraction's ghost state. *)
Definition pred_ns : namespace := (nroot .@ "bedrock" .@ "lang" .@ "cpp_logic")%bs.

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

Module Type CPP_LOGIC (Import CC : CPP_LOGIC_CLASS)
  (Import PTR : PTRS_FULL) (PTRI : PTR_INTERNAL PTR).

  Implicit Types (p : ptr).

  (* TODO: unify with [raw_byte]. This should just be machine bytes. See also
    cpp2v-core#135. *)
  Parameter runtime_val : Type.

  (* XXX why does this not work in the module type. *)
  Bind Scope ptr_scope with ptr.
  Bind Scope offset_scope with offset.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    (**
      [_valid_ptr strict p] is a persistent assertion that [p] is a _valid pointer_, that is:
      - [p] can be [nullptr]
      - [p] can point to a function or a (possibly dead) object [o]
      - if [strict = false], [p] can be past-the-end of a (possibly dead) object [o].
      In particular, [_valid_ptr strict p] prevents producing [p] by incrementing
      past-the-end pointers into overflow territory.

      Our definition of validity includes all cases in which a pointer is not
      an _invalid pointer value_ in the sense of the standard
      (https://eel.is/c++draft/basic.compound#3.1), except that our concept
      of validity survives deallocation; a pointer is only valid according to
      the standard (or "standard-valid") if it is _both_ valid ([_valid_ptr
      strict p]) and live ([live_ptr p]); we require both where needed (e.g.
      [eval_ptr_eq]).

      When the duration of a region of storage ends [note 1], contained objects [o] go
      from live to dead, and pointers to such objects become _dangling_, or
      _invalid pointer values_ (https://eel.is/c++draft/basic.compound#3.1);
      this is called _pointer zapping_ [note 1].
      In our semantics, that only consumes the non-persistent predicate
      [live_ptr p], not the persistent predicate [_valid_ptr strict p].

      Following Cerberus, [live_alloc_id] tracks liveness per allocation
      ID (see comments for [ptr]), and [live_ptr] is derived from it. Hence,
      a pointer [p] past-the-end of [o] also becomes dangling when [o] is
      deallocated.

      It's implementation-defined whether invalid pointer values are
      (non-copyable) trap representations. Instead, we restrict to
      implementations where dangling pointers are not trap representations
      (which is allowed, since this choice is implementation-defined) and
      pointer zapping does not actually clear pointers.

      [Note 1]. See https://eel.is/c++draft/basic.stc.general#4 and
      https://eel.is/c++draft/basic.compound#3.1 for C++, and
      http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2369.pdf for
      discussion in the context of the C standard.
    *)
    Parameter _valid_ptr : forall (vt : validity_type), ptr -> mpred.
    (* strict validity (not past-the-end) *)
    Notation strict_valid_ptr := (_valid_ptr Strict).
    (* validity (past-the-end allowed) *)
    Notation valid_ptr := (_valid_ptr Relaxed).

    Axiom _valid_ptr_persistent : forall b p, Persistent (_valid_ptr b p).
    Axiom _valid_ptr_affine : forall b p, Affine (_valid_ptr b p).
    Axiom _valid_ptr_timeless : forall b p, Timeless (_valid_ptr b p).
    Global Existing Instances _valid_ptr_persistent _valid_ptr_affine _valid_ptr_timeless.

    Axiom _valid_ptr_nullptr : forall b, |-- _valid_ptr b nullptr.
    Axiom strict_valid_relaxed : forall p,
      strict_valid_ptr p |-- valid_ptr p.

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

    Axiom tptsto_nonvoid : forall {σ} ty (q : Qp) p v,
      Observe [| ty <> Tvoid |] (@tptsto σ ty q p v).
    Global Existing Instance tptsto_nonvoid.

    (** The allocation is alive. Neither persistent nor fractional.
      See https://eel.is/c++draft/basic.stc.general#4 and
      https://eel.is/c++draft/basic.compound#3.1.
    *)
    Parameter live_alloc_id : alloc_id -> mpred.
    Axiom live_alloc_id_timeless : forall aid, Timeless (live_alloc_id aid).
    Global Existing Instance live_alloc_id_timeless.

    Axiom valid_ptr_alloc_id : forall p,
      valid_ptr p |-- [| is_Some (ptr_alloc_id p) |].

    (** This pointer is from a live allocation; this does not imply
    [_valid_ptr], because even overflowing offsets preserve the allocation ID.
    *)
    Definition live_ptr (p : ptr) :=
      default False%I (live_alloc_id <$> ptr_alloc_id p).

    (** We consider [nullptr] as live, following Krebbers, as a way to
    simplify stating rules for pointer comparison. *)
    Axiom nullptr_live : |-- live_ptr nullptr.

    Axiom tptsto_live : forall {σ} ty (q : Qp) p v,
      @tptsto σ ty q p v |-- live_ptr p ** True.

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
        @identity σ this (Some mdc) 1 p |-- |={↑pred_ns}=> @identity σ this None 1 p.

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

      Axiom code_at_live   : forall f p,   code_at f p |-- live_ptr p.
      Axiom method_at_live : forall f p, method_at f p |-- live_ptr p.
      Axiom ctor_at_live   : forall f p,   ctor_at f p |-- live_ptr p.
      Axiom dtor_at_live   : forall f p,   dtor_at f p |-- live_ptr p.
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
    Axiom pinned_ptr_eq : forall va p,
      pinned_ptr va p -|- [| pinned_ptr_pure va p |] ** valid_ptr p.
    Axiom pinned_ptr_unique : forall va va' p,
        Observe2 [| va = va' |] (pinned_ptr va p) (pinned_ptr va' p).
    Global Existing Instance pinned_ptr_unique.
    Axiom pinned_ptr_null : |-- pinned_ptr 0 nullptr.

    (* A pinned ptr allows access to the underlying bytes. The fupd is needed to
      update the C++ abstraction's ghost state. *)
    Axiom pinned_ptr_borrow : forall {σ} ty p v va,
      @tptsto σ ty 1 p v ** pinned_ptr va p |--
        |={↑pred_ns}=> Exists vs, @encodes σ ty v vs ** vbytes va vs 1 **
                (Forall v' vs', @encodes σ ty v' vs' -* vbytes va vs' 1 -*
                                |={↑pred_ns}=> @tptsto σ ty 1 p v').

    Axiom offset_pinned_ptr : forall resolve o n va p,
      PTRI.eval_offset resolve o = Some n ->
      valid_ptr (p .., o) |--
      pinned_ptr va p -* pinned_ptr (Z.to_N (Z.of_N va + n)) (p .., o).

    Axiom provides_storage_same_address : forall base newp ty,
      provides_storage base newp ty |-- [| same_address base newp |].
    Axiom provides_storage_pinned_ptr : forall res newp aty va,
       provides_storage res newp aty ** pinned_ptr va res |-- pinned_ptr va newp.

    Global Existing Instances
      pinned_ptr_persistent pinned_ptr_affine pinned_ptr_timeless.

    (** [aligned_ptr] states that the pointer (if it exists in memory) has
    the given alignment. This is persistent.
     *)
    Parameter aligned_ptr : forall (n : N) (p : ptr), mpred.
    Axiom aligned_ptr_persistent : forall n p, Persistent (aligned_ptr n p).
    Axiom aligned_ptr_affine : forall n p, Affine (aligned_ptr n p).
    Axiom aligned_ptr_timeless : forall n p, Timeless (aligned_ptr n p).
    Global Existing Instances aligned_ptr_persistent aligned_ptr_affine aligned_ptr_timeless.

    Axiom pinned_ptr_aligned_divide : forall va n p,
      pinned_ptr va p ⊢
      aligned_ptr n p ∗-∗ [| (n | va)%N |].

    (**
      [type_ptr {resolve := resolve} ty p] asserts that [p] points to
      a (possibly dead) object of type [ty] (in environment
      [resolve]), as defined by https://eel.is/c++draft/basic.compound#3.1.

      This implies:
      - the pointer is strictly valid [type_ptr_strict_valid], and
        "p + 1" is also valid (while possibly past-the-end) [type_ptr_valid_plus_one].
      - the pointer is not null [type_ptr_nonnull]
      - the pointer is properly aligned [type_ptr_aligned]

      [type_ptr] is persistent and survives deallocation of the pointed-to
      object, like [_valid_ptr].

      TODO: before a complete object is fully initialized,
      what [type_ptr] facts are available? For now, we only use [type_ptr]
      for fully initialized objects.
      Consider http://eel.is/c++draft/basic.memobj#basic.life, especially
      from http://eel.is/c++draft/basic.memobj#basic.life-1 to
      http://eel.is/c++draft/basic.memobj#basic.life-4.
     *)
    Parameter type_ptr : forall {resolve : genv} (c: type), ptr -> mpred.
    Axiom type_ptr_persistent : forall σ p ty,
      Persistent (type_ptr (resolve:=σ) ty p).
    Axiom type_ptr_affine : forall σ p ty,
      Affine (type_ptr (resolve:=σ) ty p).
    Axiom type_ptr_timeless : forall σ p ty,
      Timeless (type_ptr (resolve:=σ) ty p).
    Global Existing Instances type_ptr_persistent type_ptr_affine type_ptr_timeless.

    Axiom type_ptr_aligned : forall σ ty p,
      type_ptr (resolve := σ) ty p |--
      Exists align, [| @align_of σ ty = Some align |] ** aligned_ptr align p.

    Axiom type_ptr_off_nonnull : forall {σ ty p o},
      type_ptr ty (p .., o) |-- [| p <> nullptr |].

    Axiom tptsto_type_ptr : forall (σ : genv) ty q p v,
      Observe (type_ptr ty p) (tptsto ty q p v).
    Global Existing Instance tptsto_type_ptr.

    (* All objects in the C++ abstract machine have a size

       NOTE to support un-sized objects, we can simply say that the [sizeof] operator
            in C++ is only a conservative approximation of the true size of an object.
     *)
    Axiom type_ptr_size : forall σ ty p,
        type_ptr ty p |-- [| is_Some (size_of σ ty) |].

    (**
    Recall that [type_ptr] and [strict_valid_ptr] don't include
    past-the-end pointers... *)
    Axiom type_ptr_strict_valid : forall resolve ty p,
      type_ptr (resolve := resolve) ty p |-- strict_valid_ptr p.
    (** Hence they can be incremented into (possibly past-the-end) valid pointers. *)
    Axiom type_ptr_valid_plus_one : forall resolve ty p,
      type_ptr (resolve := resolve) ty p |-- valid_ptr (p .., o_sub resolve ty 1).
    Axiom type_ptr_nonnull : forall resolve ty p,
      type_ptr (resolve := resolve) ty p |-- [| p <> nullptr |].

    (**
     ** Deducing pointer equalities
     The following axioms, together with [same_address_o_sub_eq], enable going
     from [same_address] (produced by C++ pointer equality) to actual pointer
     equalities.
     *)

    (** Pointer equality with [nullptr] is easy, as long as your pointer is valid.
     Validity is necessary: the C++ expression [(char * )p - (uintptr_t) p]
     produces an invalid pointer with address 0, which is not [nullptr] because
     it preserves the provenance of [p]. *)
    Axiom same_address_eq_null : forall p tv,
      _valid_ptr tv p |--
      [| same_address p nullptr <-> p = nullptr |].

    (**
    [same_address_eq_type_ptr] concludes that two pointers [p1] and [p2] are
    equal if they have the same address, point to live objects [o1] and [o2],
    and have the same (non-uchar) type [ty] with nonzero size.

    Justifying this from the standard is tricky; here's a proof sketch.
    - Because [ty] has "nonzero size" (https://eel.is/c++draft/intro.object#8),
      and we don't support bitfields, we apply the standard:

      > Unless it is a bit-field, an object with nonzero size shall occupy one
        or more bytes of storage, including every byte that is occupied in full
        or in part by any of its subobjects.

    - Because [o1] and [o2] are live, these objects share storage, hence they
      must coincide or one must be nested inside the other
      (https://eel.is/c++draft/intro.object#4); if they coincide, our proof
      is done.
    - Because [ty] is not [unsigned char], neither pointer can provide storage
      for the other (https://eel.is/c++draft/intro.object#3); so one must be a
      subobject of the other.
    - Since [o1] and [o2] have type [ty], and type [ty] has "nonzero size",
      neither of [o1] and [o2] can be a subobject of the other;
      we conjecture is provable from the C++ type system.

    NOTE: we check "nonzero size"
    (https://eel.is/c++draft/basic.memobj#intro.object-8) using [size_of],
    which might incorporate implementation-specific compiler decisions.
    TODO: handle [std::byte] like [unsigned char].
    *)
    Axiom same_address_eq_type_ptr : forall resolve ty p1 p2 n,
      same_address p1 p2 ->
      size_of resolve ty = Some n ->
      (* if [ty = T_uchar], one of these pointer could provide storage for the other. *)
      ty <> T_uchar ->
      (n > 0)%N ->
      type_ptr ty p1 ∧ type_ptr ty p2 ∧ live_ptr p1 ∧ live_ptr p2 ⊢
        |={↑pred_ns}=> [| p1 = p2 |].
  End with_cpp.

End CPP_LOGIC.

Declare Module LC : CPP_LOGIC_CLASS.
Declare Module L : CPP_LOGIC LC PTRS_FULL_AXIOM PTR_INTERNAL_AXIOM.
Export LC L.

(* strict validity (not past-the-end) *)
Notation strict_valid_ptr := (_valid_ptr Strict).
(* validity (past-the-end allowed) *)
Notation valid_ptr := (_valid_ptr Relaxed).


(* Pointer axioms. XXX Not modeled for now. *)
Module Type VALID_PTR_AXIOMS.
  Section with_cpp.
    Context `{cpp_logic} {σ : genv}.

    Axiom invalid_ptr_invalid : forall vt,
      _valid_ptr vt invalid_ptr |-- False.

    (** Justified by [https://eel.is/c++draft/expr.add#4.1]. *)
    Axiom _valid_ptr_nullptr_sub_false : forall vt ty (i : Z) (_ : i <> 0),
      _valid_ptr vt (nullptr .., o_sub σ ty i) |-- False.
    (*
    TODO Controversial; if [f] is the first field, [nullptr->f] or casts relying on
    https://eel.is/c++draft/basic.compound#4 might invalidate this.
    To make this valid, we could ensure our axiomatic semantics produces
    [nullptr] instead of [nullptr ., o_field]. *)
    (* Axiom _valid_ptr_nullptr_field_false : forall vt f,
      _valid_ptr vt (nullptr .., o_field σ f) |-- False. *)

    (* These axioms are named after the predicate in the conclusion. *)
    Axiom strict_valid_ptr_sub : ∀ p ty i vt,
      0 < i -> _valid_ptr vt (p .., o_sub σ ty i) |-- strict_valid_ptr p.
    (* TODO: can we deduce that [p] is strictly valid? *)
    Axiom _valid_ptr_base : ∀ p base derived vt,
      _valid_ptr vt (p .., o_base σ derived base) |-- _valid_ptr vt p.
    (* TODO: can we deduce that [p] is strictly valid? *)
    Axiom _valid_ptr_derived : ∀ p base derived vt,
      _valid_ptr vt (p .., o_derived σ base derived) |-- _valid_ptr vt p.
    (* TODO: can we deduce that [p] is strictly valid? *)
    Axiom _valid_ptr_field : ∀ p f vt,
      _valid_ptr vt (p .., o_field σ f) |-- _valid_ptr vt p.
    (* TODO: Pointers to fields can't be past-the-end, right?
    Except 0-size arrays. *)
    (* Axiom strict_valid_ptr_field : ∀ p f,
      valid_ptr (p .., o_field σ f) |--
      strict_valid_ptr (p .., o_field σ f). *)
    (* TODO: if we add [strict_valid_ptr_field], we can derive
    [_valid_ptr_field] from just [strict_valid_ptr_field] *)
    (* Axiom strict_valid_ptr_field : ∀ p f,
      strict_valid_ptr (p .., o_field σ f) |-- strict_valid_ptr p. *)

    Axiom o_sub_sub : ∀ p ty n1 n2 vt,
      _valid_ptr vt (p .., o_sub σ ty n1) |--
      [! p .., o_sub σ ty n1 .., o_sub σ ty n2 = p .., o_sub σ ty (n1 + n2) !]%ptr.

    (* We're ignoring virtual inheritance here, since we have no plans to
    support it for now, but this might hold there too. *)
    Axiom o_base_derived : forall p base derived,
      strict_valid_ptr (p .., o_base σ derived base) |--
      [! p .., o_base σ derived base .., o_derived σ base derived = p !]%ptr.

    Axiom o_derived_base : forall p base derived,
      strict_valid_ptr (p .., o_derived σ base derived) |--
      [! p .., o_derived σ base derived .., o_base σ derived base = p !]%ptr.

    (* Without the validity premise to the cancellation axioms ([o_sub_sub],
      [o_base_derived], [o_derived_base]) we could incorrectly deduce that
      [valid_ptr p] entails [valid_ptr (p ., o_base derived base ., o_derived
      base derived)] which entails [valid_ptr (p ., o_base derived base)].
    *)

    (* TODO: maybe add a validity of offsets to allow stating this more generally. *)
    Axiom valid_o_sub_size : forall p ty i vt,
      _valid_ptr vt (p .., o_sub σ ty i) |-- [| is_Some (size_of σ ty) |].
  End with_cpp.
End VALID_PTR_AXIOMS.
Declare Module Export VALID_PTR : VALID_PTR_AXIOMS.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* TODO (SEMANTICS):
     set p := p ., (.[ty ! -i])
     ...
     we end up with `_valid_ptr vt p |-- _valid_ptr vt (p ., (.[ty ! -i]))
     which isn't true.

     NOTE: Modify `strict_valid_ptr_sub` and this so that they impose an
       extra pre-condition on the structure of `p` (namely that it doesn't
       have negative offsets(?))

     Paolo: good catch. Maybe the axiom should be that if [p ., (.[ty ! i])] and [p .,
     (.[ty ! j])] are both valid, then everything in between is valid.
     OTOH, `arrayR` exposes stronger reasoning principles, possibly making this
     unnecessary.

     The intended model was that, if [p'] normalizes to [p ., [ ty ! i ]],
     then [valid_ptr p'] implies validity of all pointers from [p] to [p']. As
     you point out, that model doesn't actually justify [strict_valid_ptr_sub].
   *)
  Lemma valid_ptr_sub {σ : genv} p ty i vt :
    0 <= i -> _valid_ptr vt (p .., o_sub σ ty i) |-- _valid_ptr vt p.
  Proof.
    case: i => [|i] Hle; iIntros "V".
    - iDestruct (valid_o_sub_size with "V") as %?.
      by rewrite o_sub_0 // offset_ptr_id.
    - rewrite strict_valid_ptr_sub; last by lia.
      case: vt => //. by rewrite strict_valid_relaxed.
  Qed.

  (** [p] is valid pointer value in the sense of the standard, or
  "standard-valid" (https://eel.is/c++draft/basic.compound#3.1), that is both
  valid (in our sense) and live.

  In particular, [p] is a valid pointer value even when accounting for
  pointer zapping.
  *)
  Definition _valid_live_ptr vt (p : ptr) : mpred :=
    _valid_ptr vt p ∗ live_ptr p.
  Definition valid_live_ptr p : mpred := _valid_ptr Strict p.
  Definition strict_valid_live_ptr p : mpred := _valid_ptr Relaxed p.

  Global Instance tptsto_flip_mono :
    Proper (flip genv_leq ==> eq ==> eq ==> eq ==> eq ==> flip (⊢))
      (@tptsto _ Σ).
  Proof. repeat intro. exact: tptsto_mono. Qed.

  Global Instance tptsto_as_fractional {σ} ty q a v :
    AsFractional (tptsto (σ := σ) ty q a v) (λ q, tptsto (σ := σ) ty q a v) q.
  Proof. exact: Build_AsFractional. Qed.

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

  Definition type_of_spec (fs : function_spec) : type :=
    normalize_type (Tfunction (cc:=fs.(fs_cc)) fs.(fs_return) fs.(fs_arguments)).

  Lemma length_type_of_spec fs1 fs2 :
    type_of_spec fs1 = type_of_spec fs2 →
    length (fs_arguments fs1) = length (fs_arguments fs2).
  Proof.
    destruct fs1, fs2; rewrite /type_of_spec/=; intros [= _ _ Hmap].
    erewrite <-map_length, Hmap.
    by rewrite map_length.
  Qed.

  (* [mpred] implication on [function_spec] *)
  Definition fs_impl (P Q : function_spec) : mpred :=
    [| type_of_spec P = type_of_spec Q |] ∗
    □ ∀ ti vs K, P.(fs_spec) ti vs K -∗ Q.(fs_spec) ti vs K.
  Lemma fs_impl_reflexive P : |-- fs_impl P P.
  Proof. iSplit; auto. Qed.
  Lemma fs_impl_transitive P Q R : fs_impl P Q |-- fs_impl Q R -* fs_impl P R.
  Proof.
    rewrite /fs_impl; iIntros "(-> & #H1) (-> & #H2)".
    iSplit; first done.
    iIntros "!>" (ti vs K) "Y".
    iApply ("H2" with "(H1 Y)").
  Qed.

  Definition fs_entails (P Q : function_spec) : Prop := |-- fs_impl P Q.

  #[global] Instance fs_entails_preorder : PreOrder fs_entails.
  Proof.
    split; rewrite /fs_entails.
    - intro x. exact: fs_impl_reflexive.
    - intros ? ? ? H1 H2. by iApply (fs_impl_transitive).
  Qed.
  #[global] Instance : RewriteRelation fs_entails := {}.

  (* [mpred] bi-impliciation on [function_spec] *)
  Definition fs_equiv (P Q : function_spec) : mpred :=
    [| type_of_spec P = type_of_spec Q |] ∗
    □ ∀ ti vs K, P.(fs_spec) ti vs K ∗-∗ Q.(fs_spec) ti vs K.
  Lemma fs_equiv_split P Q : fs_equiv P Q -|- fs_impl P Q ** fs_impl Q P.
  Proof.
    rewrite /fs_equiv /fs_impl; iSplit.
    - iIntros "(-> & #W)"; repeat iSplit => //;
      iIntros "!>" (???) "A"; iApply ("W" with "A").
    - iIntros "((-> & #W1) & (_ & #W2))".
      iSplit => //; iIntros "!>" (???); iSplit;
        [by iApply "W1" | by iApply "W2"].
  Qed.

  Lemma fs_equiv_reflexive P : |-- fs_equiv P P.
  Proof. rewrite fs_equiv_split -fs_impl_reflexive; by iSplit. Qed.
  Lemma fs_equiv_symmetric P Q : fs_equiv Q P |-- fs_equiv P Q.
  Proof. rewrite !fs_equiv_split. iDestruct 1 as "($ & $)". Qed.
  Lemma fs_equiv_transitive P Q R : fs_equiv P Q |-- fs_equiv Q R -* fs_equiv P R.
  Proof.
    rewrite !fs_equiv_split; iIntros "#(PQ & QP) #(QR & RQ)".
    by iSplit; iApply fs_impl_transitive.
  Qed.

  (* Equivalence relation on [function_spec] *)
  #[global] Instance function_spec_equiv : Equiv function_spec :=
    fun P Q => |-- fs_equiv P Q.

  Lemma function_spec_equiv_split P Q : P ≡ Q ↔ fs_entails P Q /\ fs_entails Q P.
  Proof.
    rewrite /fs_entails /equiv /function_spec_equiv fs_equiv_split; split.
    { by intros H; split; iDestruct H as "[??]". }
    { intros [H1 H2]. iDestruct H1 as "$". iDestruct H2 as "$". }
  Qed.

  #[global] Instance function_spec_equivalence : Equivalence (≡@{function_spec}).
  Proof.
    unfold equiv, function_spec_equiv. constructor; red; intros.
    - by iApply fs_equiv_reflexive.
    - by iApply fs_equiv_symmetric.
    - by iApply fs_equiv_transitive.
  Qed.

  Lemma pinned_ptr_type_divide_1 va n σ p ty
    (Hal : align_of (resolve := σ) ty = Some n) :
    type_ptr (resolve := σ) ty p ⊢ pinned_ptr va p -∗ [| (n | va)%N |].
  Proof.
    rewrite type_ptr_aligned Hal /=. iDestruct 1 as (? [= <-]) "A". iIntros "P".
    iApply (pinned_ptr_aligned_divide with "P A").
  Qed.

  (* Just wrappers. *)
  Lemma valid_ptr_nullptr : |-- valid_ptr nullptr.
  Proof. exact: _valid_ptr_nullptr. Qed.
  Lemma strict_valid_ptr_nullptr : |-- strict_valid_ptr nullptr.
  Proof. exact: _valid_ptr_nullptr. Qed.

  (** We can lift validity entailments through [Observe] (using
  [Observe_mono]. These are not instances, to avoid causing slowdowns in
  proof search. *)
  Lemma observe_strict_valid_valid
    `(Hobs : !Observe (strict_valid_ptr p) P) : Observe (valid_ptr p) P.
  Proof. by rewrite -strict_valid_relaxed. Qed.

  Context (σ : genv).
  Lemma observe_type_ptr_strict_valid
    `(Hobs : !Observe (type_ptr ty p) P) : Observe (strict_valid_ptr p) P.
  Proof. by rewrite -type_ptr_strict_valid. Qed.

  Lemma observe_type_ptr_valid_plus_one
    `(Hobs : !Observe (type_ptr ty p) P) : Observe (valid_ptr (p .., o_sub σ ty 1)) P.
  Proof. by rewrite -type_ptr_valid_plus_one. Qed.
End with_cpp.
