(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** this file defines the core logic (called [mpred]) that we use
    for C++.

    known issues:
    - currently the logic is sequentially consistent
    - the memory model is simplified from the standard C++ memory
      model.
 *)
From bedrock.lang Require Import prelude.base bi.prelude.
From bedrock.lang.cpp.logic Require Export mpred rep.

Require Import bedrock.lang.prelude.base.
Require Export bedrock.lang.prelude.addr.

From iris.base_logic.lib Require Export iprop.
(* TODO: ^^ only needed to export uPredI, should be removed. *)
Require Import iris.bi.monpred.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Require Import bedrock.lang.bi.cancelable_invariants.

Require Export bedrock.lang.bi.prelude.
Require Export bedrock.lang.bi.observe.
Export ChargeNotation.

From bedrock.lang.cpp.syntax Require Import
     names
     types
     translation_unit.
From bedrock.lang.cpp Require Import semantics.values.

Variant validity_type : Set := Strict | Relaxed.

Implicit Types (vt : validity_type) (σ resolve : genv).
Implicit Types (n : N) (z : Z).

(* Namespace for the invariants of the C++ abstraction's ghost state. *)
Definition pred_ns : namespace := (nroot .@ "bedrock" .@ "lang" .@ "cpp_logic")%bs.

Module Type CPP_LOGIC (Import CC : CPP_LOGIC_CLASS) (Import INTF : FULL_INTF).

  Implicit Types (p : ptr).

  (* XXX why does this not work in the module type. *)
  Bind Scope ptr_scope with ptr.
  Bind Scope offset_scope with offset.

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    (**
      [_valid_ptr vt p] is a persistent assertion that [p] is a _valid pointer_, that is:
      - [p] can be [nullptr]
      - [p] can point to a function or a (possibly dead) object [o]
      - if [vt = Relaxed], [p] can be past-the-end of a (possibly dead) object [o].
      In particular, [_valid_ptr vt p] prevents producing [p] by incrementing
      past-the-end pointers into overflow territory.

      Our definition of validity includes all cases in which a pointer is not
      an _invalid pointer value_ in the sense of the standard
      (https://eel.is/c++draft/basic.compound#3.1), except that our concept
      of validity survives deallocation; a pointer is only valid according to
      the standard (or "standard-valid") if it is _both_ valid ([_valid_ptr
      vt p]) and live ([live_ptr p]); we require both where needed (e.g.
      [eval_ptr_eq]).

      When the duration of a region of storage ends [note 1], contained objects [o] go
      from live to dead, and pointers to such objects become _dangling_, or
      _invalid pointer values_ (https://eel.is/c++draft/basic.compound#3.1);
      this is called _pointer zapping_ [note 1].
      In our semantics, that only consumes the non-persistent predicate
      [live_ptr p], not the persistent predicate [_valid_ptr vt p].

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
    Axiom strict_valid_valid : forall p,
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
      Observe [| q ≤ 1 |]%Qp (@tptsto σ t q p v).
    Global Existing Instance tptsto_frac_valid.

    Axiom tptsto_agree : forall {σ} ty q1 q2 p v1 v2,
      Observe2 [| val_related σ ty v1 v2 |]
               (@tptsto σ ty q1 p v1)
               (@tptsto σ ty q2 p v2).
    Global Existing Instances tptsto_agree.

    (* TODO (JH/PG): Add in a proper instance using this which allows us to rewrite
         `val_related` values within `tptsto`s.

         <https://gitlab.com/bedrocksystems/cpp2v-core/-/merge_requests/377#note_530611061> *)
    Axiom tptsto_val_related_transport : forall {σ} ty q p v1 v2,
        [| val_related σ ty v1 v2 |] |-- @tptsto σ ty q p v1 -* @tptsto σ ty q p v2.

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
    Axiom identity_fractional : forall σ this mdc p, Fractional (λ q, identity this mdc q p).
    Axiom identity_timeless : forall σ this mdc q p, Timeless (identity this mdc q p).
    Global Existing Instances identity_fractional identity_timeless.

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

      Axiom code_at_valid   : forall f p,   code_at f p |-- valid_ptr p.
      Axiom method_at_valid : forall f p, method_at f p |-- valid_ptr p.
      Axiom ctor_at_valid   : forall f p,   ctor_at f p |-- valid_ptr p.
      Axiom dtor_at_valid   : forall f p,   dtor_at f p |-- valid_ptr p.
    End with_genv.

    Axiom offset_pinned_ptr_pure : forall σ o z va p,
      eval_offset σ o = Some z ->
      pinned_ptr_pure va p ->
      valid_ptr (p .., o) |--
      [| pinned_ptr_pure (Z.to_N (Z.of_N va + z)) (p .., o) |].

    Axiom offset_inv_pinned_ptr_pure : forall σ o z va p,
      eval_offset σ o = Some z ->
      pinned_ptr_pure va (p .., o) ->
      valid_ptr (p .., o) |--
      [| 0 <= Z.of_N va - z |]%Z **
      [| pinned_ptr_pure (Z.to_N (Z.of_N va - z)) p |].

    Axiom provides_storage_same_address : forall storage_ptr obj_ptr ty,
      Observe [| same_address storage_ptr obj_ptr |] (provides_storage storage_ptr obj_ptr ty).

    Axiom provides_storage_valid_storage_ptr : forall storage_ptr obj_ptr aty,
      Observe (valid_ptr storage_ptr) (provides_storage storage_ptr obj_ptr aty).
    Axiom provides_storage_valid_obj_ptr : forall storage_ptr obj_ptr aty,
      Observe (valid_ptr obj_ptr) (provides_storage storage_ptr obj_ptr aty).

    Global Existing Instances provides_storage_same_address
      provides_storage_valid_storage_ptr provides_storage_valid_obj_ptr.

    (**
    [exposed_aid aid] states that the storage instance identified by [aid] is
    "exposed" [1]. This enables int2ptr casts to produce pointers into this
    storage instance.

    [1] We use "exposed" in the sense defined by the N2577 draft C standard
    (http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2577.pdf).
    See https://dl.acm.org/doi/10.1145/3290380 for an introduction.
    *)
    Parameter exposed_aid : alloc_id -> mpred.
    Axiom exposed_aid_persistent : forall aid, Persistent (exposed_aid aid).
    Axiom exposed_aid_affine : forall aid, Affine (exposed_aid aid).
    Axiom exposed_aid_timeless : forall aid, Timeless (exposed_aid aid).

    Axiom exposed_aid_null_alloc_id : |-- exposed_aid null_alloc_id.

    Global Existing Instances
      exposed_aid_persistent exposed_aid_affine exposed_aid_timeless.

    (**
      [type_ptr {resolve := resolve} ty p] asserts that [p] points to
      a (possibly dead) object of type [ty] (in environment
      [resolve]), as defined by https://eel.is/c++draft/basic.compound#3.1.

      This implies:
      - the pointer is strictly valid [type_ptr_strict_valid], and
        "p + 1" is also valid (while possibly past-the-end) [type_ptr_valid_plus_one].
      - the pointer is not null [type_ptr_nonnull]
      - the pointer is properly aligned [type_ptr_aligned_pure]

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
      Persistent (type_ptr ty p).
    Axiom type_ptr_affine : forall σ p ty,
      Affine (type_ptr ty p).
    Axiom type_ptr_timeless : forall σ p ty,
      Timeless (type_ptr ty p).
    Global Existing Instances type_ptr_persistent type_ptr_affine type_ptr_timeless.

    Axiom type_ptr_aligned_pure : forall σ ty p,
      type_ptr ty p |-- [| aligned_ptr_ty ty p |].

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
      type_ptr ty p |-- strict_valid_ptr p.
    (** Hence they can be incremented into (possibly past-the-end) valid pointers. *)
    Axiom type_ptr_valid_plus_one : forall resolve ty p,
      type_ptr ty p |-- valid_ptr (p .., o_sub resolve ty 1).
    Axiom type_ptr_nonnull : forall resolve ty p,
      type_ptr ty p |-- [| p <> nullptr |].

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

Declare Module L : CPP_LOGIC LC FULL_INTF_AXIOM.
Export mpred.LC L.

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

    (** These axioms are named after the predicate in the conclusion. *)

    (**
    TODO: The intended proof of [strict_valid_ptr_sub] assumes that, if [p']
    normalizes to [p ., [ ty ! i ]], then [valid_ptr p'] is defined to imply
    validity of all pointers from [p] to [p'].

    Note that `arrR` exposes stronger reasoning principles, but this might still be useful.
    *)
    Axiom strict_valid_ptr_sub : ∀ (i j k : Z) p ty vt1 vt2,
      (i <= j < k)%Z ->
      _valid_ptr vt1 (p .., o_sub σ ty i) |--
      _valid_ptr vt2 (p .., o_sub σ ty k) -* strict_valid_ptr (p .., o_sub σ ty j).

    (** XXX: this axiom is convoluted but
    TODO: The intended proof of [strict_valid_ptr_field_sub] (and friends) is that
    (1) if [p'] normalizes to [p'' ., [ ty ! i ]], then [valid_ptr p'] implies
    [valid_ptr p''].
    (2) [p .., o_field σ f .., o_sub σ ty i] will normalize to [p .., o_field
    σ f .., o_sub σ ty i], without cancellation.
    *)
    Axiom strict_valid_ptr_field_sub : ∀ p ty (i : Z) f vt,
      (0 < i)%Z ->
      _valid_ptr vt (p .., o_field σ f .., o_sub σ ty i) |-- strict_valid_ptr (p .., o_field σ f).

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

    (* We're ignoring virtual inheritance here, since we have no plans to
    support it for now, but this might hold there too. *)
    Axiom o_base_derived : forall p base derived,
      strict_valid_ptr (p .., o_base σ derived base) |--
      [| p .., o_base σ derived base .., o_derived σ base derived = p |].

    Axiom o_derived_base : forall p base derived,
      strict_valid_ptr (p .., o_derived σ base derived) |--
      [| p .., o_derived σ base derived .., o_base σ derived base = p |].

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

Section pinned_ptr_def.
  Context `{Σ : cpp_logic}.

  (* Just wrappers. *)
  Lemma valid_ptr_nullptr : |-- valid_ptr nullptr.
  Proof. exact: _valid_ptr_nullptr. Qed.
  Lemma strict_valid_ptr_nullptr : |-- strict_valid_ptr nullptr.
  Proof. exact: _valid_ptr_nullptr. Qed.

  Definition exposed_ptr_def p : mpred :=
    valid_ptr p ** ∃ aid, [| ptr_alloc_id p = Some aid |] ** exposed_aid aid.
  Definition exposed_ptr_aux : seal exposed_ptr_def. Proof. by eexists. Qed.
  Definition exposed_ptr := exposed_ptr_aux.(unseal).
  Definition exposed_ptr_eq : exposed_ptr = _ := exposed_ptr_aux.(seal_eq).

  Global Instance exposed_ptr_persistent p : Persistent (exposed_ptr p).
  Proof. rewrite exposed_ptr_eq. apply _. Qed.
  Global Instance exposed_ptr_affine p : Affine (exposed_ptr p).
  Proof. rewrite exposed_ptr_eq. apply _. Qed.
  Global Instance exposed_ptr_timeless p : Timeless (exposed_ptr p).
  Proof. rewrite exposed_ptr_eq. apply _. Qed.
  Global Instance exposed_ptr_valid p :
    Observe (valid_ptr p) (exposed_ptr p).
  Proof. rewrite exposed_ptr_eq. apply _. Qed.

  Lemma exposed_ptr_nullptr : |-- exposed_ptr nullptr.
  Proof.
    rewrite exposed_ptr_eq /exposed_ptr_def ptr_alloc_id_nullptr.
    iDestruct valid_ptr_nullptr as "$". iExists _.
    by iDestruct exposed_aid_null_alloc_id as "$".
  Qed.

  Lemma offset_exposed_ptr p o :
    valid_ptr (p .., o) |-- exposed_ptr p -* exposed_ptr (p .., o).
  Proof.
    rewrite exposed_ptr_eq /exposed_ptr_def.
    iIntros "#V' #[V E]". iDestruct (valid_ptr_alloc_id with "V'") as %?.
    iFrame "V'". by rewrite ptr_alloc_id_offset.
  Qed.

  Lemma offset2_exposed_ptr p o1 o2 :
    valid_ptr (p .., o2) |-- exposed_ptr (p .., o1) -* exposed_ptr (p .., o2).
  Proof.
    rewrite exposed_ptr_eq /exposed_ptr_def.
    iIntros "#V2 #[V1 E]"; iFrame "V2".
    iDestruct (valid_ptr_alloc_id with "V1") as %?.
    iDestruct (valid_ptr_alloc_id with "V2") as %?.
    by rewrite ptr_alloc_id_offset // ptr_alloc_id_offset.
  Qed.

  Lemma offset_inv_exposed_ptr p o :
    valid_ptr p |-- exposed_ptr (p .., o) -* exposed_ptr p.
  Proof. rewrite -{1 3}(offset_ptr_id p). apply offset2_exposed_ptr. Qed.

  (** Physical representation of pointers. *)
  (** [pinned_ptr va p] states that the abstract pointer [p] is tied to a
    virtual address [va].
    [pinned_ptr] will only hold on pointers that are associated to addresses,
    but other pointers exist. *)
  Definition pinned_ptr_def (va : vaddr) (p : ptr) : mpred :=
    [| pinned_ptr_pure va p |] ** exposed_ptr p.
  Definition pinned_ptr_aux : seal pinned_ptr_def. Proof. by eexists. Qed.
  Definition pinned_ptr := pinned_ptr_aux.(unseal).
  Definition pinned_ptr_eq : pinned_ptr = _ := pinned_ptr_aux.(seal_eq).

  Global Instance pinned_ptr_persistent va p : Persistent (pinned_ptr va p).
  Proof. rewrite pinned_ptr_eq. apply _. Qed.
  Global Instance pinned_ptr_affine va p : Affine (pinned_ptr va p).
  Proof. rewrite pinned_ptr_eq. apply _. Qed.
  Global Instance pinned_ptr_timeless va p : Timeless (pinned_ptr va p).
  Proof. rewrite pinned_ptr_eq. apply _. Qed.

  Lemma pinned_ptr_intro p va :
    pinned_ptr_pure va p -> exposed_ptr p |-- pinned_ptr va p.
  Proof. rewrite pinned_ptr_eq /pinned_ptr_def. by iIntros (?) "$". Qed.

  Lemma pinned_ptr_change_va p va va' :
    pinned_ptr_pure va p -> pinned_ptr va' p |-- pinned_ptr va p.
  Proof. rewrite pinned_ptr_eq /pinned_ptr_def. by iIntros (?) "(_ & $)". Qed.

  Global Instance pinned_ptr_pinned_ptr_pure va p :
    Observe [| pinned_ptr_pure va p |] (pinned_ptr va p).
  Proof. rewrite pinned_ptr_eq. apply _. Qed.

  Global Instance pinned_ptr_valid va p :
    Observe (valid_ptr p) (pinned_ptr va p).
  Proof. rewrite pinned_ptr_eq. apply _. Qed.

  (** Just a corollary of [provides_storage_same_address] in the style of
  [provides_storage_pinned_ptr]. *)
  Lemma provides_storage_pinned_ptr_pure {storage_ptr obj_ptr aty va} :
    pinned_ptr_pure va storage_ptr ->
    provides_storage storage_ptr obj_ptr aty |-- [| pinned_ptr_pure va obj_ptr |].
  Proof. rewrite provides_storage_same_address. by iIntros (HP <-). Qed.
End pinned_ptr_def.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma same_address_bool_null p tv :
    _valid_ptr tv p |--
    [| same_address_bool p nullptr = bool_decide (p = nullptr) |].
  Proof. rewrite same_address_eq_null; iIntros "!%". apply bool_decide_iff. Qed.

  Lemma valid_ptr_nonnull_nonzero p :
    p <> nullptr ->
    valid_ptr p |-- [| ptr_vaddr p <> Some 0%N |].
  Proof.
    rewrite same_address_eq_null; iIntros (Hne Hiff) "!%".
    have {Hne Hiff}: ~same_address p nullptr by intuition.
    rewrite same_address_iff ptr_vaddr_nullptr. naive_solver.
  Qed.

  #[global] Instance provides_storage_preserves_nullptr {storage_ptr obj_ptr aty} :
    Observe [| storage_ptr = nullptr <-> obj_ptr = nullptr |] (provides_storage storage_ptr obj_ptr aty).
  Proof.
    apply observe_intro_only_provable; iIntros "PS".
    iDestruct (provides_storage_same_address with "PS") as %Hsm.
    iDestruct (provides_storage_valid_obj_ptr with "PS") as "#VO".
    iDestruct (provides_storage_valid_storage_ptr with "PS") as "#VS {PS}".
    iDestruct (same_address_eq_null with "VO") as %[HeqO _].
    iDestruct (same_address_eq_null with "VS") as %[HeqS _].
    iIntros "!%"; split; intros ->.
    - apply HeqO, symmetry, Hsm.
    - apply HeqS, Hsm.
  Qed.

  #[global] Instance provides_storage_preserves_nonnull {storage_ptr obj_ptr aty} :
    Observe [| storage_ptr <> nullptr <-> obj_ptr <> nullptr |] (provides_storage storage_ptr obj_ptr aty).
  Proof.
    apply observe_intro_only_provable. iIntros "PS".
    by iDestruct (provides_storage_preserves_nullptr with "PS") as "#-> {PS}".
  Qed.

  Global Instance pinned_ptr_unique va va' p :
    Observe2 [| va = va' |] (pinned_ptr va p) (pinned_ptr va' p).
  Proof.
    rewrite pinned_ptr_eq.
    iIntros "[%H1 _] [%H2 _] !> !%". exact: pinned_ptr_pure_unique.
  Qed.

  Lemma offset_2_pinned_ptr_pure o1 o2 z1 z2 va p :
    eval_offset σ o1 = Some z1 ->
    eval_offset σ o2 = Some z2 ->
    pinned_ptr_pure va (p .., o1) ->
    valid_ptr p |-- valid_ptr (p .., o1) -* valid_ptr (p .., o2) -*
    [| pinned_ptr_pure (Z.to_N (Z.of_N va - z1 + z2)) (p .., o2) |].
  Proof.
    iIntros (He1 He2 Hpin1) "V V1 V2".
    iDestruct (offset_inv_pinned_ptr_pure with "V1") as %[??]; [done..|].
    iDestruct (offset_pinned_ptr_pure with "V2") as %Hgoal; [done..|].
    iIntros "!%". by rewrite Z2N.id in Hgoal.
  Qed.

  Lemma pinned_ptr_null : |-- pinned_ptr 0 nullptr.
  Proof.
    rewrite pinned_ptr_eq /pinned_ptr_def.
    iFrame (pinned_ptr_pure_null).
    iApply exposed_ptr_nullptr.
  Qed.

  Lemma offset_pinned_ptr o z va p :
    eval_offset _ o = Some z ->
    valid_ptr (p .., o) |--
    pinned_ptr va p -* pinned_ptr (Z.to_N (Z.of_N va + z)) (p .., o).
  Proof.
    rewrite pinned_ptr_eq /pinned_ptr_def.
    iIntros (He) "#V' #(%P & E)".
    iDestruct (offset_pinned_ptr_pure with "V'") as "$"; [done..|].
    by iApply offset_exposed_ptr.
  Qed.

  Lemma offset_inv_pinned_ptr o z va p :
    eval_offset _ o = Some z ->
    valid_ptr p |-- pinned_ptr va (p .., o) -*
    [| 0 <= Z.of_N va - z |]%Z ** pinned_ptr (Z.to_N (Z.of_N va - z)) p.
  Proof.
    rewrite pinned_ptr_eq /pinned_ptr_def.
    iIntros (He) "#V #(%P & E)".
    iDestruct (offset_inv_pinned_ptr_pure with "[]") as "-#[$$]"; [done..| |].
    { by iApply (observe with "E"). }
    by iApply offset_inv_exposed_ptr.
  Qed.

  Lemma offset2_pinned_ptr o1 o2 z1 z2 va p :
    eval_offset σ o1 = Some z1 ->
    eval_offset σ o2 = Some z2 ->
    valid_ptr p |-- valid_ptr (p .., o1) -* valid_ptr (p .., o2) -*
    pinned_ptr va (p .., o1) -*
    pinned_ptr (Z.to_N (Z.of_N va - z1 + z2)) (p .., o2).
  Proof.
    rewrite pinned_ptr_eq /pinned_ptr_def.
    iIntros (He1 He2) "V V1 #V2 #(%P & E)".
    iDestruct (offset_2_pinned_ptr_pure with "V V1 V2") as "$"; [done..|].
    by iApply offset2_exposed_ptr.
  Qed.

  Lemma pinned_ptr_aligned_divide va n p :
    pinned_ptr va p ⊢
    [| aligned_ptr n p <-> (n | va)%N |].
  Proof.
    rewrite pinned_ptr_eq /pinned_ptr_def; iIntros "(%P & _) !%".
    exact: pinned_ptr_pure_aligned_divide.
  Qed.

  Lemma pinned_ptr_pure_type_divide_1 va n p ty
    (Hal : align_of ty = Some n) :
    type_ptr ty p ⊢ [| pinned_ptr_pure va p |] -∗ [| (n | va)%N |].
  Proof.
    rewrite type_ptr_aligned_pure. iIntros "!%".
    exact: pinned_ptr_pure_divide_1.
  Qed.

  Lemma pinned_ptr_type_divide_1 va n p ty
    (Hal : align_of ty = Some n) :
    type_ptr ty p ⊢ pinned_ptr va p -∗ [| (n | va)%N |].
  Proof.
    rewrite pinned_ptr_eq /pinned_ptr_def.
    iIntros "#? #(? & _)". by iApply pinned_ptr_pure_type_divide_1.
  Qed.

  Lemma shift_pinned_ptr_sub ty z va (p1 : ptr) p2 o:
    size_of σ ty = Some o ->
    _offset_ptr p1 (o_sub _ ty z) = p2 ->
        valid_ptr p2 ** pinned_ptr va p1
    |-- pinned_ptr (Z.to_N (Z.of_N va + z * Z.of_N o)) p2.
  Proof.
    move => o_eq <-.
    iIntros "[val pin1]".
    iApply (offset_pinned_ptr _ with "val") => //.
    rewrite eval_o_sub o_eq /= Z.mul_comm //.
  Qed.

  Lemma _valid_valid p vt : _valid_ptr vt p |-- valid_ptr p.
  Proof. case: vt => [|//]. exact: strict_valid_valid. Qed.

  Lemma valid_ptr_sub (i j k : Z) p ty vt
    (Hj : (i <= j <= k)%Z) :
    _valid_ptr vt (p .., o_sub σ ty i) |--
    _valid_ptr vt (p .., o_sub σ ty k) -* valid_ptr (p .., o_sub σ ty j).
  Proof.
    destruct (decide (j = k)) as [->|Hne].
    { rewrite -_valid_valid. by iIntros "_ $". }
    rewrite -strict_valid_valid. apply strict_valid_ptr_sub. lia.
  Qed.

  Lemma _valid_ptr_field_sub (i : Z) p ty f vt (Hle : (0 <= i)%Z) :
    _valid_ptr vt (p .., o_field σ f .., o_sub σ ty i) |-- _valid_ptr vt (p .., o_field σ f).
  Proof.
    iIntros "V". case: (decide (i = 0)%Z) Hle => [-> _|Hne Hle].
    - iDestruct (valid_o_sub_size with "V") as %?.
      by rewrite offset_ptr_sub_0.
    - rewrite strict_valid_ptr_field_sub; last by lia.
      case: vt => //. by rewrite strict_valid_valid.
  Qed.

  (** [p] is a valid pointer value in the sense of the standard, or
  "standard-valid" (https://eel.is/c++draft/basic.compound#3.1), that is both
  valid (in our sense) and live.

  In particular, [p] is a valid pointer value even when accounting for
  pointer zapping.
  *)
  Definition _valid_live_ptr vt (p : ptr) : mpred :=
    _valid_ptr vt p ∗ live_ptr p.
  Definition valid_live_ptr p : mpred := _valid_live_ptr Relaxed p.
  Definition strict_valid_live_ptr p : mpred := _valid_live_ptr Strict p.

  Global Instance tptsto_flip_mono :
    Proper (flip genv_leq ==> eq ==> eq ==> eq ==> eq ==> flip (⊢))
      (@tptsto _ Σ).
  Proof. repeat intro. exact: tptsto_mono. Qed.

  Global Instance tptsto_as_fractional ty q a v :
    AsFractional (tptsto ty q a v) (λ q, tptsto ty q a v) q.
  Proof. exact: Build_AsFractional. Qed.

  Global Instance identity_as_fractional this mdc p q :
    AsFractional (identity this mdc q p) (λ q, identity this mdc q p) q.
  Proof. exact: Build_AsFractional. Qed.

  Global Instance tptsto_observe_nonnull t q p v :
    Observe [| p <> nullptr |] (tptsto t q p v).
  Proof.
    apply: observe_intro.
    destruct (ptr_eq_dec p nullptr); subst; last by eauto.
    rewrite {1}tptsto_nonnull. exact: bi.False_elim.
  Qed.

  Lemma tptsto_disjoint : forall ty p v1 v2,
    tptsto ty 1 p v1 ** tptsto ty 1 p v2 |-- False.
  Proof.
    intros *; iIntros "[T1 T2]".
    iDestruct (observe_2_elim_pure with "T1 T2") as %Hvs.
    iDestruct (tptsto_val_related_transport $! Hvs with "T1") as "T2'".
    iCombine "T2 T2'" as "T".
    iDestruct (tptsto_frac_valid with "T") as %L => //.
  Qed.

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

  (** *** Just wrappers. *)
  (** We can lift validity entailments through [Observe] (using
  [Observe_mono]. These are not instances, to avoid causing slowdowns in
  proof search. *)
  Lemma observe_strict_valid_valid
    `(Hobs : !Observe (strict_valid_ptr p) P) : Observe (valid_ptr p) P.
  Proof. by rewrite -strict_valid_valid. Qed.

  Lemma observe_type_ptr_strict_valid
    `(Hobs : !Observe (type_ptr ty p) P) : Observe (strict_valid_ptr p) P.
  Proof. by rewrite -type_ptr_strict_valid. Qed.

  Lemma observe_type_ptr_valid_plus_one
    `(Hobs : !Observe (type_ptr ty p) P) : Observe (valid_ptr (p .., o_sub σ ty 1)) P.
  Proof. by rewrite -type_ptr_valid_plus_one. Qed.

  Lemma type_ptr_valid ty p : type_ptr ty p |-- valid_ptr p.
  Proof. by rewrite type_ptr_strict_valid strict_valid_valid. Qed.

  #[global] Instance type_ptr_size_observe ty p :
    Observe [| is_Some (size_of σ ty) |] (type_ptr ty p).
  Proof. rewrite type_ptr_size. apply _. Qed.

  #[global] Instance valid_ptr_sub_0 (p : ptr) (ty : type) :
    is_Some (size_of _ ty) ->
    Observe (valid_ptr (p .., o_sub σ ty 0)) (valid_ptr p).
  Proof. intros. rewrite o_sub_0 // offset_ptr_id. refine _. Qed.
  #[global] Instance type_ptr_sub_0 (p : ptr) (ty : type) :
    is_Some (size_of _ ty) ->
    Observe (valid_ptr (p .., o_sub σ ty 0)) (type_ptr ty p).
  Proof.
    intros. by rewrite type_ptr_valid; apply valid_ptr_sub_0.
  Qed.
  #[global] Instance type_ptr_valid_ptr_next (p : ptr) (ty : type) (m n : Z) :
    (m = n + 1)%Z ->
    Observe (valid_ptr (p .., o_sub σ ty m)) (type_ptr ty (p .., o_sub σ ty n)).
  Proof.
    intros; subst.
    iIntros "X".
    iDestruct (observe (valid_ptr (p .., o_sub _ _ _ .., o_sub _ _ _)) with "X") as "z".
    apply observe_type_ptr_valid_plus_one. refine _.
    by rewrite o_sub_sub.
  Qed.

  Lemma same_alloc_refl p : valid_ptr p ⊢ [| same_alloc p p |].
  Proof.
    rewrite valid_ptr_alloc_id same_alloc_iff. iIntros "!%". case; naive_solver.
  Qed.

  Lemma live_has_alloc_id p :
    live_ptr p ⊢ ∃ aid, [| ptr_alloc_id p = Some aid |] ∗ live_alloc_id aid.
  Proof. rewrite /live_ptr; iIntros. case: (ptr_alloc_id p) => /= [aid|]; eauto. Qed.
End with_cpp.
