(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha et al.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

(**
 The "operational" style definitions about C++, especially pointers and
 values.

 C++ pointers are subtle to model.
 The definitions in this file are based on the C and C++ standards, and
 formalizations of their memory object models.
 - the CompCert memory model
 - Robbert Krebbers's model of C (Krebbers 2015, PhD thesis,
   https://robbertkrebbers.nl/research/thesis.pdf).
 - The formal model of pointer provenance for C given by Cerberus
   (https://www.cl.cam.ac.uk/~pes20/cerberus/, POPL'19 https://doi.org/10.1145/3290380,
 - A Provenance-aware Memory Object Model for C.
   Working paper N2577 of the C standards committee (ISO TC1/SC22/WG14),
   September 30, 2020
   (http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2577.pdf).
 - Work by Ramananandro et al. (e.g. POPL'12 https://doi.org/10.1145/2103656.2103718).
 - LLVM's twin semantics, that is,
 "Reconciling high-level optimizations and low-level code in LLVM", OOPSLA'18
   (https://doi.org/10.1145/3276495).

 For a crash course on formal models of pointers, consider
 https://www.ralfj.de/blog/2018/07/24/pointers-and-bytes.html; the summary is
 that two pointers might differ despite representing the same address
 (https://eel.is/c++draft/basic.compound#def:represents_the_address),
 depending on how they're constructed, and C/C++ optimizers are allowed to
 treat them differently.

 As our goal is verifying low-level systems software, we make
 assumptions on our compilers, here and elsewhere:
 - We assume compilers do not zap pointers to deallocated objects, but might
   restrict operations on them (in particular equality comparisons). See
   http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2369.pdf,
   https://www.cl.cam.ac.uk/~pes20/cerberus/notes30.pdf
 - We assume useful semantics for integer-to-pointer casts, in particular,
   the PNVI-ae-udi model by the Cerberus project (as in the N2577 draft).
   Our semantics is built with them in mind but does not provide them yet.
 - Support for effective types is also incomplete; similarly to Cerberus,
   we still assume users use options such as [-fno-strict-aliasing] GCC/Clang's.
 *)
From Coq Require Import Strings.Ascii.
From bedrock.lang.prelude Require Import base addr option.

Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.semantics Require Export types sub_module genv.

Local Close Scope nat_scope.
Local Open Scope Z_scope.
Implicit Types (σ : genv).

(** ** Allocation IDs. We use them to model pointer provenance, following
Cerberus. *)
Record alloc_id := MkAllocId { alloc_id_car : N }.

Global Instance alloc_id_eq_dec : EqDecision alloc_id.
Proof. solve_decision. Qed.
Global Instance alloc_id_countable : Countable alloc_id.
Proof. by apply: (inj_countable' alloc_id_car MkAllocId) => -[?]. Qed.


Module Type PTRS.
(** * Pointers.

This is the abstract model of pointers in C++ — more precisely, of their
values. Pointers describe paths that might identify objects, which might be
alive. Hence they must be understood relative to the C++ object model
(https://eel.is/c++draft/intro.object). We also use pointers to represent the
values of references, even if those are restricted to point to objects or
functions (https://eel.is/c++draft/dcl.ref#5).

- Not all of our pointers have concrete addresses.
  In C++, pointers to some objects are never created, and typical compilers
  might choose to not store such objects in memory; nevertheless, for
  uniformity our semantics identifies such objects via pointers, but
  our pointers need not represent an address
  (https://eel.is/c++draft/basic.compound#def:represents_the_address).
  Function [ptr_vaddr] maps a pointer to the address it represents, if any.
  See also documentation of [tptsto] and [pinned_ptr].
  (Compilers might temporarily store objects elsewhere, but only as a
  semantics-preserving optimization, which we ignore in our model of the C++
  abstract machine).
  That objects (of non-zero size) have constant addresses follows:
  - for C11 (draft N1570), from 6.2.4.2:
    > An object exists, has a constant address^33
    > [33]: The term ‘‘constant address’’ means that two pointers to the object
    constructed at possibly different times will compare equal.
  - for C++, from https://eel.is/c++draft/intro.object#8:

    > an object with nonzero size shall occupy one or more bytes of storage

    and https://eel.is/c++draft/intro.memory#1:

    > every byte has a unique address.

Pointers also have an _allocation ID_; the concept does not exist in
the standard but is used to model provenance in many models of C
pointers (CompCert, Krebbers, Cerberus, LLVM's twin semantics), sometimes
under the name of "object ID". Allocation ID of deallocated regions are never
reused for new regions.
- C++ objects form a forest of _complete objects_, and subobjects contained
  within (https://eel.is/c++draft/intro.object#2).
  All subobjects of the same complete object share the same allocation
  ID.
- Character array objects can _provide storage_ to other objects.
  (http://eel.is/c++draft/intro.object#def:provides_storage)
  In particular, when memory allocators allocates an object [o] out of a
  character array [arr], then [arr] provides storage to [o].
  Following Cerberus, a pointer to [arr] and a pointer to [o] are
  considered as having distinct provenance.

  In Cerberus, pointers with fresh provenances are created by a
  magic [malloc] primitive, which cannot be implemented in C (at least
  because of effective types, as Krebbers explains); in our semantics,
  pointers with fresh provenance are created by [new] operations (see
  [wp_prval_new] axiom).

From a pointer to an object, one can use offsets to constructs pointers
to subojects.

Our API allows tracking nested objects accurately, matching the C (object)
memory model (as rendered by Krebbers) and the model mandated by the C++
standard.

A simple model is [alloc ID * option address] [SIMPLE_PTRS_IMPL]; a richer
one is [PTRS_IMPL].
*)

  Parameter ptr : Set.
  Declare Scope ptr_scope.
  Bind Scope ptr_scope with ptr.
  Delimit Scope ptr_scope with ptr.

  Axiom ptr_eq_dec : forall (x y : ptr), { x = y } + { x <> y }.
  Global Instance ptr_eq_dec' : EqDecision ptr := ptr_eq_dec.
  (* TODO AUTO: replace [ptr_eq_dec'] with:

    Axiom ptr_eq_dec : EqDecision ptr.
    Global Existing Instance ptr_eq_dec.

  However, removing [ptr_eq_dec'] breaks some clients, especially for
  automation. *)

  Axiom ptr_countable : Countable ptr.
  Global Existing Instance ptr_countable.

  (**
    * Pointer offsets.
      Offsets represent paths between objects and subobjects.

      If [p] points to an object and [o] is an offset to a subobject,
      [p .., o] is a pointer to that subobject. If no such object exist,
      [valid_ptr (p .., o)] will not hold.

      For instance, if [p->x] is a C++ object but [p->y] isn't, in Coq pointer
      [p ., o_field "x"] will be valid but [p ., o_field "y"] will not,
      *)
  Parameter offset : Set.
  Declare Scope offset_scope.
  Bind Scope offset_scope with offset.
  Delimit Scope offset_scope with offset.

  Axiom offset_eq_dec : EqDecision offset.
  Global Existing Instance offset_eq_dec.
  Axiom offset_countable : Countable offset.
  Global Existing Instance offset_countable.

  (** Offsets form a monoid *)
  Parameter o_id : offset.
  Parameter o_dot : offset -> offset -> offset.

  Axiom id_dot : LeftId (=) o_id o_dot.
  Axiom dot_id : RightId (=) o_id o_dot.
  Axiom dot_assoc : Assoc (=) o_dot.

  Global Existing Instances id_dot dot_id dot_assoc.

  (** combine an offset and a pointer to get a new pointer;
    this is a right monoid action.
   *)
  Parameter _offset_ptr : ptr -> offset -> ptr.
  Reserved Notation "p .., o" (at level 11, left associativity).
  Notation "p .., o" := (_offset_ptr p o) : ptr_scope.
  Notation "o1 .., o2" := (o_dot o1 o2) : offset_scope.

  Axiom offset_ptr_id : forall p, (p .., o_id = p)%ptr.
  Axiom offset_ptr_dot : forall p o1 o2,
    (p .., (o1 .., o2) = p .., o1 .., o2)%ptr.

  (** C++ provides a distinguished pointer [nullptr] that is *never
      dereferenceable*
      (https://eel.is/c++draft/basic.compound#3)
  *)
  Parameter nullptr : ptr.

  (** An invalid pointer, included as a sentinel value. Other pointers might
  be invalid as well; see [_valid_ptr]. *)
  Parameter invalid_ptr : ptr.

  (* Pointer to a C++ "complete object" with external or internal linkage, or
  to "functions"; even if they are distinct in C/C++ standards (e.g.
  https://eel.is/c++draft/basic.pre#:object
  https://eel.is/c++draft/basic.compound#3.1), we represent them in the same
  way.

  Since function pointers cannot be offset, offsetting function pointers
  produces [invalid_ptr], but we haven't needed to expose this.
  *)
  (* ^ the address of global variables & functions *)
  Parameter global_ptr :
    translation_unit -> obj_name -> ptr.
    (* Dynamic loading might require adding some abstract [translation_unit_id]. *)
    (* Might need deferring, as it needs designing a [translation_unit_id];
     since loading the same translation unit twice can give different
     addresses. *)

  (* Other constructors exist, but they are internal to C++ model.
  They include
  pointers to local variables (objects with automatic linkage/storage
  duration, https://eel.is/c++draft/basic.memobj#basic.stc.auto).

  Pointers to this (https://eel.is/c++draft/expr.prim.this) are just normal
  pointers naming the receiver of a method invocation.
  *)

  (** ** Concrete pointer offsets.
  They correspond to the kind of aggregate objects described in e.g.
  https://eel.is/c++draft/basic.compound. *)

  (* If [p : cls*] points to an object with type [cls] and field [f],
    then [p .., o_field cls f] points to [p -> f]. *)
  Parameter o_field : genv -> field -> offset.
  (*
  If [p : cls*] points to an array object with [n] elements and [i ≤ n],
  [p .., o_sub ty i] represents [p + i] (which might be a past-the-end pointer).
  *)
  Parameter o_sub : genv -> type -> Z -> offset.

  (*
  [o_sub_0] axiom is required because any object is a 1-object array
  (https://eel.is/c++draft/expr.add#footnote-80).
  *)
  Axiom o_sub_0 : ∀ σ ty,
    is_Some (size_of σ ty) ->
    o_sub σ ty 0 = o_id.
  (* TODO: drop (is_Some (size_of σ ty)) via
  `displacement (o_sub σ ty i) = if (i = 0) then 0 else i * size_of σ ty` *)

  (** going up and down the class hierarchy, one step at a time. *)
  Parameter o_base : genv -> forall (derived base : globname), offset.
  Parameter o_derived : genv -> forall (base derived : globname), offset.

  (** * Deprecated APIs *)
  (** Offset a pointer by a certain number of bytes. *)
  Parameter offset_ptr__ : Z -> ptr -> ptr.
  #[deprecated(since="2020-12-08", note="Use structured offsets instead.")]
  Notation offset_ptr_ := offset_ptr__.

  Axiom offset_ptr_0__ : forall b,
    offset_ptr_ 0 b = b.
  #[deprecated(since="2020-12-08", note="Use structured offsets instead.")]
  Notation offset_ptr_0_ := offset_ptr_0__.

  (** Map pointers to allocation IDs; total on valid pointers thanks to
  [valid_ptr_alloc_id]. *)
  Parameter ptr_alloc_id : ptr -> option alloc_id.
  (**
  Map pointers to the address they represent,
  (https://eel.is/c++draft/basic.compound#def:represents_the_address).
  Not defined on all valid pointers; defined on pointers existing in C++ (
  https://eel.is/c++draft/basic.compound#3).
  See discussion above.
  *)
  Parameter ptr_vaddr : ptr -> option vaddr.

  (**
    [ptr_vaddr_nullptr] is not mandated by the standard, but valid across
    compilers we are interested in.
    The closest hint is in https://eel.is/c++draft/conv.ptr
   *)
  Axiom ptr_vaddr_nullptr : ptr_vaddr nullptr = Some 0%N.

  Axiom ptr_alloc_id_offset : forall {p o},
    is_Some (ptr_alloc_id (p .., o)) ->
    ptr_alloc_id (p .., o) = ptr_alloc_id p.

  (** Pointers into the same array with the same address have the same index.
  Wrapped by [same_address_o_sub_eq]. *)
  Axiom ptr_vaddr_o_sub_eq : forall p σ ty n1 n2 sz,
    size_of σ ty = Some sz -> (sz > 0)%N ->
    (same_property ptr_vaddr (p .., o_sub _ ty n1) (p .., o_sub _ ty n2) ->
    n1 = n2)%ptr.

  Axiom o_sub_sub_nneg : ∀ σ p ty (z1 z2 : Z),
    (0 <= z1 -> 0 <= z2 ->
    p .., o_sub σ ty z1 .., o_sub σ ty z2 = p .., o_sub σ ty (z1 + z2))%ptr%Z.

  Axiom o_sub_sub_npos : ∀ σ p ty (z1 z2 : Z),
    (z1 <= 0 -> z2 <= 0 ->
    p .., o_sub σ ty z1 .., o_sub σ ty z2 = p .., o_sub σ ty (z1 + z2))%ptr%Z.
End PTRS.

Module Type PTRS_DERIVED (Import L : PTRS).
  Parameter same_alloc : ptr -> ptr -> Prop.
  Axiom same_alloc_eq : same_alloc = same_property ptr_alloc_id.

  Parameter same_address : ptr -> ptr -> Prop.
  Axiom same_address_eq : same_address = same_property ptr_vaddr.

  (** Define when [p]'s address is pinned to [va], as defined via [ptr_vaddr]. *)
  Parameter pinned_ptr_pure : forall (va : vaddr) (p : ptr), Prop.
  Axiom pinned_ptr_pure_eq : pinned_ptr_pure = fun (va : vaddr) (p : ptr) => ptr_vaddr p = Some va.
End PTRS_DERIVED.

Module Type RAW_BYTES.
(** * Raw bytes
    Raw bytes represent the low-level view of data.
    [raw_byte] abstracts over the internal structure of this low-level view of data.
    E.g. in the [simple_pred] model, [raw_byte] would be instantiated with [runtime_val].

    [raw_int_byte] is a raw byte that is a concrete integer values (i.e. not a pointer fragment or poison).
 *)
Parameter raw_byte : Set.
Parameter raw_byte_eq_dec : EqDecision raw_byte.
Existing Instance raw_byte_eq_dec.

Axiom raw_int_byte : N -> raw_byte.

End RAW_BYTES.

Module Type PTRS_MIXIN (Import P : PTRS) (Import PD : PTRS_DERIVED P).
  Global Instance same_alloc_dec : RelDecision same_alloc.
  Proof. rewrite same_alloc_eq. apply _. Qed.
  Global Instance same_address_dec : RelDecision same_address.
  Proof. rewrite same_address_eq. apply _. Qed.

  Lemma pinned_ptr_pure_unique va1 va2 p :
    pinned_ptr_pure va1 p -> pinned_ptr_pure va2 p -> va1 = va2.
  Proof.
    rewrite pinned_ptr_pure_eq => H1 H2. apply (inj Some). by rewrite -H1 -H2.
  Qed.

  Lemma same_address_pinned p1 p2 :
    same_address p1 p2 <-> ∃ va, pinned_ptr_pure va p1 ∧ pinned_ptr_pure va p2.
  Proof. by rewrite same_address_eq pinned_ptr_pure_eq same_property_iff. Qed.

  Lemma same_alloc_iff p1 p2 :
    same_alloc p1 p2 <-> ∃ aid, ptr_alloc_id p1 = Some aid ∧ ptr_alloc_id p2 = Some aid.
  Proof. by rewrite same_alloc_eq same_property_iff. Qed.

  Global Instance pinned_ptr_pure_proper va :
    Proper (same_address ==> iff) (pinned_ptr_pure va).
  Proof.
    move=> p1 p2.
    by rewrite same_address_pinned pinned_ptr_pure_eq => -[va' [-> ->]].
  Qed.
  Global Instance: Params pinned_ptr_pure 1 := {}.

  Lemma same_alloc_offset p o
    (Hs : is_Some (ptr_alloc_id (p .., o))) :
    same_alloc p (p .., o).
  Proof.
    case: (Hs) => aid Eq. rewrite same_alloc_iff.
    exists aid. by rewrite -(ptr_alloc_id_offset Hs).
  Qed.

  (** Pointers into the same array with the same address have the same index.
  Wrapper by [ptr_vaddr_o_sub_eq]. *)
  Lemma same_address_o_sub_eq p σ ty n1 n2 sz :
    size_of σ ty = Some sz -> (sz > 0)%N ->
    same_address (p .., o_sub _ ty n1) (p .., o_sub _ ty n2) -> n1 = n2.
  Proof. rewrite same_address_eq. exact: ptr_vaddr_o_sub_eq. Qed.
End PTRS_MIXIN.

Module Type VAL_MIXIN (Import L : PTRS) (Import R : RAW_BYTES).

(** * Values
    Primitive abstract C++ runtime values come in two flavors.
    - pointers (also used for references)
    - integers (used for everything else)
    Aggregates are not represented directly, but only by talking about
    primitive subobjects.

    There is also a distinguished undefined element [Vundef] that
    models uninitialized values (https://eel.is/c++draft/basic.indet).
    Operations on [Vundef] are all undefined behavior.
    [Vraw] (a raw byte) represents the low-level bytewise view of data.
    See [logic/layout.v] for more axioms about it.
 *)
Variant val : Set :=
| Vint (_ : Z)
| Vptr (_ : ptr)
| Vraw (_ : raw_byte)
| Vundef
.

Definition val_dec : forall a b : val, {a = b} + {a <> b}.
Proof. solve_decision. Defined.
Instance val_eq_dec : EqDecision val := val_dec.
Instance val_inhabited : Inhabited val := populate (Vint 0).

End VAL_MIXIN.

Module Type PTRS_FULL := PTRS <+ PTRS_DERIVED <+ RAW_BYTES <+ VAL_MIXIN <+ PTRS_MIXIN.
Declare Module PTRS_FULL_AXIOM : PTRS_FULL.
Export PTRS_FULL_AXIOM.

(* Unsound! TODO: this axiom is unsound; if [o + o' = 0],
but [offset_ptr_ o p] overflows into an invalid pointer, then
[offset_ptr_ o' (offset_ptr_ o p)] is invalid as well.

But since [offset_ptr_ ] should be deprecated anyway, we defer removing it,
to update clients only once.
*)
Axiom offset_ptr_combine__ : forall p o o',
  (* TODO: this premise is necessary, but breaks clients. *)
  (* offset_ptr_ o p <> invalid_ptr -> *)
  offset_ptr_ o' (offset_ptr_ o p) = offset_ptr_ (o + o') p.
#[deprecated(since="2020-11-25",
note="This is UNSOUND. Use higher-level APIs or o_sub_sub.")]
Notation offset_ptr_combine_ := offset_ptr_combine__.

Instance ptr_inhabited : Inhabited ptr := populate nullptr.

(** wrappers for constructing certain values *)
Definition Vchar (a : Ascii.ascii) : val :=
  Vint (Z.of_N (N_of_ascii a)).
Definition Vbool (b : bool) : val :=
  Vint (if b then 1 else 0).
Definition Vnat (b : nat) : val :=
  Vint (Z.of_nat b).
Definition Vn (b : N) : val :=
  Vint (Z.of_N b).
Notation Vz := Vint (only parsing).

(** we use [Vundef] as our value of type [void] *)
Definition Vvoid := Vundef.

(** lifting pointer offsets to values *)
Definition offset_ptr (o : Z) (v : val) : val :=
  match v with
  | Vptr p => Vptr (offset_ptr_ o p)
  | _ => Vundef
  end.
Theorem offset_ptr_val : forall v o p,
    Vptr p = v ->
    Vptr (offset_ptr_ o p) = offset_ptr o v.
Proof. intros; subst; reflexivity. Qed.

Definition is_true (v : val) : option bool :=
  match v with
  | Vint v => Some (negb (Z.eqb v 0))
  | Vptr p => Some match ptr_eq_dec p nullptr with
                  | left _ => false
                  | right _ => true
                  end
  | Vundef | Vraw _ => None
  end.

Theorem is_true_int : forall i,
    is_true (Vint i) = Some (negb (BinIntDef.Z.eqb i 0)).
Proof. reflexivity. Qed.

Theorem Vptr_inj : forall p1 p2, Vptr p1 = Vptr p2 -> p1 = p2.
Proof. inversion 1; reflexivity. Qed.
Theorem Vint_inj : forall a b, Vint a = Vint b -> a = b.
Proof. inversion 1; reflexivity. Qed.
Theorem Vbool_inj : forall a b, Vbool a = Vbool b -> a = b.
Proof. by move=>[] [] /Vint_inj. Qed.

(** * regions
    to model the stack frame in separation logic, we use a notion of regions
    that are threaded through the semantics.

    we instantiate [region] as a stack of finite maps from variables
    to their addresses.
 *)
Inductive region : Type :=
| Remp (this : option ptr) (result : option ptr)
| Rbind (_ : localname) (_ : ptr) (_ : region).

Fixpoint get_location (ρ : region) (b : localname) : option ptr :=
  match ρ with
  | Remp _ _ => None
  | Rbind x p rs =>
    if decide (b = x) then Some p
    else get_location rs b
  end.

Fixpoint get_this (ρ : region) : option ptr :=
  match ρ with
  | Remp this _ => this
  | Rbind _ _ rs => get_this rs
  end.

Fixpoint get_result (ρ : region) : option ptr :=
  match ρ with
  | Remp _ result => result
  | Rbind _ _ rs => get_result rs
  end.

Definition max_val (bits : bitsize) (sgn : signed) : Z :=
  match bits , sgn with
  | W8   , Signed   => 2^7 - 1
  | W8   , Unsigned => 2^8 - 1
  | W16  , Signed   => 2^15 - 1
  | W16  , Unsigned => 2^16 - 1
  | W32  , Signed   => 2^31 - 1
  | W32  , Unsigned => 2^32 - 1
  | W64  , Signed   => 2^63 - 1
  | W64  , Unsigned => 2^64 - 1
  | W128 , Signed   => 2^127 - 1
  | W128 , Unsigned => 2^128 - 1
  end.

Definition min_val (bits : bitsize) (sgn : signed) : Z :=
  match sgn with
  | Unsigned => 0
  | Signed =>
    match bits with
    | W8   => -2^7
    | W16  => -2^15
    | W32  => -2^31
    | W64  => -2^63
    | W128 => -2^127
    end
  end.

Definition bound (bits : bitsize) (sgn : signed) (v : Z) : Prop :=
  min_val bits sgn <= v <= max_val bits sgn.

(** typedness of values
    note that only primitives fit into this, there is no [val] representation
    of aggregates.
 *)
(** [has_type v t] means that [v] is an initialized value of type [t].
For all types [t] except [Tvoid], this means that [v] is not [Vundef]. *)
Parameter has_type : val -> type -> Prop.

Axiom has_type_pointer : forall v ty,
    has_type v (Tpointer ty) -> exists p, v = Vptr p.
Axiom has_type_nullptr : forall v,
    has_type v Tnullptr -> v = Vptr nullptr.
Axiom has_type_reference : forall v ty,
    has_type v (Treference ty) -> exists p, v = Vptr p /\ p <> nullptr.
Axiom has_type_rv_reference : forall v ty,
    has_type v (Trv_reference ty) -> exists p, v = Vptr p /\ p <> nullptr.
Axiom has_type_array : forall v ty n,
    has_type v (Tarray ty n) -> exists p, v = Vptr p /\ p <> nullptr.
Axiom has_type_function : forall v cc rty args,
    has_type v (Tfunction (cc:=cc) rty args) -> exists p, v = Vptr p /\ p <> nullptr.

Axiom has_type_void : forall v,
    has_type v Tvoid -> v = Vundef.

Axiom has_nullptr_type : forall ty,
    has_type (Vptr nullptr) (Tpointer ty).

Axiom has_type_bool : forall v,
    has_type v Tbool <-> exists b, v = Vbool b.

Lemma has_bool_type : forall z,
  0 <= z < 2 <-> has_type (Vint z) Tbool.
Proof.
  intros z. rewrite has_type_bool. split=>Hz.
  - destruct (decide (z = 0)); simplify_eq; first by exists false.
    destruct (decide (z = 1)); simplify_eq; first by exists true. lia.
  - unfold Vbool in Hz. destruct Hz as [b Hb].
    destruct b; simplify_eq; lia.
Qed.

(** Note that from [has_type v (Tint sz sgn)] does not follow
  [v = Vint _] since [v] might also be [Vraw _] (for [T_uchar]). *)
Axiom has_int_type' : forall sz sgn v,
    has_type v (Tint sz sgn) <-> (exists z, v = Vint z /\ bound sz sgn z) \/ (exists r, v = Vraw r /\ Tint sz sgn = T_uchar).

Lemma has_int_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tint sz sgn).
Proof. move => *. rewrite has_int_type'. naive_solver. Qed.

Theorem has_char_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tchar sz sgn).
Proof. apply has_int_type. Qed.

Axiom has_type_qual : forall t q x,
    has_type x (drop_qualifiers t) ->
    has_type x (Tqualified q t).

Hint Resolve has_type_qual : has_type.

Arguments Z.add _ _ : simpl never.
Arguments Z.sub _ _ : simpl never.
Arguments Z.mul _ _ : simpl never.
Arguments Z.pow _ _ : simpl never.
Arguments Z.opp _ : simpl never.
Arguments Z.pow_pos _ _ : simpl never.

(* XXX adapter. *)
Definition glob_addr (σ : genv) (o : obj_name) : option ptr :=
  (fun _ => global_ptr σ.(genv_tu) o) <$> σ.(genv_tu) !! o.

Module Type PTR_INTERNAL (Import P : PTRS).
  (* Useful *)
  Parameter eval_offset : genv -> offset -> option Z.

  (* Clients are not SUPPOSED to look at these APIs; they're only meant for
  transition, and ideally we can drop them. *)
  Axiom _offset_ptr_eq : forall tu p o,
    is_Some (eval_offset tu o) ->
    Some (p .., o)%ptr = flip offset_ptr_ p <$> eval_offset tu o.

  (* NOTE: the multiplication is flipped from path_pred. *)
  Axiom eval_o_sub : forall resolve ty (i : Z),
    eval_offset resolve (o_sub resolve ty i) =
      (fun n => i * Z.of_N n) <$> size_of resolve ty.

  Lemma _o_sub_collapse p i n ty resolve
    (Hsz : size_of resolve ty = Some n) :
    (p .., o_sub resolve ty i)%ptr = offset_ptr_ (i * Z.of_N n) p.
  Proof.
    apply (inj Some).
    by rewrite (_offset_ptr_eq resolve) eval_o_sub Hsz; eauto.
  Qed.

  #[deprecated(since="2020-11-29", note="Use higher-level APIs and avoid
  offset_ptr_; this is only migration band-aid.")]
  Notation offset_ptr_eq := _offset_ptr_eq.
  #[deprecated(since="2020-11-29", note="Use higher-level APIs and avoid
  offset_ptr_; this is only migration band-aid.")]
  Notation o_sub_collapse := _o_sub_collapse.
End PTR_INTERNAL.
Declare Module PTR_INTERNAL_AXIOM : PTR_INTERNAL PTRS_FULL_AXIOM.
