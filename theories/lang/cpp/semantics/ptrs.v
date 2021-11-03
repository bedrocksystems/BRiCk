(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
The "operational" style definitions about C++ pointers.

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
From bedrock.prelude Require Import base addr option numbers.

Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp.semantics Require Export types genv.
Require Import iris.algebra.ofe. (* XXX we're mostly not using Iris here. *)

Local Close Scope nat_scope.
Local Open Scope Z_scope.
Implicit Types (σ : genv).

(** ** Allocation IDs. We use them to model pointer provenance, following
Cerberus. *)
Record alloc_id := MkAllocId { alloc_id_car : N }.

#[global] Instance MkAllocId_inj : Inj (=) (=) MkAllocId.
Proof. by intros ?? [=]. Qed.
#[global] Instance alloc_id_eq_dec : EqDecision alloc_id.
Proof. solve_decision. Qed.
#[global] Instance alloc_id_countable : Countable alloc_id.
Proof. by apply: (inj_countable' alloc_id_car MkAllocId) => -[?]. Qed.

Reserved Notation "p .., o" (at level 11, left associativity).

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
    In particular, when memory allocators allocate an object [o] out of a
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
  #[global] Instance ptr_eq_dec' : EqDecision ptr := ptr_eq_dec.
  (* TODO AUTO: replace [ptr_eq_dec'] with:

    Axiom ptr_eq_dec : EqDecision ptr.
    #[global] Existing Instance ptr_eq_dec.

  However, removing [ptr_eq_dec'] breaks some clients, especially for
  automation. *)

  Axiom ptr_countable : Countable ptr.
  #[global] Existing Instance ptr_countable.

  (** * Pointer offsets.
      Offsets represent paths between objects and subobjects.

      If [p] points to an object and [o] is an offset to a subobject,
      [p .., o] is a pointer to that subobject. If no such object exist,
      [valid_ptr (p .., o)] will not hold.

      For instance, if [p->x] is a C++ object but [p->y] isn't, in Coq,
      the pointer [p ., o_field "x"] will be valid but [p ., o_field "y"]
      will not.
   *)
  Parameter offset : Set.
  Declare Scope offset_scope.
  Bind Scope offset_scope with offset.
  Delimit Scope offset_scope with offset.

  Axiom offset_eq_dec : EqDecision offset.
  #[global] Existing Instance offset_eq_dec.
  Axiom offset_countable : Countable offset.
  #[global] Existing Instance offset_countable.

  (** Offsets form a monoid *)
  Parameter o_id  :                     offset.
  Parameter o_dot : offset -> offset -> offset.

  Axiom id_dot    : LeftId  (=) o_id o_dot.
  Axiom dot_id    : RightId (=) o_id o_dot.
  Axiom dot_assoc : Assoc   (=)      o_dot.

  #[global] Existing Instances id_dot dot_id dot_assoc.

  (** combine an offset and a pointer to get a new pointer;
    this is a right monoid action.
   *)
  Parameter _offset_ptr : ptr -> offset -> ptr.
  Notation "p .., o"   := (_offset_ptr p o) : ptr_scope.
  Notation "o1 .., o2" := (o_dot o1 o2)     : offset_scope.
  #[global] Open Scope ptr_scope.

  Axiom offset_ptr_id : forall p, p .., o_id = p.
  Axiom offset_ptr_dot : forall p o1 o2,
    p .., (o1 .., o2) = p .., o1 .., o2.

  (** C++ provides a distinguished pointer [nullptr] that is *never
      dereferenceable*
      (https://eel.is/c++draft/basic.compound#3)
   *)
  Parameter nullptr : ptr.

  (** An invalid pointer, included as a sentinel value. Other pointers might
      be invalid as well; see [_valid_ptr].
   *)
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
  Axiom global_ptr_nonnull : forall tu o, global_ptr tu o <> nullptr.

  (* Other constructors exist, but they are internal to C++ model.
     They include:
     - pointers to local variables (objects with automatic linkage/storage
       duration, https://eel.is/c++draft/basic.memobj#basic.stc.auto).
     - pointers to this (https://eel.is/c++draft/expr.prim.this) are just normal
       pointers naming the receiver of a method invocation.
   *)

  (** ** Concrete pointer offsets.

      They correspond to the kind of aggregate objects described in e.g.
      https://eel.is/c++draft/basic.compound.
   *)

  (* If [p : cls*] points to an object with type [cls] and field [f],
     then [p .., o_field cls f] points to [p -> f].
   *)
  Parameter o_field : genv -> field -> offset.

  (* If [p : cls*] points to an array object with [n] elements and [i ≤ n],
     [p .., o_sub ty i] represents [p + i] (which might be a past-the-end pointer).
   *)
  Parameter o_sub : genv -> type -> Z -> offset.

  (* [o_sub_0] axiom is required because any object is a 1-object array
     (https://eel.is/c++draft/expr.add#footnote-80).
   *)
  Axiom o_sub_0 : ∀ σ ty,
    is_Some (size_of σ ty) ->
    o_sub σ ty 0 = o_id.
  (* TODO: drop (is_Some (size_of σ ty)) via
     `displacement (o_sub σ ty i) = if (i = 0) then 0 else i * size_of σ ty`
   *)

  (** going up and down the class hierarchy, one step at a time. *)
  Parameter o_base : genv -> forall (derived base : globname), offset.
  Parameter o_derived : genv -> forall (base derived : globname), offset.

  (** Map pointers to allocation IDs; total on valid pointers thanks to
      [valid_ptr_alloc_id].
   *)
  Parameter ptr_alloc_id : ptr -> option alloc_id.

  Parameter null_alloc_id : alloc_id.
  Axiom ptr_alloc_id_nullptr :
    ptr_alloc_id nullptr = Some null_alloc_id.

  Axiom ptr_alloc_id_offset : forall {p o},
    is_Some (ptr_alloc_id (p .., o)) ->
    ptr_alloc_id (p .., o) = ptr_alloc_id p.

  (** Map pointers to the address they represent,
      (https://eel.is/c++draft/basic.compound#def:represents_the_address).
      Not defined on all valid pointers; defined on pointers existing in C++ (
      https://eel.is/c++draft/basic.compound#3).
      See discussion above.
   *)
  Parameter ptr_vaddr : ptr -> option vaddr.

  (** [ptr_vaddr_nullptr] is not mandated by the standard, but valid across
      compilers we are interested in.
      The closest hint is in https://eel.is/c++draft/conv.ptr
   *)
  Axiom ptr_vaddr_nullptr : ptr_vaddr nullptr = Some 0%N.

  Axiom global_ptr_nonnull_addr : forall tu o, ptr_vaddr (global_ptr tu o) <> Some 0%N.
  Axiom global_ptr_nonnull_aid : forall tu o, ptr_alloc_id (global_ptr tu o) <> Some null_alloc_id.

  Axiom global_ptr_inj : forall tu, Inj (=) (=) (global_ptr tu).
  Axiom global_ptr_addr_inj : forall tu, Inj (=) (=) (λ o, ptr_vaddr (global_ptr tu o)).
  Axiom global_ptr_aid_inj : forall tu, Inj (=) (=) (λ o, ptr_alloc_id (global_ptr tu o)).
  #[global] Existing Instances global_ptr_inj global_ptr_addr_inj global_ptr_aid_inj.

  (** Pointers into the same array with the same address have the same index.
  Wrapped by [same_address_o_sub_eq]. *)
  Axiom ptr_vaddr_o_sub_eq : forall p σ ty n1 n2 sz,
    size_of σ ty = Some sz -> (sz > 0)%N ->
    same_property ptr_vaddr (p .., o_sub _ ty n1) (p .., o_sub _ ty n2) ->
    n1 = n2.
  Axiom o_dot_sub : ∀ {σ : genv} i j ty,
    o_dot (o_sub _ ty i) (o_sub _ ty j) = o_sub _ ty (i + j).

  (** [eval_offset] and associated axioms are more advanced, only to be used
  in special cases. *)
  (* TODO drop [genv]. *)
  Parameter eval_offset : genv -> offset -> option Z.

  Axiom eval_o_sub : forall σ ty (i : Z),
    eval_offset σ (o_sub σ ty i) =
      (* This order enables reducing for known ty. *)
      (fun n => Z.of_N n * i) <$> size_of σ ty.

  (**
  To hide implementation details of the compiler from proofs, we restrict
  this axiom to POD/Standard-layout structures.
  *)
  Axiom eval_o_field : forall σ f n cls st,
    f = {| f_name := n ; f_type := cls |} ->
    glob_def σ cls = Some (Gstruct st) ->
    st.(s_layout) = POD \/ st.(s_layout) = Standard ->
    eval_offset σ (o_field σ f) = offset_of σ (f_type f) (f_name f).
End PTRS.

Module Type PTRS_DERIVED (Import P : PTRS).
  Parameter same_alloc : ptr -> ptr -> Prop.
  Axiom same_alloc_eq : same_alloc = same_property ptr_alloc_id.

  Parameter same_address : ptr -> ptr -> Prop.
  Axiom same_address_eq : same_address = same_property ptr_vaddr.

End PTRS_DERIVED.

Module Type PTRS_INTF_MINIMAL := PTRS <+ PTRS_DERIVED.

Module Type PTRS_MIXIN (Import P : PTRS_INTF_MINIMAL).
  (**
  Explictly declare that all Iris equalities on pointers are trivial.
  We only add such explicit declarations as actually needed.
  *)
  Canonical Structure ptrO := leibnizO ptr.
  #[global] Instance ptr_inhabited : Inhabited ptr := populate nullptr.

  (** ** [same_address] lemmas *)

  #[global] Instance same_address_dec : RelDecision same_address.
  Proof. rewrite same_address_eq. apply _. Qed.
  #[global] Instance same_address_per : RelationClasses.PER same_address.
  Proof. rewrite same_address_eq. apply _. Qed.
  #[global] Instance same_address_comm : Comm iff same_address.
  Proof. apply: symmetry_iff. Qed.
  #[global] Instance same_address_RewriteRelation : RewriteRelation same_address := {}.

  Lemma same_address_iff p1 p2 :
    same_address p1 p2 <-> ∃ va, ptr_vaddr p1 = Some va ∧ ptr_vaddr p2 = Some va.
  Proof. by rewrite same_address_eq same_property_iff. Qed.

  Lemma same_address_pinned p1 p2 :
    same_address p1 p2 <-> ∃ va, ptr_vaddr p1 = Some va /\ ptr_vaddr p2 = Some va.
  Proof. by rewrite same_address_iff. Qed.

  Lemma same_address_intro p1 p2 va :
    ptr_vaddr p1 = Some va -> ptr_vaddr p2 = Some va -> same_address p1 p2.
  Proof. rewrite same_address_eq; exact: same_property_intro. Qed.

  Lemma same_address_nullptr_nullptr : same_address nullptr nullptr.
  Proof. have ? := ptr_vaddr_nullptr. exact: same_address_intro. Qed.

  #[global] Instance ptr_vaddr_proper :
    Proper (same_address ==> eq) ptr_vaddr.
  Proof. by intros p1 p2 (va&->&->)%same_address_iff. Qed.

  #[global] Instance ptr_vaddr_params : Params ptr_vaddr 1 := {}.


  (** ** [same_address_bool] lemmas *)
  Definition same_address_bool p1 p2 := bool_decide (same_address p1 p2).

  #[global] Instance same_address_bool_comm : Comm eq same_address_bool.
  Proof. move=> p1 p2. apply bool_decide_iff, comm, _. Qed.

  Lemma same_address_bool_eq {p1 p2 va1 va2} :
    ptr_vaddr p1 = Some va1 → ptr_vaddr p2 = Some va2 →
    same_address_bool p1 p2 = bool_decide (va1 = va2).
  Proof.
    intros Hs1 Hs2. apply bool_decide_iff.
    rewrite same_address_eq same_property_iff. naive_solver.
  Qed.

  Lemma same_address_bool_partial_reflexive p :
    is_Some (ptr_vaddr p) ->
    same_address_bool p p = true.
  Proof.
    move=> Hsm. rewrite /same_address_bool bool_decide_true; first done.
    by rewrite same_address_eq -same_property_reflexive_equiv.
  Qed.

  (** ** [same_alloc] lemmas *)

  #[global] Instance same_alloc_dec : RelDecision same_alloc.
  Proof. rewrite same_alloc_eq. apply _. Qed.
  #[global] Instance same_alloc_per : RelationClasses.PER same_alloc.
  Proof. rewrite same_alloc_eq. apply _. Qed.
  #[global] Instance same_alloc_comm : Comm iff same_alloc.
  Proof. apply: symmetry_iff. Qed.

  Lemma same_alloc_iff p1 p2 :
    same_alloc p1 p2 <-> ∃ aid, ptr_alloc_id p1 = Some aid ∧ ptr_alloc_id p2 = Some aid.
  Proof. by rewrite same_alloc_eq same_property_iff. Qed.

  Lemma same_alloc_intro p1 p2 aid :
    ptr_alloc_id p1 = Some aid -> ptr_alloc_id p2 = Some aid -> same_alloc p1 p2.
  Proof. rewrite same_alloc_eq; exact: same_property_intro. Qed.

  Lemma same_alloc_nullptr_nullptr : same_alloc nullptr nullptr.
  Proof. have ? := ptr_alloc_id_nullptr. exact: same_alloc_intro. Qed.



  Lemma ptr_alloc_id_base p o
    (Hs : is_Some (ptr_alloc_id (p .., o))) :
    is_Some (ptr_alloc_id p).
  Proof. by rewrite -(ptr_alloc_id_offset Hs). Qed.

  Lemma same_alloc_offset p o
    (Hs : is_Some (ptr_alloc_id (p .., o))) :
    same_alloc p (p .., o).
  Proof.
    case: (Hs) => aid Eq. rewrite same_alloc_iff.
    exists aid. by rewrite -(ptr_alloc_id_offset Hs).
  Qed.

  Lemma same_alloc_offset_2 p o1 o2 p1 p2
    (E1 : p1 = p .., o1) (E2 : p2 = p .., o2)
    (Hs1 : is_Some (ptr_alloc_id (p .., o1)))
    (Hs2 : is_Some (ptr_alloc_id (p .., o2))) :
    same_alloc p1 p2.
  Proof.
    subst; move: (Hs1) => [aid Eq]; rewrite same_alloc_iff; exists aid; move: Eq.
    by rewrite (ptr_alloc_id_offset Hs1) (ptr_alloc_id_offset Hs2).
  Qed.

  Lemma same_alloc_offset_1 p o
    (Hs : is_Some (ptr_alloc_id (p .., o))) :
    same_alloc p (p .., o).
  Proof.
    apply: (same_alloc_offset_2 p o_id o); rewrite ?offset_ptr_id //.
    exact: ptr_alloc_id_base Hs.
  Qed.

  (** Pointers into the same array with the same address have the same index.
  Wrapper by [ptr_vaddr_o_sub_eq]. *)
  Lemma same_address_o_sub_eq p σ ty n1 n2 sz :
    size_of σ ty = Some sz -> (sz > 0)%N ->
    same_address (p .., o_sub _ ty n1) (p .., o_sub _ ty n2) -> n1 = n2.
  Proof. rewrite same_address_eq. exact: ptr_vaddr_o_sub_eq. Qed.

  Lemma offset_ptr_sub_0 p ty resolve
    (Hsz : is_Some (size_of resolve ty)) :
    _offset_ptr p (o_sub _ ty 0) = p.
  Proof. by rewrite o_sub_0 // offset_ptr_id. Qed.

  (** [aligned_ptr] states that the pointer (if it exists in memory) has
  the given alignment.
    *)
  Definition aligned_ptr align p :=
    (exists va, ptr_vaddr p = Some va /\ (align | va)%N) \/ ptr_vaddr p = None.
  Definition aligned_ptr_ty {σ} ty p :=
    exists align, align_of ty = Some align /\ aligned_ptr align p.

  #[global] Instance aligned_ptr_divide_mono :
    Proper (flip N.divide ==> eq ==> impl) aligned_ptr.
  Proof.
    move=> m n + _ p ->.
    rewrite /aligned_ptr => ? [[va [P D]]|]; [left|by right].
    eexists _; split=> //. by etrans.
  Qed.
  #[global] Instance aligned_ptr_divide_flip_mono :
    Proper (N.divide ==> eq ==> flip impl) aligned_ptr.
  Proof. solve_proper. Qed.
  #[global] Instance N_divide_RewriteRelation : RewriteRelation N.divide := {}.

  Lemma aligned_ptr_divide_weaken m n p :
    (n | m)%N ->
    aligned_ptr m p -> aligned_ptr n p.
  Proof. by move->. Qed.

  Lemma aligned_ptr_mult_weaken_l m n p :
    aligned_ptr (m * n) p -> aligned_ptr n p.
  Proof. by apply aligned_ptr_divide_weaken, N.divide_mul_r. Qed.

  Lemma aligned_ptr_mult_weaken_r m n p :
    aligned_ptr (m * n) p -> aligned_ptr m p.
  Proof. by apply aligned_ptr_divide_weaken, N.divide_mul_l. Qed.

  Lemma aligned_ptr_min p : aligned_ptr 1 p.
  Proof.
    rewrite /aligned_ptr.
    case: ptr_vaddr; [|by eauto] => va.
    eauto using N.divide_1_l.
  Qed.

  Lemma aligned_ptr_ty_mult_weaken {σ} m n ty p :
    align_of ty = Some m -> (n | m)%N ->
    aligned_ptr_ty ty p -> aligned_ptr n p.
  Proof.
    rewrite /aligned_ptr_ty;
      naive_solver eauto using aligned_ptr_divide_weaken.
  Qed.

  Lemma pinned_ptr_pure_aligned_divide va n p :
    ptr_vaddr p = Some va ->
    aligned_ptr n p <-> (n | va)%N.
  Proof. rewrite /aligned_ptr. naive_solver. Qed.

  Lemma pinned_ptr_pure_divide_1 σ va n p ty
    (Hal : align_of ty = Some n) :
    aligned_ptr_ty ty p → ptr_vaddr p = Some va → (n | va)%N.
  Proof.
    rewrite /aligned_ptr_ty Hal /aligned_ptr /=.
    naive_solver.
  Qed.

  Lemma o_sub_sub p ty i j σ :
    p .., o_sub _ ty i .., o_sub _ ty j = (p .., o_sub _ ty (i + j)).
  Proof. by rewrite -offset_ptr_dot o_dot_sub. Qed.

  Notation _id := o_id (only parsing).
  Notation _dot := (o_dot) (only parsing).
  (** access a field *)
  Notation _field := (@o_field _) (only parsing).
  (** subscript an array *)
  Notation _sub z := (@o_sub _ z) (only parsing).
  (** [_base derived base] is a cast from derived to base. *)
  Notation _base := (@o_base _) (only parsing).
  (** [_derived base derived] is a cast from base to derived *)
  Notation _derived := (@o_derived _) (only parsing).
End PTRS_MIXIN.

Module Type PTRS_INTF := PTRS_INTF_MINIMAL <+ PTRS_MIXIN.
