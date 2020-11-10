(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
(**
 * The "operational" style definitions about C++.
 *
 * The definitions in this file are based (loosely) on CompCert.
 *)
From Coq Require Import Strings.Ascii.
Require Import bedrock.lang.prelude.base.

Require Import bedrock.lang.cpp.ast.
Require Export bedrock.lang.cpp.semantics.sub_module.

Local Close Scope nat_scope.
Local Open Scope Z_scope.

Module Type PTRS.
  (** * Pointers.

      This is the abstract model of pointers in C++.
      - A simple model is [block * offset] which is representing a collection
        of isolated blocks. There is no address arithmetic that can get you
        from one block to another.
      - A more complex model allows for nested blocks and more accurately
        models the C/C++ (object) memory model. See
        https://robbertkrebbers.nl/thesis.html.
      Not all of our pointers have physical addresses; for discussion, see
      documentation of [tptsto] and [pinned_ptr].

      This API allows constructing "invalid" pointers; pointer validity is
      defined by [valid_ptr : genv -> ptr -> mpred] elsewhere.
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

  (* Question to resolve: can we commit to Leibniz equality or should we
  expose a setoid with the associated pain? I expect the former. *)

  (* Parameter ptr_equiv : Equiv ptr.
  Global Existing Instances ptr_equiv.
  Axiom ptr_equivalence : Equivalence (==@{ptr}).
  Global Existing Instances ptr_equivalence.
  Axiom ptr_equiv_dec : RelDecision (==@{ptr}).
  Global Existing Instances ptr_equiv_dec. *)

  (** * Offsets.
      Offsets represent paths between locations
   *)
  Parameter offset : Set.
  Declare Scope offset_scope.
  Bind Scope offset_scope with offset.
  Delimit Scope offset_scope with offset.

  Axiom offset_eq_dec : EqDecision offset.
  Global Existing Instance offset_eq_dec.
  Axiom offset_countable : Countable offset.
  Global Existing Instance offset_countable.

  (* Parameter offset_equiv : Equiv offset.
  Global Existing Instances offset_equiv.
  Axiom offset_equivalence : Equivalence (==@{offset}).
  Global Existing Instances offset_equivalence.
  Axiom offset_equiv_dec : RelDecision (==@{offset}).
  Global Existing Instances offset_equiv_dec. *)

  (* offsets form a monoid; maybe just use the free monoid [list offset]? *)
  (* identity - probably not strictly necessary*)
  Parameter o_id : offset.
  Parameter o_dot : offset -> offset -> offset.

  Axiom id_dot : LeftId (=) o_id o_dot.
  Axiom dot_id : RightId (=) o_id o_dot.
  Axiom dot_assoc : Assoc (=) o_dot.
  (* Axiom dot_proper : Proper ((≡) ==> (≡) ==> (≡)) o_dot. *)

  Global Existing Instances id_dot dot_id dot_assoc.
  (* Global Existing Instances dot_proper. *)

  (** combine an offset and a pointer to get a new pointer;
    this is a right monoid action.
   *)
  Parameter _offset_ptr : ptr -> offset -> ptr.
  Reserved Notation "p .., o" (at level 11, left associativity).
  Notation "p .., o" := (_offset_ptr p o) : ptr_scope.
  Notation "o1 .., o2" := (o_dot o1 o2) : offset_scope.
  (* TODO: use an operational typeclass, and add stdpp-style Haskell-style
  variants of the operator. *)

  (* Axiom offset_ptr_proper : Proper ((≡) ==> (≡) ==> (≡)) _offset_ptr. *)
  (* Global Existing Instances offset_ptr_proper. *)
  Axiom offset_ptr_dot : forall p o1 o2,
    (p .., (o1 .., o2) = p .., o1 .., o2)%ptr.

  (** C++ provides a distinguished pointer [nullptr] that is *never
      dereferenceable*
  *)
  Parameter nullptr : ptr.

  (** An invalid pointer, included as a sentinel value. *)
  Parameter invalid_ptr : ptr.

  (** TODO: To drop [genv], we add _some_ constructors for root pointers. *)
  (* Pointer to a C++ "complete object" with external or internal linkage. *)
  (* ^ the address of global variables & functions *)
  Parameter global_ptr :
    translation_unit -> obj_name -> ptr.
    (* Dynamic loading might require adding some abstract [translation_unit_id]. *)
    (* Might need deferring, as it needs designing a [translation_unit_id];
     since loading the same translation unit twice can give different
     addresses. *)

  (* Pointer to "functions"; in C/C++ standards, those are distinct from
  pointers to objects. *)
  Parameter fun_ptr :
    translation_unit -> obj_name -> (* translation_unit_id ->  *) ptr.

  (* Other constructors exist, but are currently only used internally to the
  operational semantics (?):
  - pointers to local variables (objects with automatic linkage/storage duration)
  - pointers to [this]
  *)

  (** ** pointer offsets *)

  (* [o_field cls n] represents [x.n] for [x : cls] *)
  Parameter o_field : genv -> field -> offset.
  (* [o_sub ty n] represents [x + n] for [x : cls*] *)
  Parameter o_sub : genv -> type -> Z -> offset.

  (** going up and down the class heirarchy *)
  Parameter o_base : genv -> forall (derived base : globname), offset.
  Parameter o_derived : genv -> forall (base derived : globname), offset.

  (** * Deprecated APIs *)
  (** Offset a pointer by a certain number of bytes. *)
  Parameter offset_ptr__ : Z -> ptr -> ptr.
  (* #[deprecated(since="X", note="XXX")] *)
  Notation offset_ptr_ := offset_ptr__.

  Axiom offset_ptr_0__ : forall b,
      offset_ptr_ 0 b = b.
  (* #[deprecated(since="X", note="XXX")] *)
  Notation offset_ptr_0_ := offset_ptr_0__.

  Axiom offset_ptr_combine__ : forall b o o',
      offset_ptr_ o' (offset_ptr_ o b) = offset_ptr_ (o + o') b.
  (* #[deprecated(since="X", note="XXX")] *)
  Notation offset_ptr_combine_ := offset_ptr_combine__.
End PTRS.

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

Module Type VAL_MIXIN (Import L : PTRS) (Import R : RAW_BYTES).

(** * values
    Abstract C++ runtime values come in two flavors.
    - integers
    - pointers
    There is also a distinguished undefined element [Vundef] that
    models uninitialized values. Operations on [Vundef] are all
    undefined behavior.
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

Module Type PTRS_FULL := PTRS <+ RAW_BYTES <+ VAL_MIXIN.
Declare Module PTRS_FULL_AXIOM : PTRS_FULL.
Export PTRS_FULL_AXIOM.

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

Fixpoint find_field {T} (f : ident) (fs : list (ident * T)) : option T :=
  match fs with
  | nil => None
  | (f',v) :: fs =>
    if decide (f = f') then
      Some v
    else find_field f fs
  end%list.

(* note: we expose the fact that reference fields are compiled to pointers,
   so the [offset_of] a reference field is the offset of the pointer.
 *)
Definition offset_of (resolve : genv) (t : globname) (f : ident) : option Z :=
  match glob_def resolve t with
  | Some (Gstruct s) =>
    find_field f (List.map (fun '(a,_,_,c) => (a,c.(li_offset) / 8)) s.(s_fields))
  | Some (Gunion u) =>
    find_field f (List.map (fun '(a,_,_,c) => (a,c.(li_offset) / 8)) u.(u_fields))
  | _ => None
  end.

Definition parent_offset (resolve : genv) (t : globname) (f : globname) : option Z :=
  match glob_def resolve t with
  | Some (Gstruct s) => find_field f (List.map (fun '(s,l) => (s,l.(li_offset) / 8)) s.(s_bases))
  | _ => None
  end.

Variant Roption_leq {T} (R : T -> T -> Prop) : option T -> option T -> Prop :=
| Rleq_None {x} : Roption_leq R None x
| Rleq_Some {x y} (_ : R x y) : Roption_leq R (Some x) (Some y).

(** * sizeof() *)
(** this is a partial implementation of [size_of], it doesn't indirect through
    typedefs, but the cpp2v generator flattens these for us anyways.
 *)
Definition GlobDecl_size_of (g : GlobDecl) : option N :=
  match g with
  | Gstruct s => Some s.(s_size)
  | Gunion u => Some u.(u_size)
  | _ => None
  end.
Instance proper_named_size_of: Proper (GlobDecl_ler ==> Roption_leq eq) GlobDecl_size_of.
Proof.
  rewrite /GlobDecl_size_of => x y Heq.
  repeat (case_match; try constructor);
    simplify_eq/= => //;
    apply require_eq_success in Heq; naive_solver.
Qed.

Fixpoint size_of (resolve : genv) (t : type) : option N :=
  match t with
  | Tpointer _ => Some (pointer_size resolve)
  | Treference _ => None
  | Trv_reference _ => None
  | Tint sz _ => Some (bytesN sz)
  | Tvoid => None
  | Tarray t n => N.mul n <$> size_of resolve t
  | Tnamed nm => glob_def resolve nm ≫= GlobDecl_size_of
  | Tfunction _ _ => None
  | Tbool => Some 1
  | Tmember_pointer _ _ => Some (pointer_size resolve)
  | Tqualified _ t => size_of resolve t
  | Tnullptr => Some (pointer_size resolve)
  | Tfloat sz => Some (bytesN sz)
  | Tarch sz _ => bytesN <$> sz
  end%N.

Global Instance Proper_size_of
: Proper (genv_leq ==> eq ==> Roption_leq eq) (@size_of).
Proof.
  intros ?? Hle ? t ->; induction t; simpl; (try constructor) => //.
  all: try exact: pointer_size_proper.
  - by destruct IHt; constructor; subst.
  - move: Hle => [[ /(_ g) Hle _] _ _].
    unfold glob_def, globals in *.
    destruct (globals (genv_tu x) !! g) as [g1| ]; last constructor.
    move: Hle => /(_ _ eq_refl) [g2 [-> HH]] /=.
    exact: proper_named_size_of.
  - by destruct o; constructor.
Qed.

(* it is hard to define [size_of] as a function because it needs
to recurse through the environment in the case of [Treference]:
termination will require a proof of well-foundedness of the environment *)
Theorem size_of_int : forall {c : genv} s w,
    @size_of c (Tint w s) = Some (bytesN w).
Proof. reflexivity. Qed.
Theorem size_of_char : forall {c : genv} s w,
    @size_of c (Tchar w s) = Some (bytesN w).
Proof. reflexivity. Qed.
Theorem size_of_bool : forall {c : genv},
    @size_of c Tbool = Some 1%N.
Proof. reflexivity. Qed.
Theorem size_of_pointer : forall {c : genv} t,
    @size_of c (Tpointer t) = Some (pointer_size c).
Proof. reflexivity. Qed.
Theorem size_of_qualified : forall {c : genv} t q,
    @size_of c t = @size_of c (Tqualified q t).
Proof. reflexivity. Qed.
Theorem size_of_array : forall {c : genv} t n sz,
    @size_of c t = Some sz ->
    @size_of c (Tarray t n) = Some (n * sz)%N.
Proof. simpl; intros. rewrite H. reflexivity. Qed.

Lemma size_of_Qmut : forall {c} t,
    @size_of c t = @size_of c (Qmut t).
Proof. reflexivity. Qed.

Lemma size_of_Qconst : forall {c} t ,
    @size_of c t = @size_of c (Qconst t).
Proof. reflexivity. Qed.

(** * alignof() *)
(* todo: we should embed alignment information in our types *)
Parameter align_of : forall {resolve : genv} (t : type), option N.
Axiom Proper_align_of : Proper (genv_leq ==> eq ==> Roption_leq eq) (@align_of).
Global Existing Instance Proper_align_of.
Axiom align_of_size_of : forall {σ : genv} (t : type) sz,
    size_of σ t = Some sz ->
    exists al, align_of (resolve:=σ) t = Some al /\
          (* alignmend is a multiple of the size *)
          (al mod sz = 0)%N.

Arguments Z.add _ _ : simpl never.
Arguments Z.sub _ _ : simpl never.
Arguments Z.mul _ _ : simpl never.
Arguments Z.pow _ _ : simpl never.
Arguments Z.opp _ : simpl never.
Arguments Z.pow_pos _ _ : simpl never.

(* XXX adapter. *)
Definition glob_addr (σ : genv) (o : obj_name) : option ptr :=
  let p := global_ptr σ.(genv_tu) o in
  match (bool_decide (p = invalid_ptr)) with
  | true => None
  | false => Some p
  end.


(* Clients are not SUPPOSED to look at these APIs, and ideally we can drop them. *)
Module Type ptr_internal (Import P : PTRS).
  Parameter eval_offset : genv -> offset -> option Z.

  (* NOTE this API is especially non-sensical, since pointers and offsets
  contain no translation unit, but eval_offset does *)
  Axiom offset_ptr_eq : forall tu p o,
    Some (p .., o)%ptr = flip offset_ptr_ p <$> eval_offset tu o.

  (* NOTE: the multiplication is flipped from path_pred. *)
  Axiom eval_o_sub : forall resolve ty (i : Z),
    eval_offset resolve (o_sub resolve ty i) =
      (fun n => i * Z.of_N n) <$> size_of resolve ty.

  Lemma o_sub_collapse p i n ty resolve
    (Hsz : size_of resolve ty = Some n) :
    (p .., o_sub resolve ty i)%ptr = offset_ptr_ (i * Z.of_N n) p.
  Proof.
    apply (inj Some).
    by rewrite (offset_ptr_eq resolve) eval_o_sub Hsz.
  Qed.
End ptr_internal.
