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
Require Import bedrock.lang.cpp.semantics.sub_module.

Local Close Scope nat_scope.
Local Open Scope Z_scope.

Module Type PTR_API.
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
  *)

  Parameter ptr : Set.
  Axiom ptr_eq_dec : forall (x y : ptr), { x = y } + { x <> y }.
  Global Instance ptr_eq_dec' : EqDecision ptr := ptr_eq_dec.
  (* TODO AUTO: replace [ptr_eq_dec'] with:

    Axiom ptr_eq_dec : EqDecision ptr.
    Global Existing Instance ptr_eq_dec.

  However, removing [ptr_eq_dec'] breaks some clients, especially for
  automation. *)

  Axiom ptr_countable : Countable ptr.
  Global Existing Instance ptr_countable.

  (** C++ provides a distinguished pointer [nullptr] that is *never
      dereferenceable*
  *)
  Parameter nullptr : ptr.

  (** ** pointer offsets *)
  (** the offset of a pointer. *)
  Parameter offset_ptr_ : Z -> ptr -> ptr.

  Axiom offset_ptr_combine_ : forall b o o',
      offset_ptr_ o' (offset_ptr_ o b) = offset_ptr_ (o + o') b.
  Axiom offset_ptr_0_ : forall b,
      offset_ptr_ 0 b = b.
End PTR_API.

Declare Module PTR : PTR_API.
Export PTR.

Instance ptr_inhabited : Inhabited ptr := populate nullptr.
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
Instance: EqDecision val := val_dec.

Instance val_inhabited : Inhabited val := populate (Vint 0).

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

(** * global environments *)

(** this contains two things:
   - the types declared in the program
   - the program's symbol table (mapping of globals to pointers)
     (this is not necessarily the same as a the symbol table in the
      object file because it will contain the addresses of [static]
      variables)

   if we want to do things like word-size agnostic verification, then
   information like that would need to be in here as well.
 *)
Record genv : Type :=
{ genv_tu : translation_unit
  (* ^ the [translation_unit] *)
; glob_addr : obj_name -> option ptr
  (* ^ the address of global variables & functions *)
; pointer_size_bitsize : bitsize
  (* ^ the size of a pointer *)
}.

Definition byte_order (g : genv) : endian :=
  g.(genv_tu).(byte_order).
Definition pointer_size (g : genv) := bytesN (pointer_size_bitsize g).

(** [genv_leq a b] states that [b] is an extension of [a] *)
Record genv_leq {l r : genv} : Prop :=
{ tu_le : sub_module l.(genv_tu) r.(genv_tu)
; addr_le : forall a p, l.(glob_addr) a = Some p -> r.(glob_addr) a = Some p
; pointer_size_le : l.(pointer_size_bitsize) = r.(pointer_size_bitsize) }.
Arguments genv_leq _ _ : clear implicits.

Instance PreOrder_genv_leq : PreOrder genv_leq.
Proof.
  constructor.
  { constructor; auto; reflexivity. }
  { red. destruct 1; destruct 1; constructor; try etransitivity; eauto. }
Qed.
Instance: RewriteRelation genv_leq := {}.

Definition glob_def (g : genv) (gn : globname) : option GlobDecl :=
  g.(genv_tu).(globals) !! gn.

Definition genv_eq (l r : genv) : Prop :=
  genv_leq l r /\ genv_leq r l.

Instance genv_tu_proper : Proper (genv_leq ==> sub_module) genv_tu.
Proof. solve_proper. Qed.
Instance genv_tu_flip_proper : Proper (flip genv_leq ==> flip sub_module) genv_tu.
Proof. solve_proper. Qed.

(* Sadly, neither instance is picked up by [f_equiv]. *)
Instance pointer_size_bitsize_proper : Proper (genv_leq ==> eq) pointer_size_bitsize.
Proof. solve_proper. Qed.
Instance pointer_size_bitsize_flip_proper : Proper (flip genv_leq ==> eq) pointer_size_bitsize.
Proof. by intros ?? <-. Qed.
Instance pointer_size_proper : Proper (genv_leq ==> eq) pointer_size.
Proof. unfold pointer_size; intros ???. f_equiv. exact: pointer_size_bitsize_proper. Qed.
Instance pointer_size_flip_proper : Proper (flip genv_leq ==> eq) pointer_size.
Proof. by intros ?? <-. Qed.

Instance byte_order_proper : Proper (genv_leq ==> eq) byte_order.
Proof. intros ???. apply sub_module.byte_order_proper. solve_proper. Qed.
Instance byte_order_flip_proper : Proper (flip genv_leq ==> eq) byte_order.
Proof. by intros ?? <-. Qed.

(* this states that the [genv] is compatible with the given [translation_unit]
 * it essentially means that the [genv] records all the types from the
 * compilation unit and that the [genv] contains addresses for all globals
 * defined in the [translation_unit]
 *)
Class genv_compat {tu : translation_unit} {g : genv} : Prop :=
{ tu_compat : sub_module tu g.(genv_tu) }.
Arguments genv_compat _ _ : clear implicits.
Infix "⊧" := genv_compat (at level 1).

Theorem genv_byte_order_tu tu g :
    tu ⊧ g ->
    byte_order g = translation_unit.byte_order tu.
Proof. intros. apply sub_module.byte_order_flip_proper, tu_compat. Qed.

Theorem genv_compat_submodule : forall m σ, m ⊧ σ -> sub_module m σ.(genv_tu).
Proof. by destruct 1. Qed.

Instance genv_compat_proper : Proper (flip sub_module ==> genv_leq ==> impl) genv_compat.
Proof.
  intros ?? Heq1 ?? [Heq2 _ _] [Heq3]; constructor.
  by rewrite Heq1 Heq3.
Qed.
Instance genv_compat_flip_proper : Proper (sub_module ==> flip genv_leq ==> flip impl) genv_compat.
Proof. solve_proper. Qed.

(* XXX rename/deprecate? *)
Theorem subModuleModels a b σ : b ⊧ σ -> sub_module a b -> a ⊧ σ.
Proof. by intros ? ->. Qed.

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
  - move: Hle => [[ /(_ g) Hle _ _] _ _].
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
