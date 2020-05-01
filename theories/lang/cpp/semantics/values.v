(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * The "operational" style definitions about C++.
 *
 * The definitions in this file are based (loosely) on CompCert.
 *)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import stdpp.gmap.

Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.sub_module.

Set Default Proof Using "Type".

(** * pointers
    this is the abstract model of pointers in C++.
    - A simple model is [block * offset] which is representing a collection
      of isolated blocks. There is no address arithmetic that can get you
      from one block to another.
    - A more complex model allows for nested blocks and more accurately
      models the C/C++ (object) memory model. See
      https://robbertkrebbers.nl/thesis.html
 *)
Parameter ptr : Set.
Parameter ptr_eq_dec : forall (x y : ptr), { x = y } + { x <> y }.
Instance: EqDecision ptr := ptr_eq_dec.
Instance: Countable ptr.
Proof. Admitted.

(** C++ provides a distinguished pointer [nullptr] that is *never
    dereferenable*
 *)
Parameter nullptr : ptr.


(** ** pointer offsets *)
(** the offset of a pointer. *)
Parameter offset_ptr_ : Z -> ptr -> ptr.

Axiom offset_ptr_combine_ : forall b o o',
    offset_ptr_ o' (offset_ptr_ o b) = offset_ptr_ (o + o') b.
Axiom offset_ptr_0_ : forall b,
    offset_ptr_ 0 b = b.


(** * values
    abstract C++ runtime values come in two flavors.
    - integers
    - pointers
    there is also a distinguished undefined element [Vundef] that
    models uninitialized values. Operations on [Vundef] are all
    undefined behavior.
 *)
Variant val : Set :=
| Vint (_ : Z)
| Vptr (_ : ptr)
| Vundef
.

Definition val_dec : forall a b : val, {a = b} + {a <> b}.
Proof.
  decide equality. eapply Z.eq_dec. apply ptr_eq_dec.
Defined.
Instance: EqDecision val := val_dec.

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
  | Vundef => None
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

    here, we instantiate [region] as [ptr] which allows us to extend regions
    at runtime (when new variables are declared).

    an alternative model is to instantiate region as [gmap ident ptr]
    essentially giving a location to each local variable.
    todo: change to this model?
 *)
Definition region : Type := ptr.

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
{ genv_cu : compilation_unit
  (* ^ the [compilation_unit] *)
; glob_addr : obj_name -> option ptr
  (* ^ the address of global variables & functions *)
; pointer_size : N
  (* ^ the size of a pointer (in bytes) *)
}.

(** [genv_leq a b] states that [b] is an extension of [a] *)
Definition genv_leq (l r : genv) : Prop :=
  sub_module l.(genv_cu) r.(genv_cu) /\
  (forall a p, l.(glob_addr) a = Some p ->
          r.(glob_addr) a = Some p) /\
  l.(pointer_size) = r.(pointer_size).

Instance PreOrder_genv_leq : PreOrder genv_leq.
Proof.
  constructor.
  { constructor; [ | constructor ]; auto; reflexivity. }
  { red. unfold genv_leq.
    intros ? ? ? [A [B C]] [A' [B' C']].
    split; [ | split ]; etransitivity; eauto. }
Qed.
Definition glob_def (g : genv) (gn : globname) : option GlobDecl :=
  g.(genv_cu).(globals) !! gn.

Definition genv_eq (l r : genv) : Prop :=
  genv_leq l r /\ genv_leq r l.

(* this states that the [genv] is compatible with the given [compilation_unit]
 * it essentially means that the [genv] records all the types from the
 * compilation unit and that the [genv] contains addresses for all globals
 * defined in the [compilation_unit]
 *)
Parameter genv_compat : compilation_unit -> genv -> Prop.
Infix "⊧" := genv_compat (at level 1).

Parameter subModuleModels : forall a b σ, b ⊧ σ -> module_le a b = true -> a ⊧ σ.

(** typedness of values
    note that only primitives fit into this, there is no [val] representation
    of aggregates.
 *)
Parameter has_type : val -> type -> Prop.
Arguments has_type _%Z _.

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
  (min_val bits sgn <= v <= max_val bits sgn)%Z.

Axiom has_type_pointer : forall v ty, has_type v (Tpointer ty) -> exists p, v = Vptr p.

Axiom has_int_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tint sz sgn).

Axiom has_char_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tchar sz sgn).

Axiom has_type_qual : forall t q x,
    has_type x (drop_qualifiers t) ->
    has_type x (Tqualified q t).

Hint Resolve has_type_qual : has_type.

Fixpoint find_field {T} (f : ident) (fs : list (ident * T)) : option T :=
  match fs with
  | nil => None
  | (f',v) :: fs =>
    if String.eqb f f' then
      Some v
    else find_field f fs
  end%list.

(* note: we expose the fact that reference fields are compiled to pointers,
   so the [offset_of] a referene field is the offset of the pointer.
 *)
Definition offset_of (resolve : genv) (t : globname) (f : ident) : option Z :=
  match glob_def resolve t with
  | Some (Gstruct s) =>
    find_field f (List.map (fun '(a,_,c) => (a,c.(li_offset) / 8)%Z) s.(s_fields))
  | Some (Gunion u) =>
    find_field f (List.map (fun '(a,_,c) => (a,c.(li_offset) / 8))%Z u.(u_fields))
  | _ => None
  end.

Definition parent_offset (resolve : genv) (t : globname) (f : globname) : option Z :=
  match glob_def resolve t with
  | Some (Gstruct s) => find_field f (List.map (fun '(s,l) => (s,l.(li_offset) / 8))%Z s.(s_bases))
  | _ => None
  end.

Variant Roption_leq {T} (R : T -> T -> Prop) : option T -> option T -> Prop :=
| Rleq_None {x} : Roption_leq R None x
| Rleq_Some {x y} (_ : R x y) : Roption_leq R (Some x) (Some y).

(** * sizeof() *)
(** this is a partial implementation of [size_of], it doesn't indirect through
    typedefs, but the cpp2v generator flattens these for us anyways.
 *)
Fixpoint size_of (resolve : genv) (t : type) : option N :=
  match t with
  | Tpointer _ => Some (@pointer_size resolve)
  | Treference _ => None
  | Trv_reference _ => None
  | Tint sz _ => Some (bytesN sz)
  | Tchar sz _ => Some (bytesN sz)
  | Tvoid => None
  | Tarray t n => match size_of resolve t with
                 | None => None
                 | Some s => Some (n * s)
                 end
  | Tnamed nm =>
    match glob_def resolve nm with
    | Some (Gstruct s) => Some s.(s_size)
    | Some (Gunion u) => Some u.(u_size)
    | _ => None
    end
  | Tfunction _ _ => None
  | Tbool => Some 1
  | Tmember_pointer _ _ => Some (@pointer_size resolve)
  | Tqualified _ t => size_of resolve t
  | Tnullptr => Some (@pointer_size resolve)
  | Tfloat sz => Some (bytesN sz)
  | Tarch sz _ => match sz with
                 | None => None
                 | Some sz => Some (bytesN sz)
                 end
  end%N.

Global Instance Proper_size_of
: Proper (genv_leq ==> eq ==> Roption_leq eq) (@size_of).
Proof.
  red. red. red. intros; subst.
  induction y0; simpl; try constructor; eauto.
  - apply H.
  - destruct IHy0; try constructor. subst. auto.
  - destruct H as [ [ H _ ] _ ].
    specialize (H g).
    unfold glob_def, globals, Lookup_instance_0 in *.
    destruct (globals (genv_cu x) !! g); try constructor.
    destruct (H _ eq_refl) as [ ? [ -> HH ] ]; clear H.
    destruct g0; try constructor;
    destruct x0; try constructor; simpl in HH ; try congruence.
    + apply require_eq_success in HH. destruct HH. congruence.
    + apply require_eq_success in HH. destruct HH. congruence.
  - apply H.
  - apply H.
  - destruct o; repeat constructor.
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
Global Declare Instance Proper_align_of
: Proper (genv_leq ==> eq ==> Roption_leq eq) (@align_of).

Arguments Z.add _ _ : simpl never.
Arguments Z.sub _ _ : simpl never.
Arguments Z.mul _ _ : simpl never.
Arguments Z.pow _ _ : simpl never.
Arguments Z.opp _ : simpl never.
Arguments Z.pow_pos _ _ : simpl never.
