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

Require Import bedrock.lang.cpp.ast.

(** pointers *)
Parameter ptr : Set.
Parameter ptr_eq_dec : forall (x y : ptr), { x = y } + { x <> y }.
Parameter nullptr : ptr.


(** values *)
Variant val : Type :=
| Vint (_ : Z)
| Vptr (_ : ptr)
| Vundef
.

Definition val_dec : forall a b : val, {a = b} + {a <> b}.
Proof.
  decide equality. eapply Z.eq_dec. apply ptr_eq_dec.
Defined.

Definition Vchar (a : Ascii.ascii) : val :=
  Vint (Z.of_N (N_of_ascii a)).
Definition Vbool (b : bool) : val :=
  Vint (if b then 1 else 0).
Definition Vnat (b : nat) : val :=
  Vint (Z.of_nat b).
Definition Vn (b : N) : val :=
  Vint (Z.of_N b).
Notation Vz := Vint (only parsing).
Definition Vvoid := Vundef.

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

(* this is the stack frame *)
Parameter region : Type.
(* this is the thread information *)
Parameter thread_info : Type.


(** pointer offsets *)
(* All offsets are valid pointers. todo: This is unsound. *)
Parameter offset_ptr_ : Z -> ptr -> ptr.

Axiom offset_ptr_combine_ : forall b o o',
    offset_ptr_ o' (offset_ptr_ o b) = offset_ptr_ (o + o') b.
Axiom offset_ptr_0_ : forall b,
    offset_ptr_ 0 b = b.


Parameter offset_ptr : Z -> val -> val.
(* note(gmm): this is not defined according to the C semantics because creating
 * a pointer that goes out of bounds of the object is undefined behavior in C,
 * e.g. [(p + a) - a <> p] if [p + a] is out of bounds.
 *)
Axiom offset_ptr_combine : forall b o o',
    offset_ptr o' (offset_ptr o b) = offset_ptr (o + o') b.
Axiom offset_ptr_0 : forall b,
    offset_ptr 0 b = b.
Axiom offset_ptr_val : forall v o p, Vptr p = v -> Vptr (offset_ptr_ o p) = offset_ptr o v.


(** global environments *)

(* this contains two things:
 * - the types declared in the program
 * - the program's symbol table (mapping of globals to pointers)
 *   (this is not necessarily the same as a the symbol table in the
 *    object file because it will contain the addresses of [static]
 *    variables)
 *
 * if we want to do things like word-size agnostic verification, then
 * information like that would need to be in here as well.
 *)
Record genv : Type :=
{ genv_cu : compilation_unit
  (* ^ the [compilation_unit] *)
; glob_addr : obj_name -> option ptr
  (* ^ the address of global variables & functions *)
}.

(* [genv_leq a b] states that [b] is an extension of [a] *)
Parameter genv_leq : genv -> genv -> Prop.
Global Declare Instance PreOrder_genv_leq : PreOrder genv_leq.
Definition glob_def (g : genv) (gn : globname) : option GlobDecl :=
  lookup_global g.(genv_cu) gn.

(* this states that the [genv] is compatible with the given [compilation_unit]
 * it essentially means that the [genv] records all the types from the
 * compilation unit and that the [genv] contains addresses for all globals
 * defined in the [compilation_unit]
 *)
Parameter genv_compat : compilation_unit -> genv -> Prop.
Infix "⊧" := genv_compat (at level 1).



(* todo(gmm): this should be indexed by [genv] *)
Parameter has_type : val -> type -> Prop.
Arguments has_type _%Z _.

Definition max_val (bits : size) (sgn : signed) : Z :=
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
  end%Z.

Definition min_val (bits : size) (sgn : signed) : Z :=
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
  end%Z.

Axiom has_type_pointer : forall v ty, has_type v (Tpointer ty) -> exists p, v = Vptr p.

Definition bound (bits : size) (sgn : signed) (v : Z) : Prop :=
  (min_val bits sgn <= v <= max_val bits sgn)%Z.

Arguments Z.add _ _ : simpl never.
Arguments Z.sub _ _ : simpl never.
Arguments Z.mul _ _ : simpl never.
Arguments Z.pow _ _ : simpl never.
Arguments Z.opp _ : simpl never.
Arguments Z.pow_pos _ _ : simpl never.

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

(* todo(gmm): this isn't sound due to reference fields *)
Definition offset_of (resolve : genv) (t : globname) (f : ident) : option Z :=
  match glob_def resolve t with
  | Some (Gstruct s) => find_field f (List.map (fun '(a,_,c) => (a,c.(li_offset) / 8)%Z) s.(s_fields))
  | Some (Gunion u) => find_field f (List.map (fun '(a,_,c) => (a,c.(li_offset) / 8))%Z u.(u_fields))
  | _ => None
  end.

Definition parent_offset (resolve : genv) (t : globname) (f : globname) : option Z :=
  match glob_def resolve t with
  | Some (Gstruct s) => find_field f (List.map (fun '(s,l) => (s,l.(li_offset) / 8))%Z s.(s_bases))
  | _ => None
  end.

Parameter pointer_size : genv -> N. (* in bytes *)

Variant Roption_leq {T} (R : T -> T -> Prop) : option T -> option T -> Prop :=
| Rleq_None {x} : Roption_leq R None x
| Rleq_Some {x y} (_ : R x y) : Roption_leq R (Some x) (Some y).

(* sizeof() *)
(* [size_of] requires a well-founded type environment in order to be
 * implementable as a function.
 *)
Parameter size_of : forall (resolve : genv) (t : type), option N.
Global Declare Instance Proper_size_of
: Proper (genv_leq ==> eq ==> Roption_leq eq) (@size_of).

(* it is hard to define [size_of] as a function because it needs
to recurse through the environment in the case of [Treference]:
termination will require a proof of well-foundedness of the environment *)
Axiom size_of_int : forall {c : genv} s w,
    @size_of c (Tint w s) = Some (N.div (N_of_size w + 7) 8).
Axiom size_of_char : forall {c : genv} s w,
    @size_of c (Tchar w s) = Some (N.div (N_of_size w + 7) 8).
Axiom size_of_bool : forall {c : genv},
    @size_of c Tbool = Some 1%N.
Axiom size_of_pointer : forall {c : genv} t,
    @size_of c (Tpointer t) = Some (pointer_size c).
Axiom size_of_qualified : forall {c : genv} t q,
    @size_of c t = @size_of c (Tqualified q t).
Axiom size_of_array : forall {c : genv} t n sz,
    @size_of c t = Some sz ->
    @size_of c (Tarray t n) = Some (sz * n)%N.

Lemma size_of_Qmut : forall {c} t,
    @size_of c t = @size_of c (Qmut t).
Proof.
  intros.
  now apply size_of_qualified.
Qed.

Lemma size_of_Qconst : forall {c} t ,
    @size_of c t = @size_of c (Qconst t).
Proof.
  intros.
  now apply size_of_qualified.
Qed.

(* alignof() *)
Parameter align_of : forall {resolve : genv} (t : type), option N.
Global Declare Instance Proper_align_of
: Proper (genv_leq ==> eq ==> Roption_leq eq) (@align_of).
