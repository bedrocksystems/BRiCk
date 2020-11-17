(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From bedrock.lang.prelude Require Import base avl.
From bedrock.lang.cpp.syntax Require Import names expr stmt types.

Set Primitive Projections.

(** Record an offset in _bits_. *)
Record LayoutInfo : Set :=
{ li_offset : Z }.
Instance: EqDecision LayoutInfo.
Proof. solve_decision. Defined.

Record Ctor : Set :=
{ c_class  : globname
; c_params : list (ident * type)
; c_cc     : calling_conv
; c_body   : option (OrDefault (list Initializer * Stmt))
}.
Instance: EqDecision Ctor.
Proof. solve_decision. Defined.

Record Dtor : Set :=
{ d_class  : globname
; d_cc     : calling_conv
; d_body   : option (OrDefault (Stmt * list (FieldOrBase * obj_name)))
}.
Instance: EqDecision Dtor.
Proof. solve_decision. Defined.

Variant FunctionBody : Set :=
| Impl (_ : Stmt)
| Builtin (_ : BuiltinFn)
.
Instance: EqDecision FunctionBody.
Proof. solve_decision. Defined.

Record Func : Set :=
{ f_return : type
; f_params : list (ident * type)
; f_cc     : calling_conv
; f_body   : option FunctionBody
}.
Instance: EqDecision Func.
Proof. solve_decision. Defined.

Record Method : Set :=
{ m_return  : type
; m_class   : globname
; m_this_qual : type_qualifiers
; m_params  : list (ident * type)
; m_cc      : calling_conv
; m_body    : option Stmt
}.
Instance: EqDecision Method.
Proof. solve_decision. Defined.

Record Union : Set :=
{ u_fields : list (ident * type * option Expr * LayoutInfo)
  (* ^ fields with type, initializer, and layout information *)
; u_size : N
  (* ^ size of the union (including padding) *)
}.
Instance: EqDecision Union.
Proof. solve_decision. Defined.


Variant LayoutType : Set := POD | Standard | Unspecified.
Instance: EqDecision LayoutType.
Proof. solve_decision. Defined.

Record Struct : Set :=
{ s_bases : list (globname * LayoutInfo)
  (* ^ base classes *)
; s_fields : list (ident * type * option Expr * LayoutInfo)
  (* ^ fields with type, initializer, and layout information *)
; s_layout : LayoutType
  (* ^ the type of layout semantics *)
; s_size : N
  (* ^ size of the structure (including padding) *)
; s_virtuals : list (obj_name * option obj_name)
  (* ^ function_name -> symbol *)
; s_overrides : list (obj_name * obj_name)
  (* ^ k |-> v ~ update k with v *)
; s_virtual_dtor : option obj_name
  (* ^ the name of the virtual destructor, if it is virtual *)
}.
Instance: EqDecision Struct.
Proof. solve_decision. Defined.

Definition has_vtable (s : Struct) : bool :=
  match s.(s_virtuals) with
  | nil => false
  | _ :: _ => true
  end.

Variant Ctor_type : Set := Ct_Complete | Ct_Base | Ct_alloc | Ct_Comdat.
Instance: EqDecision Ctor_type.
Proof. solve_decision. Defined.


(* Definition ctor_name (type : Ctor_type) (cls : globname) : obj_name := *)
(*   match cls with *)
(*   | String _ (String _ s) => *)
(*     "_ZN" ++ s ++ "C" ++ (match type with *)
(*                           | Ct_Complete => "1" *)
(*                           | Ct_Base => "2" *)
(*                           | Ct_Comdat => "5" *)
(*                           end) ++ "Ev" *)
(*   | _ => "" *)
(*   end. *)

Variant Dtor_type : Set := Dt_Deleting | Dt_Complete | Dt_Base | Dt_Comdat.
Instance: EqDecision Dtor_type.
Proof. solve_decision. Defined.

Definition dtor_name (type : Dtor_type) (cls : globname) : obj_name :=
  match cls with
  | BS.String _ (BS.String _ s) =>
    ("_ZN" ++ s ++ "D" ++ ("0" (*match type with
                          | Dt_Deleting => "0"
                          | Dt_Complete => "1"
                          | Dt_Base => "2"
                          | Dt_Comdat => "5"
                          end *)) ++ "Ev")
  | _ => ""
  end%bs.

(* Values in Object files. These can be externed. *)
Variant ObjValue : Set :=
| Ovar         (_ : type) (_ : option Expr)
| Ofunction    (_ : Func)
| Omethod      (_ : Method)
| Oconstructor (_ : Ctor)
| Odestructor  (_ : Dtor).
Instance: EqDecision ObjValue.
Proof. solve_decision. Defined.

(** [type_of_value o] returns the type of the given [ObjValue] *)
Definition type_of_value (o : ObjValue) : type :=
  normalize_type
  match o with
  | Ovar t _ => t
  | Ofunction f => Tfunction (cc:=f.(f_cc)) f.(f_return) $ snd <$> f.(f_params)
  | Omethod m => Tfunction (cc:=m.(m_cc)) m.(m_return) $ Tptr (Tqualified m.(m_this_qual) (Tnamed m.(m_class))) :: (snd <$> m.(m_params))
  | Oconstructor c =>
    Tfunction (cc:=c.(c_cc)) Tvoid $ Tptr (Tnamed c.(c_class)) :: (snd <$> c.(c_params))
  | Odestructor d =>
    Tfunction (cc:=d.(d_cc)) Tvoid $ Tptr (Tnamed d.(d_class)) :: nil
  end.

Variant GlobDecl : Set :=
| Gtype     (* this is a type declaration, but not a definition *)
| Gunion    (_ : Union)
| Gstruct   (_ : Struct)
| Genum     (_ : type) (_ : list ident)
| Gconstant (_ : type) (_ : option Expr)
| Gtypedef  (_ : type).
Instance: EqDecision GlobDecl.
Proof. solve_decision. Defined.



Definition symbol_table : Type := IM.t ObjValue.

Definition type_table : Type := IM.t GlobDecl.

Variant endian : Set := Little | Big.

Instance endian_dec : EqDecision endian.
Proof. solve_decision. Defined.

Record translation_unit : Type :=
{ symbols    : symbol_table
; globals    : type_table
; byte_order : endian
}.

Instance global_lookup : Lookup globname GlobDecl translation_unit :=
  fun k m => m.(globals) !! k.
Instance symbol_lookup : Lookup obj_name ObjValue translation_unit :=
  fun k m => m.(symbols) !! k.

Instance Singleton_twothree {V} : SingletonM bs V (IM.t V) :=
  fun k v => <[ k := v ]> ∅.

Instance Singleton_symbol_table : SingletonM obj_name ObjValue symbol_table := _.
Instance Singleton_type_table : SingletonM globname GlobDecl type_table := _.

Fixpoint ref_to_type (t : type) : option type :=
  match t with
  | Tref t
  | Trv_ref t => Some t
  | Tqualified _ t => ref_to_type t
  | _ => None
  end.

(* Not a reference type *)
Notation not_ref_type t := (ref_to_type t = None).

Section with_type_table.
  Variable te : type_table.
  (* Adapted from Krebbers'15, Definition 3.3.5 *)

  (* Check that [g : GlobDecl] is complete in environment [te]. *)
  Inductive complete_decl : GlobDecl -> Prop :=
  | complete_Struct {st}
              (_ : forall b li, In (b, li) st.(s_bases) -> complete_type (Tnamed b))
              (_ : forall x t e li, In (x, t, e, li) st.(s_fields) -> complete_type t)
    : complete_decl (Gstruct st)
  | complete_Union {u}
              (_ : forall x t e li, In (x, t, e, li) u.(u_fields) -> complete_type t)
    : complete_decl (Gunion u)
  | complete_enum {t consts} (_ : complete_type t)
    : complete_decl (Genum t consts)
  (* Basic types. This excludes references (see [complete_basic_type_not_ref]). *)
  with complete_basic_type : type -> Prop :=
  | complete_float sz : complete_basic_type (Tfloat sz)
  | complete_int sgn sz : complete_basic_type (Tint sgn sz)
  | complete_bool : complete_basic_type Tbool
  | complete_void : complete_basic_type Tvoid
  | complete_nullptr : complete_basic_type Tnullptr
  (* t can in turn be a pointer type *)
  | complete_ptr {t} : complete_pointee_type t -> complete_basic_type (Tptr t)

  (* [complete_pointee_type t] says that a pointer/reference to [t] is complete.
     This excludes references (see [complete_pointee_type_not_ref]). *)
  with complete_pointee_type : type -> Prop :=
  | complete_pt_basic t :
    complete_basic_type t ->
    complete_pointee_type t
  (*
    Pointers to array are only legal if the array is complete, at least
    in C, since they cannot actually be indexed or created.
    This rejects the invalid C:

    [struct T; int foo(struct T x[][10]);]

    However, C++ compilers appear to accept this code.
    TODO: decide behavior.
    *)
  | complete_pt_array t n
    (_ : (n <> 0)%N) (* From Krebbers. Probably needed to reject [T[][]]. *)
    (_ : complete_type t) :
    complete_pointee_type (Tarray t n)
  | complete_pt_named n :
    complete_pointee_type (Tnamed n)
  (* Beware:
  [Tfunction] represents a function type; somewhat counterintuitively,
  a pointer to a function type is complete even if the argument/return types
  are not complete, you're just forbidden from actually invoking the pointer. *)
  | complete_pt_function {cc ret args}
      (_ : complete_pointee_type ret)
      (_ : complete_pointee_types args)
    : complete_pointee_type (Tfunction (cc:=cc) ret args)
  with complete_pointee_types : list type -> Prop :=
  | complete_pt_nil : complete_pointee_types []
  | complete_pt_cons t ts :
    complete_pointee_type t ->
    complete_pointee_types ts ->
    complete_pointee_types (t :: ts)
  (* [complete_type t] says that type [t] is well-formed, that is, complete. *)
  with complete_type : type -> Prop :=
  | complete_basic t :
    complete_basic_type t ->
    complete_type t
  (* Reference types. This setup forbids references to references. *)
  | complete_ref {t} : complete_pointee_type t -> complete_type (Tref t)
  | complete_rv_ref {t} : complete_pointee_type t -> complete_type (Trv_ref t)
  (*
  A reference to a struct/union named [n] is well-formed if its definition is.
  TODO: instead of checking that [n] points to a well-formed definition
  _at each occurrence_, check it once, when adding it to our
  analogue of a type environment, that is [type_table].
  However, that might require replacing [type_table] by a _sequence_ of
  declarations, instead of an unordered dictionary.
  *)
  | complete_named_struct {n st} (_ : te !! n = Some st)
                    (_ : complete_decl st) :
    complete_type (Tnamed n)
  | complete_array {t n}
    (_ : (n <> 0)%N) (* Needed? from Krebbers*)
    (_ : complete_type t) :
    complete_type (Tarray t n)
  | complete_member_pointer {n t} (_ : not_ref_type t)
      (_ : complete_pointee_type (Tnamed n))
      (_ : complete_pointee_type t)
    : complete_type (Tmember_pointer n t)
  (* Beware: Argument/return types need not be complete. *)
  | complete_function {cc ret args}
      (_ : complete_pointee_type ret)
      (_ : complete_pointee_types args)
    : complete_type (Tfunction (cc:=cc) ret args)
  | complete_qualified {q t} (_ : complete_type t)
    : complete_type (Tqualified q t).
End with_type_table.

Scheme complete_decl_mut_ind := Minimality for complete_decl Sort Prop
with complete_basic_type_mut_ind := Minimality for complete_basic_type Sort Prop
with complete_type_mut_ind := Minimality for complete_type Sort Prop
with complete_pointee_type_mut_ind := Minimality for complete_pointee_type Sort Prop
with complete_pointee_types_mut_ind := Minimality for complete_pointee_types Sort Prop.

Combined Scheme complete_mut_ind from complete_decl_mut_ind, complete_basic_type_mut_ind,
  complete_pointee_type_mut_ind, complete_pointee_types_mut_ind, complete_type_mut_ind.

Lemma complete_basic_type_not_ref te t : complete_basic_type te t → not_ref_type t.
Proof. by inversion 1. Qed.
Lemma complete_pointee_type_not_ref te t : complete_pointee_type te t → not_ref_type t.
Proof. inversion 1; by [eapply complete_basic_type_not_ref | ]. Qed.

Lemma complete_type_not_ref_ref te t1 t2 : complete_type te t1 → ref_to_type t1 = Some t2 → not_ref_type t2.
Proof.
  induction 1 => Hsome; simplify_eq/=; generalize dependent te => te;
    try by [exact: complete_pointee_type_not_ref| tauto].
  move => /complete_basic_type_not_ref; naive_solver.
Qed.

Unset Primitive Projections.
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
; pointer_size_bitsize : bitsize
  (* ^ the size of a pointer *)
}.
Definition genv_byte_order (g : genv) : endian :=
  g.(genv_tu).(byte_order).
Definition pointer_size (g : genv) := bytesN (pointer_size_bitsize g).
