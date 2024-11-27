(*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.types.
Require Import bedrock.lang.cpp.syntax.stmt.


#[local] Notation EqDecision1 T := (∀ (A : Set), EqDecision A -> EqDecision (T A)) (only parsing).
#[local] Notation EqDecision2 T := (∀ (A : Set), EqDecision A -> EqDecision1 (T A)) (only parsing).
#[local] Notation EqDecision3 T := (∀ (A : Set), EqDecision A -> EqDecision2 (T A)) (only parsing).
#[local] Notation EqDecision4 T := (∀ (A : Set), EqDecision A -> EqDecision3 (T A)) (only parsing).
#[local] Tactic Notation "solve_decision" := intros; solve_decision.

Variant OrDefault {t : Set} : Set :=
  | Defaulted
  | UserDefined (_ : t).
Arguments OrDefault : clear implicits.
#[global] Instance OrDefault_inh: forall {T: Set}, Inhabited (OrDefault T).
Proof. repeat constructor. Qed.
#[global] Instance OrDefault_eq_dec: forall {T: Set}, EqDecision T -> EqDecision (OrDefault T).
Proof. solve_decision. Defined.

Module OrDefault.
  Import UPoly.

  Definition fmap {A B : Set} (f : A -> B) (v : OrDefault A) : OrDefault B :=
    match v with
    | Defaulted => Defaulted
    | UserDefined a => UserDefined (f a)
    end.
  #[global] Arguments fmap _ _ _ & _ : assert.

  (*
  #[universes(polymorphic)]
  Definition traverse@{u | } {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}
    {A B : Set} (f : A -> F B) (v : OrDefault A) : F (OrDefault B) :=
    match v with
    | Defaulted => mret Defaulted
    | UserDefined a => UserDefined <$> f a
    end.
  #[global] Arguments traverse _ _ _ _ _ _ & _ _ : assert.
  #[global] Hint Opaque traverse : typeclass_instances.
  *)

  #[global,universes(polymorphic)]
  Instance OrDefault_traverse : Traverse OrDefault :=
    fun F _ _ _ _ _ f od =>
      match od with
      | Defaulted => mret Defaulted
      | UserDefined v => UserDefined <$> f v
      end.
End OrDefault.

(** ** Type Declarations *)

(** Record an offset in _bits_. *)
Record LayoutInfo : Set :=
{ li_offset : Z }.
#[global] Instance: EqDecision LayoutInfo.
Proof. solve_decision. Defined.

Record Member' {lang} : Set := mkMember
{ mem_name : field_name.t lang
; mem_type : type' lang
; mem_mutable : bool
; mem_init : option (Expr' lang)
; mem_layout : LayoutInfo }.
#[global] Arguments Member' : clear implicits.
#[global] Arguments mkMember {_} & _ _ _ _ _ : assert.
#[global] Instance Member_eq_dec {lang}: EqDecision (Member' lang).
Proof. solve_decision. Defined.
Notation Member := (Member' lang.cpp).

Record Union' {lang} : Set := Build_Union
{ u_fields : list (Member' lang)
  (* ^ fields with type, initializer, and layout information *)
; u_dtor : obj_name' lang
  (* ^ the name of the destructor *)
; u_trivially_destructible : bool
  (* ^ whether objects of the union type are trivially destructible. *)
; u_delete : option (obj_name' lang)
  (* ^ name of [operator delete], if it exists *)
; u_size : N
  (* ^ size of the union (including padding) *)
; u_alignment : N
  (* ^ alignment of the union *)
}.
#[global] Arguments Union' : clear implicits.
#[global] Arguments Build_Union {_} & _ _ _ _ _ _ : assert.
#[global] Instance Union'_eq_dec {lang} : EqDecision (Union' lang).
Proof. solve_decision. Defined.
Notation Union := (Union' lang.cpp).

Variant LayoutType : Set := POD | Standard | Unspecified.
#[global] Instance: EqDecision LayoutType.
Proof. solve_decision. Defined.

Record Struct' {lang} : Set := Build_Struct
{ s_bases : list (classname' lang * LayoutInfo)
  (* ^ base classes *)
; s_fields : list (Member' lang)
  (* ^ fields with type, initializer, and layout information *)
; s_virtuals : list (obj_name' lang * option (obj_name' lang))
  (* ^ function_name -> symbol *)
; s_overrides : list (obj_name' lang * obj_name' lang)
  (* ^ k |-> v ~ update k with v *)
; s_dtor : obj_name' lang
  (* ^ the name of the destructor.
     NOTE at the C++ abstract machine level, there is only
          one destructor, but implementations (and name mangling)
          use multiple destructors in cases of classes with [virtual]
          inheritence.
   *)
; s_trivially_destructible : bool
  (* ^ this is actually computable, and we could compute it *)
; s_delete : option (obj_name' lang)
  (* ^ the name of a [delete] member function in case virtual dispatch is used to destroy an
     object of this type. *)
; s_layout : LayoutType
  (* ^ the type of layout semantics *)
(* The remaining fields are implementation-dependent. They might be mandated by the per-platform ABI. *)
; s_size : N
  (* ^ size of the structure (including padding) *)
; s_alignment : N
  (* ^ alignment of the structure *)
}.
#[global] Arguments Struct' : clear implicits.
#[global] Arguments Build_Struct {_} & _ _ _ _ _ _ _ _ _ _ : assert.
#[global] Instance Struct_eq_dec {lang} : EqDecision (Struct' lang).
Proof. solve_decision. Defined.
Notation Struct := (Struct' lang.cpp).

(** [has_vtable s] determines whether [s] has any <<virtual>> methods
    (or bases). Having a vtable is *not* a transitive property.
    A class that only inherits <<virtual>> methods does not have a
    vtable.

    Note that methods that override virtual methods are implicitly virtual.
    This includes destructor.
 *)
Definition has_vtable {lang} (s : Struct' lang) : bool :=
  match s.(s_virtuals) with
  | nil => false
  | _ :: _ => true
  end.
#[global] Arguments has_vtable {_} & _ : assert.

(* [has_virtual_dtor s] returns true if the destructor is virtual. *)
Definition has_virtual_dtor {lang} (s : Struct' lang) : bool :=
  List.existsb (fun '(a,_) => bool_decide (a = s.(s_dtor))) s.(s_virtuals).
#[global] Arguments has_virtual_dtor _ & _ : assert.

Variant Ctor_type : Set := Ct_Complete | Ct_Base | Ct_alloc | Ct_Comdat.
#[global] Instance: EqDecision Ctor_type.
Proof. solve_decision. Defined.

(** ** Value Declarations *)

(** *** Functions *)
Variant FunctionBody' {lang} : Set :=
| Impl (_ : Stmt' lang)
| Builtin (_ : BuiltinFn)
.
#[global] Arguments FunctionBody' _ : clear implicits, assert.
#[global] Arguments Impl _ &.
#[global] Instance: forall {lang}, EqDecision (FunctionBody' lang).
Proof. solve_decision. Defined.
Notation FunctionBody := (FunctionBody' lang.cpp).

Record Func' {lang} : Set := Build_Func
{ f_return : type' lang
; f_params : list (ident * type' lang)
; f_cc     : calling_conv
; f_arity  : function_arity
; f_body   : option (FunctionBody' lang)
}.
#[global] Arguments Func' : clear implicits.
#[global] Arguments Build_Func {_} & _ _ _ _ _ : assert.
#[global] Instance: forall {lang}, EqDecision (Func' lang).
Proof. solve_decision. Defined.
#[global] Instance Func_inhabited {lang} : Inhabited (Func' lang).
Proof. solve_inhabited. Qed.
Notation Func := (Func' lang.cpp).

(** *** Methods *)
Record Method' {lang} : Set := Build_Method
{ m_return  : type' lang
; m_class   : classname' lang
; m_this_qual : type_qualifiers
; m_params  : list (ident * type' lang)
; m_cc      : calling_conv
; m_arity   : function_arity
; m_body    : option (OrDefault (Stmt' lang))
}.
#[global] Arguments Method' : clear implicits.
#[global] Arguments Build_Method {_} & _ _ _ _ _ _ _ : assert.
#[global] Instance: forall {lang}, EqDecision (Method' lang).
Proof. solve_decision. Defined.
Notation Method := (Method' lang.cpp).

Definition static_method {lang} (m : Method' lang)
  : Func' lang :=
  {| f_return := m.(m_return)
   ; f_params := m.(m_params)
   ; f_cc := m.(m_cc)
   ; f_arity := m.(m_arity)
   ; f_body := match m.(m_body) with
               | Some (UserDefined body) => Some (Impl body)
               | _ => None
               end |}.

(** *** Constructors *)

Variant InitPath' {lang} : Set :=
| InitBase (_ : classname' lang)
| InitField (_ : field_name.t lang)
| InitIndirect (anon_path : list (field_name.t lang * classname' lang)) (_ : field_name.t lang)
| InitThis.
#[global] Arguments InitPath' : clear implicits.
#[global] Instance: forall {lang}, EqDecision (InitPath' lang).
Proof. solve_decision. Defined.
#[global] Notation InitPath := (InitPath' lang.cpp).

Record Initializer' {lang} : Set := Build_Initializer
  { init_path : InitPath' lang
  ; init_init : Expr' lang }.
#[global] Arguments Initializer' : clear implicits.
#[global] Arguments Build_Initializer {_} & _ _ : assert.
#[global] Instance: forall {lang}, EqDecision (Initializer' lang).
Proof. solve_decision. Defined.
Notation Initializer := (Initializer' lang.cpp).

Record Ctor' {lang} : Set := Build_Ctor
{ c_class  : classname' lang
; c_params : list (ident * type' lang)
; c_cc     : calling_conv
; c_arity  : function_arity
; c_body   : option (OrDefault (list (Initializer' lang) * Stmt' lang))
}.
#[global] Arguments Ctor' : clear implicits.
#[global] Arguments Build_Ctor {_} & _ _ _ _ _ : assert.
#[global] Instance: forall {lang}, EqDecision (Ctor' lang).
Proof. solve_decision. Defined.
Notation Ctor := (Ctor' lang.cpp).

(** *** Destructors *)

Record Dtor' {lang} : Set := Build_Dtor
{ d_class  : classname' lang
; d_cc     : calling_conv
; d_body   : option (OrDefault (Stmt' lang))
}.
#[global] Arguments Dtor' : clear implicits.
#[global] Arguments Build_Dtor {_} & _ _ _ : assert.
#[global] Instance: forall {lang}, EqDecision (Dtor' lang).
Proof. solve_decision. Defined.
Notation Dtor := (Dtor' lang.cpp).

Variant Dtor_type : Set := Dt_Deleting | Dt_Complete | Dt_Base | Dt_Comdat.
#[global] Instance: EqDecision Dtor_type.
Proof. solve_decision. Defined.

(*
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
*)
