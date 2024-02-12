(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.syntax.names.
Require Import bedrock.lang.cpp.syntax.expr.
Require Import bedrock.lang.cpp.syntax.stmt.
Require Import bedrock.lang.cpp.syntax.types.

#[local] Notation EqDecision1 T := (∀ (A : Set), EqDecision A -> EqDecision (T A)) (only parsing).
#[local] Notation EqDecision2 T := (∀ (A : Set), EqDecision A -> EqDecision1 (T A)) (only parsing).
#[local] Notation EqDecision3 T := (∀ (A : Set), EqDecision A -> EqDecision2 (T A)) (only parsing).
#[local] Tactic Notation "solve_decision" := intros; solve_decision.

(** ** Type Declarations *)

(** Record an offset in _bits_. *)
Record LayoutInfo : Set :=
{ li_offset : Z }.
#[global] Instance: EqDecision LayoutInfo.
Proof. solve_decision. Defined.

Record Member' {type Expr : Set} : Set := mkMember
{ mem_name : ident
; mem_type : type
; mem_mutable : bool
; mem_init : option Expr
; mem_layout : LayoutInfo }.
#[global] Arguments Member' _ _ : clear implicits, assert.
#[global] Arguments mkMember {_ _} &.
#[global] Instance: EqDecision2 Member'.
Proof. solve_decision. Defined.
Notation Member := (Member' type Expr).

Record Union' {type Expr : Set} : Set := Build_Union
{ u_fields : list (Member' type Expr)
  (* ^ fields with type, initializer, and layout information *)
; u_dtor : obj_name
  (* ^ the name of the destructor *)
; u_trivially_destructible : bool
  (* ^ whether objects of the union type are trivially destructible. *)
; u_delete : option obj_name
  (* ^ name of [operator delete], if it exists *)
; u_size : N
  (* ^ size of the union (including padding) *)
; u_alignment : N
  (* ^ alignment of the union *)
}.
#[global] Arguments Union' _ _ : clear implicits, assert.
#[global] Arguments Build_Union {_ _} &.
#[global] Instance: EqDecision2 Union'.
Proof. solve_decision. Defined.
Notation Union := (Union' type Expr).


Variant LayoutType : Set := POD | Standard | Unspecified.
#[global] Instance: EqDecision LayoutType.
Proof. solve_decision. Defined.


Record Struct' {classname type Expr : Set} : Set := Build_Struct
{ s_bases : list (classname * LayoutInfo)
  (* ^ base classes *)
; s_fields : list (Member' type Expr)
  (* ^ fields with type, initializer, and layout information *)
; s_virtuals : list (obj_name * option obj_name)
  (* ^ function_name -> symbol *)
; s_overrides : list (obj_name * obj_name)
  (* ^ k |-> v ~ update k with v *)
; s_dtor : obj_name
  (* ^ the name of the destructor.
     NOTE at the C++ abstract machine level, there is only
          one destructor, but implementations (and name mangling)
          use multiple destructors in cases of classes with [virtual]
          inheritence.
   *)
; s_trivially_destructible : bool
  (* ^ this is actually computable, and we could compute it *)
; s_delete : option obj_name
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
#[global] Arguments Struct' _ _ _ : clear implicits, assert.
#[global] Arguments Build_Struct {_ _ _} &.
#[global] Instance: EqDecision3 Struct'.
Proof. solve_decision. Defined.
Notation Struct := (Struct' globname type Expr).

(** [has_vtable s] determines whether [s] has any <<virtual>> methods
    (or bases). Having a vtable is *not* a transitive property.
    A class that only inherits <<virtual>> methods does not have a
    vtable.
 *)
Definition has_vtable {classname type Expr} (s : Struct' classname type Expr) : bool :=
  match s.(s_virtuals) with
  | nil => false
  | _ :: _ => true
  end.
#[global] Arguments has_vtable _ _ _ & _ : assert.

(* [has_virtual_dtor s] returns true if the destructor is virtual. *)
Definition has_virtual_dtor {classname type Expr} (s : Struct' classname type Expr) : bool :=
  List.existsb (fun '(a,_) => bool_decide (a = s.(s_dtor))) s.(s_virtuals).
#[global] Arguments has_virtual_dtor _ _ _ & _ : assert.

Variant Ctor_type : Set := Ct_Complete | Ct_Base | Ct_alloc | Ct_Comdat.
#[global] Instance: EqDecision Ctor_type.
Proof. solve_decision. Defined.


(** ** Value Declarations *)

(** *** Functions *)
Variant FunctionBody' {type Expr : Set} : Set :=
| Impl (_ : Stmt' type Expr)
| Builtin (_ : BuiltinFn)
.
#[global] Arguments FunctionBody' _ _ : clear implicits, assert.
#[global] Arguments Impl _ _ &.
#[global] Instance: EqDecision2 FunctionBody'.
Proof. solve_decision. Defined.
Notation FunctionBody := (FunctionBody' decltype Expr).

Record Func' {type Expr : Set} : Set := Build_Func
{ f_return : type
; f_params : list (ident * type)
; f_cc     : calling_conv
; f_arity  : function_arity
; f_body   : option (FunctionBody' type Expr)
}.
#[global] Arguments Func' _ _ : clear implicits, assert.
#[global] Arguments Build_Func {_ _} &.
#[global] Instance: EqDecision2 Func'.
Proof. solve_decision. Defined.
#[global] Instance Func_inhabited {type Expr : Set} `{!Inhabited type} :
  Inhabited (Func' type Expr).
Proof. solve_inhabited. Qed.
Notation Func := (Func' decltype Expr).

(** *** Methods *)

Record Method' {classname type Expr : Set} : Set := Build_Method
{ m_return  : type
; m_class   : classname
; m_this_qual : type_qualifiers
; m_params  : list (ident * type)
; m_cc      : calling_conv
; m_arity   : function_arity
; m_body    : option (OrDefault (Stmt' type Expr))
}.
#[global] Arguments Method' _ _ _ : clear implicits, assert.
#[global] Arguments Build_Method {_ _ _} &.
#[global] Instance: EqDecision3 Method'.
Proof. solve_decision. Defined.
Notation Method := (Method' globname decltype Expr).

Definition static_method {classname type Expr : Set} (m : Method' classname type Expr)
  : Func' type Expr :=
  {| f_return := m.(m_return)
   ; f_params := m.(m_params)
   ; f_cc := m.(m_cc)
   ; f_arity := m.(m_arity)
   ; f_body := match m.(m_body) with
               | Some (UserDefined body) => Some (Impl body)
               | _ => None
               end |}.



(** *** Constructors *)

Variant InitPath' {classname : Set} : Set :=
| InitBase (_ : classname)
| InitField (_ : ident)
| InitIndirect (anon_path : list (ident * classname)) (_ : ident)
| InitThis.
#[global] Arguments InitPath' _ : clear implicits, assert.
#[global] Instance: EqDecision1 InitPath'.
Proof. solve_decision. Defined.
#[global] Notation InitPath := (InitPath' globname).

Record Initializer' {classname type Expr : Set} : Set := Build_Initializer
  { init_path : InitPath' classname
  ; init_type : type
  ; init_init : Expr }.
#[global] Arguments Initializer' _ _ _ : clear implicits, assert.
#[global] Arguments Build_Initializer {_ _ _} &.
#[global] Instance: EqDecision3 Initializer'.
Proof. solve_decision. Defined.
Notation Initializer := (Initializer' globname decltype Expr).

Record Ctor' {classname type Expr : Set} : Set := Build_Ctor
{ c_class  : classname
; c_params : list (ident * type)
; c_cc     : calling_conv
; c_arity  : function_arity
; c_body   : option (OrDefault (list (Initializer' classname type Expr) * Stmt' type Expr))
}.
#[global] Arguments Ctor' _ _ _ : clear implicits, assert.
#[global] Arguments Build_Ctor {_ _ _} &.
#[global] Instance: EqDecision3 Ctor'.
Proof. solve_decision. Defined.
Notation Ctor := (Ctor' globname decltype Expr).

(** *** Destructors *)

Record Dtor' {classname type Expr : Set} : Set := Build_Dtor
{ d_class  : classname
; d_cc     : calling_conv
; d_body   : option (OrDefault (Stmt' type Expr))
}.
#[global] Arguments Dtor' _ _ _ : clear implicits, assert.
#[global] Arguments Build_Dtor {_ _ _} &.
#[global] Instance: EqDecision3 Dtor'.
Proof. solve_decision. Defined.
Notation Dtor := (Dtor' globname decltype Expr).

Variant Dtor_type : Set := Dt_Deleting | Dt_Complete | Dt_Base | Dt_Comdat.
#[global] Instance: EqDecision Dtor_type.
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

(* [Tmember_func ty fty] constructs the function type for a
     member function that takes a [this] parameter of [ty]

   TODO technically the [this] parameter is [const].
 *)
Definition Tmember_func (ty : exprtype) (fty : functype) : functype :=
  match fty with
  | @Tfunction cc ar ret args => Tfunction (cc:=cc) (ar:=ar) ret (Tptr ty :: args)
  | _ => fty
  end.
