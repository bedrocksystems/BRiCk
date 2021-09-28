(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.fin_maps.
From bedrock.prelude Require Import base avl.
From bedrock.lang.cpp.syntax Require Import names expr stmt types.

#[local] Set Primitive Projections.

(** Record an offset in _bits_. *)
Record LayoutInfo : Set :=
{ li_offset : Z }.
Instance: EqDecision LayoutInfo.
Proof. solve_decision. Defined.

Variant InitPath : Set :=
| InitBase (_ : globname)
| InitField (_ : ident)
| InitIndirect (anon_path : list (ident * globname)) (_ : ident)
| InitThis.
Instance: EqDecision InitPath.
Proof. solve_decision. Defined.

Record Initializer :=
  { init_path : InitPath
  ; init_type : type
  ; init_init : Expr }.
Instance: EqDecision Initializer.
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
; d_body   : option (OrDefault Stmt)
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
; m_body    : option (OrDefault Stmt)
}.
Instance: EqDecision Method.
Proof. solve_decision. Defined.

Record Member : Set := mkMember
{ mem_name : ident
; mem_type : type
; mem_init : option Expr
; mem_layout : LayoutInfo }.
Instance: EqDecision Member.
Proof. solve_decision. Defined.


Record Union : Set :=
{ u_fields : list Member
  (* ^ fields with type, initializer, and layout information *)
; u_dtor : obj_name
  (* ^ the name of the destructor *)
; u_trivially_destructible : bool
  (* ^ whether objects of the union type are trivially destructible. *)
; u_size : N
  (* ^ size of the union (including padding) *)
; u_alignment : N
  (* ^ alignment of the union *)
}.
Instance: EqDecision Union.
Proof. solve_decision. Defined.


Variant LayoutType : Set := POD | Standard | Unspecified.
Instance: EqDecision LayoutType.
Proof. solve_decision. Defined.


Record Struct : Set :=
{ s_bases : list (globname * LayoutInfo)
  (* ^ base classes *)
; s_fields : list Member
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
; s_layout : LayoutType
  (* ^ the type of layout semantics *)
(* The remaining fields are implementation-dependent. They might be mandated by the per-platform ABI. *)
; s_size : N
  (* ^ size of the structure (including padding) *)
; s_alignment : N
  (* ^ alignment of the structure *)
}.
Instance: EqDecision Struct.
Proof. solve_decision. Defined.

Definition has_vtable (s : Struct) : bool :=
  match s.(s_virtuals) with
  | nil => false
  | _ :: _ => true
  end.

(* [has_virtual_dtor s] returns true if the destructor is virtual. *)
Definition has_virtual_dtor (s : Struct) : bool :=
  List.existsb (fun '(a,_) => bool_decide (a = s.(s_dtor))) s.(s_virtuals).

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

(* [Tmember_func ty fty] constructs the function type for a
     member function that takes a [this] parameter of [ty]

   TODO technically the [this] parameter is [const], but we are not
        treating [const] correctly right now, so we make it non-const
        in the type. The C++ typesystem prevents us from attempting to
        modify the value of [this] since it is not an Lvalue.
 *)
Definition Tmember_func (ty : type) (fty : type) : type :=
  match fty with
  | @Tfunction cc ret args => Tfunction (cc:=cc) ret (Tptr ty :: args)
  | _ => fty
  end.

(** [type_of_value o] returns the type of the given [ObjValue] *)
Definition type_of_value (o : ObjValue) : type :=
  normalize_type
  match o with
  | Ovar t _ => t
  | Ofunction f => Tfunction (cc:=f.(f_cc)) f.(f_return) $ snd <$> f.(f_params)
  | Omethod m =>
    Tmember_func (Tqualified m.(m_this_qual) (Tnamed m.(m_class))) $ Tfunction (cc:=m.(m_cc)) m.(m_return) $ snd <$> m.(m_params)
  | Oconstructor c =>
    Tmember_func (Tnamed c.(c_class)) $ Tfunction (cc:=c.(c_cc)) Tvoid $ snd <$> c.(c_params)
  | Odestructor d =>
    Tmember_func (Tnamed d.(d_class)) $ Tfunction (cc:=d.(d_cc)) Tvoid nil
  end.

Variant GlobDecl : Set :=
| Gtype     (* this is a type declaration, but not a definition *)
| Gunion    (_ : Union) (* union body *)
| Gstruct   (_ : Struct) (* struct body *)
| Genum     (_ : type) (_ : list ident) (* *)
| Gconstant (_ : type) (init : option Expr) (* used for enumerator constants*)
| Gtypedef  (_ : type).
Instance: EqDecision GlobDecl.
Proof. solve_decision. Defined.

Definition symbol_table : Type := IM.t ObjValue.

Definition type_table : Type := IM.t GlobDecl.

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
  (*
  To traverse a type definition and compute, say, its list of subobjects,
  we require that the type is _complete_, as in the usual sense.

  This definition is adapted from Krebbers'15, Definition 3.3.5, with needed
  adjustments for C++.

  Unlike Krebbers:
  - our [type_table] are not ordered
  - [complete_named] takes a proof of [complete_decl] to simplify its use for consumers,
    so we'd naively recheck a struct wherever needed; but an actual checker can
    be smarter (it could use a state monad carrying a map of known-complete types).

  The C++ standard defines and constrains "(in)complete type"s at
  https://eel.is/c++draft/basic.types.general#def:object_type,incompletely-defined,
  and constraints it at https://eel.is/c++draft/basic.scope.pdecl#6,
  https://eel.is/c++draft/class.mem#def:data_member,
  https://eel.is/c++draft/basic.def.odr#12,
  https://eel.is/c++draft/basic.def#5.
  *)

  (* Check that [g : GlobDecl] is complete in environment [te]. *)
  Inductive complete_decl : GlobDecl -> Prop :=
  (* We intentionally omit Krebbers' clauses checking the aggregate is not
  empty: empty aggregates are legal in full C/C++ (see
  [cpp2v-tests/test_translation_unit_validity.cpp]). *)
  | complete_Struct {st}
              (_ : forall b li, In (b, li) st.(s_bases) -> complete_type (Tnamed b))
              (_ : forall x t e li, In (mkMember x t e li) st.(s_fields) -> complete_type t)
    : complete_decl (Gstruct st)
  | complete_Union {u}
              (_ : forall x t e li, In (mkMember x t e li) u.(u_fields) -> complete_type t)
    : complete_decl (Gunion u)
  | complete_enum {t consts} (_ : complete_type t)
    : complete_decl (Genum t consts)
  (* No need for typedefs since those are forbidden in `Tnamed`, `Gtype` isn't
  legal, `Gconstant` is illegal and wouldn't make sense. *)

  (* Basic types. This excludes references (as checked by [complete_basic_type_not_ref]). *)
  with complete_basic_type : type -> Prop :=
  | complete_float sz : complete_basic_type (Tfloat sz)
  | complete_int sgn sz : complete_basic_type (Tint sgn sz)
  | complete_bool : complete_basic_type Tbool
  | complete_void : complete_basic_type Tvoid
  | complete_nullptr : complete_basic_type Tnullptr
  (* t can in turn be a pointer type *)
  | complete_ptr {t} : complete_pointee_type t -> complete_basic_type (Tptr t)

  (* [complete_pointee_type t] says that a pointer/reference to [t] is complete.
     This excludes references (as checked by [complete_pointee_type_not_ref])
     since they cannot be nested. *)
  with complete_pointee_type : type -> Prop :=
  | complete_pt_qualified {q t} (_ : complete_pointee_type t)
    : complete_pointee_type (Tqualified q t)
  (*
    Pointers to array are only legal if the array is complete, at least
    in C, since they cannot actually be indexed or created.
    This rejects the invalid C:

    [struct T; int foo(struct T x[][10]);]

    However, C++ compilers appear to accept this code, which we cover
    in [wellscoped_array].
    *)
  | complete_pt_array t n
    (_ : (n <> 0)%N) (* From Krebbers. Probably needed to reject [T[][]]. *)
    (_ : complete_type t) :
    complete_pointee_type (Tarray t n)
  | complete_pt_named {n decl} :
    (* This check could not appear in a Krebbers-style definition.
       And it is not needed to enable computation on complete types.
     *)
    te !! n = Some decl ->
    complete_pointee_type (Tnamed n)
  (* Beware:
  [Tfunction] represents a function type; somewhat counterintuitively,
  a pointer to a function type is complete even if the argument/return types
  are not complete but only well-scoped, you're just forbidden from
  actually invoking the pointer; this follows Krebbers'15 3.3.5. *)
  | complete_pt_function {cc ret args}
      (_ : wellscoped_type ret)
      (_ : wellscoped_types args)
    : complete_pointee_type (Tfunction (cc:=cc) ret args)
  | complete_pt_basic t :
    complete_basic_type t ->
    complete_pointee_type t
  (* [complete_type t] says that type [t] is well-formed, that is, complete. *)
  with complete_type : type -> Prop :=
  | complete_qualified {q t} (_ : complete_type t)
    : complete_type (Tqualified q t)
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
  | complete_named {n decl} (_ : te !! n = Some decl)
                    (_ : complete_decl decl) :
    complete_type (Tnamed n)
  | complete_array {t n}
    (_ : (n <> 0)%N) (* Needed? from Krebbers*)
    (_ : complete_type t) :
    complete_type (Tarray t n)
  | complete_member_pointer {n t} (_ : not_ref_type t)
      (_ : complete_pointee_type (Tnamed n))
      (_ : complete_pointee_type t)
    : complete_type (Tmember_pointer n t)
  | complete_function {cc ret args} :
    (*
    We could probably omit this constructor, and consider function types as not
    complete; "complete function types" do not exist in the standard, and
    [complete_symbol_table] does not use the concept.
     *)
    complete_pointee_type (Tfunction (cc:=cc) ret args) ->
    complete_type (Tfunction (cc:=cc) ret args)
  | complete_basic t :
    complete_basic_type t ->
    complete_type t
  (** Well-scoped arguments cannot mention undeclared types. Krebbers identifies
  them with valid pointee, but that breaks down in C++ due to references. *)
  with wellscoped_type : type -> Prop :=
  | wellscoped_qualified {q t} (_ : wellscoped_type t)
    : wellscoped_type (Tqualified q t)
  | wellscoped_array t n
    (_ : (n <> 0)%N) : (* From Krebbers. Probably needed to reject [T[][]]. *)
    wellscoped_type t ->
    wellscoped_type (Tarray t n)
  | wellscoped_pointee t :
    complete_pointee_type t ->
    wellscoped_type t
  (* covers references. *)
  | wellscoped_complete {t} :
    complete_type t ->
    wellscoped_type t
  with wellscoped_types : list type -> Prop :=
  | wellscoped_nil : wellscoped_types []
  | wellscoped_cons t ts :
    wellscoped_type t ->
    wellscoped_types ts ->
    wellscoped_types (t :: ts).

  Inductive valid_decl : GlobDecl -> Prop :=
  | valid_typedef t :
    (*
    All typedefs in use have been inlined at their use-site, so we don't enforce
    their validity.

    In addition, we can't enforce their validity because `clang` produces
    builtin typedefs with ill-scoped bodies, such as
    [(Dtypedef "__NSConstantString" (Tnamed "_Z22__NSConstantString_tag")) :: ... ::
    (Dtypedef "__builtin_va_list" (Tarray (Tnamed "_Z13__va_list_tag") 1)) ::]. *)
    (* wellscoped_type t -> *)
    valid_decl (Gtypedef t)
  | valid_type : valid_decl Gtype
  | valid_const t oe :
    (* Potentially redundant. *)
    wellscoped_type t ->
    valid_decl (Gconstant t oe)
  | valid_complete_decl g :
    complete_decl g -> valid_decl g.
End with_type_table.

Scheme complete_decl_mut_ind := Minimality for complete_decl Sort Prop
with complete_basic_type_mut_ind := Minimality for complete_basic_type Sort Prop
with complete_pointee_type_mut_ind := Minimality for complete_pointee_type Sort Prop
with complete_type_mut_ind := Minimality for complete_type Sort Prop
with wellscoped_type_mut_ind := Minimality for wellscoped_type Sort Prop
with wellscoped_types_mut_ind := Minimality for wellscoped_types Sort Prop.

Combined Scheme complete_mut_ind from complete_decl_mut_ind, complete_basic_type_mut_ind,
  complete_pointee_type_mut_ind, complete_type_mut_ind,
  wellscoped_type_mut_ind, wellscoped_types_mut_ind.

Lemma complete_basic_type_not_ref te t : complete_basic_type te t → not_ref_type t.
Proof. by inversion 1. Qed.
Lemma complete_pointee_type_not_ref te t : complete_pointee_type te t → not_ref_type t.
Proof. induction 1; by [eapply complete_basic_type_not_ref | ]. Qed.

Lemma complete_type_not_ref_ref te t1 t2 : complete_type te t1 → ref_to_type t1 = Some t2 → not_ref_type t2.
Proof.
  induction 1 => Hsome; simplify_eq/=; generalize dependent te => te;
    try by [exact: complete_pointee_type_not_ref| tauto].
  move => /complete_basic_type_not_ref; naive_solver.
Qed.

(**
Adapted from Krebbers'15, Definition 3.3.6:
- all member types must be complete
- all function types must be pointer-complete as defined above.
*)
Definition complete_type_table (te : type_table) :=
  map_Forall (fun _key d => valid_decl te d) te.

Definition complete_symbol_table (te : type_table) (syms : symbol_table) :=
  map_Forall (fun _key d => complete_pointee_type te (type_of_value d)) syms.

Definition complete_translation_unit (te : type_table) (syms : symbol_table) :=
  complete_type_table te /\ complete_symbol_table te syms.

(*
#[global] Instance complete_type_table_dec te : Decision (complete_type_table te).
Proof.
apply: map_Forall_dec.
(* unshelve eapply map_Forall_dec; try apply _. *)
*)

(*
TODOs for FM-216:
1. prove [complete_type_table_dec] above with an efficient checker.
2. add [bool_decide (complete_type_table globals = true] to translation_unit;
   that's automatically proof-irrelevant, and proofs are just cheap [eq_refl].
3. add any helper lemmas, say for proving equality of [translation_unit] from
   equality of the relevant componets.

Twist: the "decision procedure" likely requires fuel; find how to adapt the
above plan. We'll likely end up with a boolean checker proven correct.

Question: do we need [complete_symbol_table]? This is not expected.

Goal: enable recursion on proofs of [complete_type_table], e.g. for defining
[anyR] (FM-215).
*)

(**
A [translation_unit] value represents all the statically known information
about a C++ translation unit, that is, a source file.
TOOD: add support for symbols with _internal_ linkage.
TODO: does linking induce a (non-commutative) monoid on object files? Is then
a translation unit a "singleton" value in this monoid? *)
Record translation_unit : Type :=
{ symbols    : symbol_table
; globals    : type_table
; byte_order : endian
}.

Instance global_lookup : Lookup globname GlobDecl translation_unit :=
  fun k m => m.(globals) !! k.
Instance symbol_lookup : Lookup obj_name ObjValue translation_unit :=
  fun k m => m.(symbols) !! k.
