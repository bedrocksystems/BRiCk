(*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export bedrock.prelude.base.
Require bedrock.prelude.option.
Require Export bedrock.lang.cpp.ast.

(** * Derived forms used by cpp2v *)

(**
TODO: Most definitions in this file exists for use in cpp2v-generated
code where they are immediately reduced away. They could be tucked
into a module that only gets imported by cpp2v-generated files.
*)

(** ** Notations *)
(**
TODO: These seem misplaced.
*)

Declare Custom Entry cppglobal.

Declare Scope cpp_scope.
Delimit Scope cpp_scope with cpp.

Declare Scope cppfield_scope.
Delimit Scope cppfield_scope with field.
Bind Scope cppfield_scope with field.

(* XXX This is only parsing to work around Coq misusing it outside
[cppfield_scope]. See #235. *)
Notation "` e `" := e (e custom cppglobal at level 200, at level 0,
  only parsing) : cppfield_scope.

(** Importing [cpp_notation] makes cpp2v-generated names generally
available as, e.g., [``::MyClass``]. *)
Module Export cpp_notation.
  Notation "'``' e '``'" := e
    (at level 0, e custom cppglobal at level 200,
     format "`` e ``") : cpp_scope.
  Open Scope cpp_scope.
End cpp_notation.

(** ** Names *)

Fixpoint do_end (ty : globname) : obj_name :=
  match ty with
  | BS.String _ BS.EmptyString => "D0Ev"
  | BS.String x v => BS.String x (do_end v)
  | _ => BS.EmptyString
  end.

(** Build the name of a destructor for a type.
    NOTE this can be improved if we essentially turn it into a
    constructor of [obj_name]; however, that has some wider
    implications that we should solve in a separate issue.
 *)
Definition DTOR (ty : globname) : obj_name :=
  match ty with
  | BS.String _ (BS.String _ ((BS.String c _) as rest)) =>
    if bool_decide (c = "N"%byte) then
      "_Z" ++ do_end rest
    else
      "_ZN" ++ rest ++ "D0Ev"
  | BS.String _ (BS.String _ v) => "_ZN" ++ do_end v
  | _ => "OOPS"
  end%bs.

Definition Nanon (ty : globname) : ident :=
  "#" ++ ty.

Definition pure_virt (x : obj_name) : obj_name * option obj_name :=
  (x, None).
Definition impl_virt (x : obj_name) : obj_name * option obj_name :=
  (x, Some x).

Definition mk_overrides (methods : list (obj_name * obj_name)) : list (obj_name * obj_name) := methods.

Definition mk_virtuals (methods : list (obj_name * option obj_name)) : list (obj_name * option obj_name) := methods.

(** ** Types *)

Section type.
  Context {type : Set}.

  (**
  Unsupported types. [description] is meant to be only used for
  documentation.
  *)
  Definition Tunsupported `{!Inhabited type} (description : bs) : type.
  Proof. exact inhabitant. Qed.

  (*
  Indicate that [underlying] is used to represent alias type [name].
  Enums are treated similarly.
  *)
  Definition Talias (name : globname) {underlying : type} : type :=
    underlying.
  Definition Tunderlying (enum : type) {underlying : type} : type :=
    underlying.
  Definition Tunary_xform (name : bs) (arg : type) {result : type} : type :=
    result.

End type.
Notation Tdecay_type original adjusted := (adjusted) (only parsing).
Notation Tvariable_array ty e := (types.Tvariable_array ty) (only parsing).

(** ** Expressions *)

Definition Eoperator_member_call (oo : OverloadableOperator) (nm : obj_name) (ct : dispatch_type) (ft : type) (obj : Expr) (es : list Expr) (ty : type) : Expr :=
  Eoperator_call oo (operator_impl.MFunc nm ct ft) (obj :: es) ty.

Definition Eoperator_call (oo : OverloadableOperator) (f : obj_name) (ft : type) (es : list Expr) (ty : type) : Expr :=
  Eoperator_call oo (operator_impl.Func f ft) es ty.

Definition Eenum_const_at (e : globname) (c : ident) (ty : exprtype) : Expr :=
  Ecast Cintegral (Eenum_const e c) Prvalue ty.

Definition Ebuiltin (nm : obj_name) (ty : type) : Expr :=
  Ecast Cbuiltin2fun (Eglobal nm ty) Prvalue (Tptr ty).

Definition Emember (arrow : bool) (e : Expr) (f : ident + obj_name) (mut : bool) (ty : decltype) : _ :=
  option.get_some $
    let e :=
      if arrow then
        match drop_qualifiers $ type_of e with
        | Tptr t => Some (Ederef e t)
        | _ => None
        end
      else
        Some e
    in
    (fun e => match f with
           | inr nm => Ecomma e (Eglobal nm ty)
           | inl f => Emember e f mut ty
           end) <$> e.

Notation Allocating := new_form.Allocating (only parsing).
Notation NonAllocating := new_form.NonAllocating (only parsing).

(** ** Statements *)

Section stmt.
  Context {obj_name type Expr : Set}.
  #[local] Notation Stmt := (Stmt' obj_name type Expr).

  Definition Sreturn_void : Stmt := Sreturn None.
  Definition Sreturn_val (e : Expr) : Stmt := Sreturn (Some e).
  Definition Sforeach (range ibegin iend : Stmt)
      (init : option Stmt) (cond : option Expr) (inc : option Expr)
      (decl body : Stmt) : Stmt :=
    Sseq [range; ibegin; iend; Sfor init cond inc (Sseq [decl; body])].
End stmt.

(** ** Translation units *)

Definition translation_unitK : Type :=
  symbol_table -> type_table -> (symbol_table -> type_table -> translation_unit) -> translation_unit.

(** TODO FM-601 don't ignore this *)
Definition Dstatic_assert (_ : option bs) (_ : Expr) : translation_unitK :=
  fun syms tys k =>
  k syms tys.

Definition Dvariable (name : obj_name) (t : type) (init : option Expr) : translation_unitK :=
  fun syms tys k =>
  k (<[ name := Ovar t init ]> syms) tys.

Definition Dfunction (name : obj_name) (f : Func) : translation_unitK :=
  fun syms tys k =>
  k (<[ name := Ofunction f ]> syms) tys.

Definition Dmethod (name : obj_name) (static : bool) (f : Method) : translation_unitK :=
  fun syms tys k =>
    let add := if static then Ofunction $ static_method f else Omethod f in
      k (<[ name := add ]> syms) tys.

Definition Dconstructor (name : obj_name) (f : Ctor) : translation_unitK :=
  fun syms tys k =>
  k (<[ name := Oconstructor f ]> syms) tys.

Definition Ddestructor (name : obj_name) (f : Dtor) : translation_unitK :=
  fun syms tys k =>
  k (<[ name := Odestructor f ]> syms) tys.

Definition Dunion (name : globname) (o : option Union) : translation_unitK :=
  fun syms tys k =>
  k syms (<[ name := from_option Gunion Gtype o ]> tys).

Definition Dstruct (name : globname) (o : option Struct) : translation_unitK :=
  fun syms tys k =>
  k syms (<[ name := from_option Gstruct Gtype o ]> tys).

Definition Denum (name : globname) (t : type) (branches : list ident) : translation_unitK :=
  fun syms tys k =>
  k syms $ <[ name := Genum t branches ]> tys.

Definition Denum_constant (name : globname)
    (gn : globname) (ut : exprtype) (v : N + Z) (init : option Expr) : translation_unitK :=
  fun syms tys k =>
  let v := match v with inl n => Echar n ut | inr z => Eint z ut end in
  let t := Tenum gn in
  k syms $ <[ name := Gconstant t (Some (Ecast Cintegral v Prvalue t)) ]> tys.

Definition Dtypedef (name : globname) (t : type) : translation_unitK :=
  fun syms tys k =>
  k syms $ <[ name := Gtypedef t ]> tys.

Definition Dtype (name : globname) : translation_unitK :=
  fun syms tys k =>
  k syms $ <[ name := Gtype ]> tys.

(* Definition translation_unit_canon (c : translation_unit) : translation_unit := *)
(*   {| symbols := avl.map_canon c.(symbols) *)
(*    ; types := avl.map_canon c.(types) |}. *)

Fixpoint decls' (ls : list translation_unitK) : translation_unitK :=
  match ls with
  | nil => fun syms tys k => k syms tys
  | m :: ms => fun syms tys k => m syms tys (fun s t => decls' ms s t k)
  end.

Definition decls ls (e : endian) : translation_unit :=
  decls' ls ∅ ∅ $ fun a b =>
  {| symbols := avl.map_canon a
  ; types := avl.map_canon b
  ; initializer := nil (* FIXME *)
  ; byte_order := e |}.

Declare Reduction reduce_translation_unit := vm_compute.
