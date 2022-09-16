(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export bedrock.prelude.base.
Require Export bedrock.lang.cpp.ast.

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

Definition Nanon (ty : globname) : globname :=
  "#" ++ ty.

Definition Cenum_const (e : globname) (x : ident) : obj_name :=
  e ++ "::" ++ x.

Definition pure_virt (x : obj_name) : obj_name * option obj_name :=
  (x, None).
Definition impl_virt (x : obj_name) : obj_name * option obj_name :=
  (x, Some x).

Definition Sreturn_void : Stmt := Sreturn None.
Definition Sreturn_val (e : Expr) : Stmt := Sreturn (Some e).
Definition Sforeach (range ibegin iend : Stmt)
  (init : option Stmt) (cond : option Expr) (inc : option (ValCat * Expr))
  (decl body : Stmt) : Stmt :=
  Sseq [range; ibegin; iend; Sfor init cond inc
        (Sseq [decl; body])].

(* Indicate that [underlying] is used to represent alias type [name]. Enums are treated similarly. *)
Definition Talias (name : globname) {underlying : type} : type :=
  underlying.
Definition Tunderlying (enum : type) {underlying : type} : type :=
  underlying.

Definition mk_overrides (methods : list (obj_name * obj_name)) : list (obj_name * obj_name) := methods.

Definition mk_virtuals (methods : list (obj_name * option obj_name)) : list (obj_name * option obj_name) := methods.

Definition NStop : list ident := nil.

Bind Scope Z_scope with Z.

Declare Custom Entry cppglobal.

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
  Declare Scope cpp_scope.
  Delimit Scope cpp_scope with cpp.
  Notation "'``' e '``'" := e
    (at level 0, e custom cppglobal at level 200,
     format "`` e ``") : cpp_scope.
  Open Scope cpp_scope.
End cpp_notation.

Notation Tdecay_type ty := (Qconst (Tptr ty)) (only parsing).
Notation Tincomplete_array ty := (Qconst (Tptr ty)) (only parsing).
Notation Tvariable_array ty e := (Qconst (Tptr ty)) (only parsing).

(** this is the compatibility layer, cpp2v generates these definitions
 *)
Definition translation_unitK : Type :=
  symbol_table -> type_table -> (symbol_table -> type_table -> translation_unit) -> translation_unit.

(** TODO FM-601 don't ignore this *)
Definition Dstatic_assert (_ : option bs) (_ : Expr) : translation_unitK :=
  fun syms tys k => k syms tys.

Definition Dvariable (name : obj_name) (t : type) (init : option Expr) : translation_unitK :=
  fun syms tys k => k (<[ name := Ovar t init ]> syms) tys.

Definition Dfunction    (name : obj_name) (f : Func) : translation_unitK :=
  fun syms tys k => k (<[ name := Ofunction f ]> syms) tys.
Definition Dmethod    (name : obj_name) (f : Method) : translation_unitK :=
  fun syms tys k => k (<[ name := Omethod f ]> syms) tys.
Definition Dconstructor    (name : obj_name) (f : Ctor) : translation_unitK :=
  fun syms tys k => k (<[ name := Oconstructor f ]> syms) tys.
Definition Ddestructor    (name : obj_name) (f : Dtor) : translation_unitK :=
  fun syms tys k => k (<[ name := Odestructor f ]> syms) tys.

Definition Dunion (name : globname) (o : option Union) : translation_unitK :=
  fun syms tys k =>
    k syms (<[ name := match o with
                       | None => Gtype
                       | Some u => Gunion u
                       end ]> tys).
Definition Dstruct (name : globname) (o : option Struct) : translation_unitK :=
  fun syms tys k =>
    k syms (<[ name := match o with
                       | None => Gtype
                       | Some u => Gstruct u
                       end ]> tys).

(* named enumerations *)
Definition Denum (name : globname) (t : type) (branches : list (ident * BinNums.Z)) : translation_unitK :=
  fun syms tys k => k syms $ <[ name := Genum t (List.map fst branches) ]> tys.
(*
    let enum_ty := Tnamed name in
    let raw_ty :=
        match t with
        | None => enum_ty
        | Some t => t
        end
    in
    k syms (List.fold_left (fun acc '(nm, oe) => <[ Cenum_const name nm := Gconstant enum_ty (Some (Eint oe raw_ty)) ]> acc)
                           branches
                           match t with
                           | Some t => <[ name := Genum t (List.map fst branches) ]> tys
                           | None => tys
                           end). *)
  (* ^ enumerations (the initializers need to be constant expressions) *)

Definition Dconstant    (name : globname) (t : type) (e : Expr) : translation_unitK :=
  fun syms tys k => k syms $ <[ name := Gconstant t (Some e) ]> tys.
Definition Dconstant_undef  (name : globname) (t : type) : translation_unitK :=
  fun syms tys k => k syms $ <[ name := Gconstant t None ]> tys.
Definition Denum_constant (name : globname) (t : type) (v : Z) (init : option Expr) : translation_unitK :=
  fun syms tys k => k syms $ <[ name := Gconstant t (Some (Eint v t)) ]> tys.
Definition Dtypedef     (name : globname) (t : type) : translation_unitK :=
  fun syms tys k => k syms $ <[ name := Gtypedef t ]> tys.
Definition Dtype (name : globname) : translation_unitK :=
  fun syms tys k => k syms $ <[ name := Gtype ]> tys.
(* Definition translation_unit_canon (c : translation_unit) : translation_unit := *)
(*   {| symbols := avl.map_canon c.(symbols) *)
(*    ; globals := avl.map_canon c.(globals) |}. *)

Fixpoint decls' (ls : list translation_unitK) : translation_unitK :=
  match ls with
  | nil => fun syms tys k => k syms tys
  | m :: ms => fun syms tys k => m syms tys (fun s t => decls' ms s t k)
  end.

Definition decls ls (e : endian) : translation_unit :=
  decls' ls ∅ ∅ (fun a b => {| symbols := avl.map_canon a
                           ; globals := avl.map_canon b
                           ; initializer := nil (* FIXME *)
                           ; byte_order := e |}).

Declare Reduction reduce_translation_unit := vm_compute.
