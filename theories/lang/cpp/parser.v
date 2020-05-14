(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Export
        Coq.Lists.List
        Coq.ZArith.BinInt.

Require Import stdpp.gmap.
Require Export bedrock.lang.cpp.ast.

Set Default Proof Using "Type".

Definition Nanon (ty : globname) : globname :=
  ("#" ++ ty)%bs.

Definition Talias (underlying : type) (name : globname) : type :=
  underlying.

Definition NStop : list ident := nil.

Bind Scope Z_scope with Z.

Declare Custom Entry cppglobal.
Declare Scope cppfield_scope.
Delimit Scope cppfield_scope with field.
Bind Scope cppfield_scope with field.

Notation "` e `" := e (e custom cppglobal at level 200, at level 0) : cppfield_scope.


(** this is the compatibility layer, cpp2v generates these definitions
 *)
(* HACK to get around the fact that [gmap_empty] is opaque. *)
(* Local Definition empty_symbols : symbol_table := *)
(*   Eval vm_compute in gmap_empty. *)
(* Local Definition empty_globals : type_table := *)
(*   Eval vm_compute in gmap_empty. *)
(* Local Instance symbol_table_empty_trans : Empty symbol_table := empty_symbols. *)
(* Local Instance type_table_empty_trans : Empty type_table := empty_globals. *)

Definition compilation_unitK : Type :=
  symbol_table -> type_table -> (symbol_table -> type_table -> compilation_unit) -> compilation_unit.

Definition Dvar (name : obj_name) (t : type) (init : option Expr) : compilation_unitK :=
  fun syms tys k => k (<[ name := Ovar t init ]> syms) tys.

Definition Dfunction    (name : obj_name) (f : Func) : compilation_unitK :=
  fun syms tys k => k (<[ name := Ofunction f ]> syms) tys.
Definition Dmethod    (name : obj_name) (f : Method) : compilation_unitK :=
  fun syms tys k => k (<[ name := Omethod f ]> syms) tys.
Definition Dconstructor    (name : obj_name) (f : Ctor) : compilation_unitK :=
  fun syms tys k => k (<[ name := Oconstructor f ]> syms) tys.
Definition Ddestructor    (name : obj_name) (f : Dtor) : compilation_unitK :=
  fun syms tys k => k (<[ name := Odestructor f ]> syms) tys.

Definition Dunion (name : globname) (o : option Union) : compilation_unitK :=
  fun syms tys k =>
    k syms (<[ name := match o with
                       | None => Gtype
                       | Some u => Gunion u
                       end ]> tys).
Definition Dstruct (name : globname) (o : option Struct) : compilation_unitK :=
  fun syms tys k =>
    k syms (<[ name := match o with
                       | None => Gtype
                       | Some u => Gstruct u
                       end ]> tys).

Definition Denum (name : globname) (t : option type) (branches : list (ident * BinNums.Z)) : compilation_unitK :=
  fun syms tys k =>
    let enum_ty := Tnamed name in
    let raw_ty :=
        match t with
        | None => enum_ty
        | Some t => t
        end
    in
    k syms (List.fold_left (fun acc '(nm, oe) => <[ nm := Gconstant enum_ty (Some (Eint oe raw_ty)) ]> acc) 
                           branches
                           match t with
                           | Some t => <[ name := Genum t (List.map fst branches) ]> tys
                           | None => tys
                           end).
  (* ^ enumerations (the initializers need to be constant expressions) *)

Definition Dconstant    (name : globname) (t : type) (e : Expr) : compilation_unitK :=
  fun syms tys k => k syms (<[ name := Gconstant t (Some e) ]> tys).
Definition Dconstant_undef  (name : globname) (t : type) : compilation_unitK :=
  fun syms tys k => k syms (<[ name := Gconstant t None ]> tys).
Definition Dtypedef     (name : globname) (t : type) : compilation_unitK :=
  fun syms tys k => k syms (<[ name := Gtypedef t ]> tys).
Definition Dtype (name : globname) : compilation_unitK :=
  fun syms tys k => k syms (<[ name := Gtype ]> tys).
Definition compilation_unit_canon (c : compilation_unit) : compilation_unit :=
  {| symbols := avl.map_canon c.(symbols)
   ; globals := avl.map_canon c.(globals) |}.

Fixpoint decls' (ls : list compilation_unitK) : compilation_unitK :=
  match ls with
  | nil => fun syms tys k => k syms tys
  | m :: ms => fun syms tys k => m syms tys (fun s t => decls' ms s t k)
  end.

Definition decls ls : compilation_unit :=
  decls' ls ∅ ∅ (fun a b => {| symbols := avl.map_canon a
                           ; globals := avl.map_canon b |}).

Declare Reduction reduce_compilation_unit := vm_compute.

Export Bytestring.
