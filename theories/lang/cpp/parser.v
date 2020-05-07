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
Local Definition empty_symbols : symbol_table :=
  Eval vm_compute in gmap_empty.
Local Definition empty_globals : type_table :=
  Eval vm_compute in gmap_empty.
Local Instance symbol_table_empty_trans : Empty symbol_table := empty_symbols.
Local Instance type_table_empty_trans : Empty type_table := empty_globals.

Definition Dvar (name : obj_name) (t : type) (init : option Expr) : translation_unit :=
  {| symbols := {[ name := Ovar t init ]}
   ; globals := ∅ |}.

Definition Dfunction    (name : obj_name) (f : Func) : translation_unit :=
  {| symbols := {[ name := Ofunction f ]}
   ; globals := ∅ |}.
Definition Dmethod    (name : obj_name) (f : Method) : translation_unit :=
  {| symbols := {[ name := Omethod f ]}
   ; globals := ∅ |}.
Definition Dconstructor    (name : obj_name) (f : Ctor) : translation_unit :=
  {| symbols := {[ name := Oconstructor f ]}
   ; globals := ∅ |}.
Definition Ddestructor    (name : obj_name) (f : Dtor) : translation_unit :=
  {| symbols := {[ name := Odestructor f ]}
   ; globals := ∅ |}.
Definition Dunion (name : globname) (o : option Union) : translation_unit :=
  {| symbols := ∅
   ; globals := {[ name := match o with
                           | None => Gtype
                           | Some u => Gunion u
                           end ]} |}.
Definition Dstruct (name : globname) (o : option Struct) : translation_unit :=
  {| symbols := ∅
   ; globals := {[ name := match o with
                           | None => Gtype
                           | Some u => Gstruct u
                           end ]} |}.

Definition Denum (name : globname) (t : option type) (branches : list (ident * BinNums.Z)) : translation_unit :=
  {| symbols := ∅
   ; globals :=
       let enum_ty := Tnamed name in
       let raw_ty :=
           match t with
           | None => enum_ty
           | Some t => t
           end
       in
       match t with
       | Some t => {[ name := Genum t (List.map fst branches) ]}
       | None => ∅
       end ∪
       list_to_map (List.map (fun '(nm, oe) => (nm, Gconstant enum_ty (Some (Eint oe raw_ty)))) branches) |}.
  (* ^ enumerations (the initializers need to be constant expressions) *)

Definition Dconstant    (name : globname) (t : type) (e : Expr) : translation_unit :=
  {| symbols := ∅
   ; globals := {[ name := Gconstant t (Some e) ]} |}.
Definition Dconstant_undef  (name : globname) (t : type) : translation_unit :=
  {| symbols := ∅
   ; globals := {[ name := Gconstant t None ]} |}.
Definition Dtypedef     (name : globname) (t : type) : translation_unit :=
  {| symbols := ∅
   ; globals := {[ name := Gtypedef t ]} |}.
Definition Dtype (name : globname) : translation_unit :=
  {| symbols := ∅
   ; globals := {[ name := Gtype ]}|}.


Definition Is_true_canon {b} : Is_true b -> Is_true b :=
  match b as b return Is_true b -> Is_true b with
  | true => fun _ => I
  | false => fun pf => match pf with end
  end.

Require stdpp.pmap.

Definition pmap_canon {K} (s : pmap.Pmap K) : pmap.Pmap K.
destruct s.
exists pmap_car. apply Is_true_canon. assumption.
Defined.

Definition stringmap_canon {K} (s : gmap bs K) : gmap bs K.
  destruct s.
  refine (
      let t := bool_decide
           (map_Forall
              (λ (p : positive) (_ : K),
                 countable.encode <$> countable.decode p = Some p)
              (pmap_canon gmap_car)) in
match t as X return X = t -> _ with
| true => _
| false => _
end eq_refl
).
{ exists (pmap_canon gmap_car).
  red. apply Is_true_canon.
  subst t. red. rewrite <- H. exact I. }
{ exists gmap_car. apply Is_true_canon. assumption. }
Defined.

Definition compilation_union_canon (c : translation_unit) : translation_unit :=
  {| symbols := stringmap_canon c.(symbols)
   ; globals := stringmap_canon c.(globals) |}.

Fixpoint decls' (ls : list translation_unit) : translation_unit :=
  match ls with
  | nil => {| symbols := ∅ ; globals := ∅ |}
  | m :: ms =>
    let res := decls' ms in
    {| symbols := m.(symbols) ∪ res.(symbols)
     ; globals := m.(globals) ∪ res.(globals) |}
  end.

Definition decls ls : translation_unit :=
  compilation_union_canon (decls' ls).

Declare Reduction reduce_translation_unit :=
  cbv beta iota zeta delta
      [ decls decls' compilation_union_canon pmap_canon pmap.Pmap_wf andb
        parser.empty_globals parser.empty_symbols
        Dvar Dfunction Dmethod Dconstructor Ddestructor
        Dunion Dstruct Denum Dconstant Dconstant_undef Dtypedef Dtype
        stringmap_canon symbols globals
        union map_union union_with map_union_with merge gmap.gmap_merge
        pmap.Pmerge pmap.Pmerge_raw pmap.Pomap_raw
        singletonM map_singleton
        insert map_insert
        partial_alter gmap.gmap_partial_alter pmap.Ppartial_alter pmap.Ppartial_alter_raw
        countable.encode
        option_union_with byte_countable
        Bytestring.print Bytestring.parse Bytestring.t_dec bytestring_countable bytestring.append
        Papp
        empty pmap.Psingleton_raw flip mbind compose option_bind
        pmap.PNode'
        List.map fst snd
        list_to_map
        names.globname_eq
        names.localname_eq
        names.ident_eq
        names.obj_name_eq
        string_rec string_rect decide_rel
        negb
        foldr Ascii.shift

        symbol_table_empty_trans type_table_empty_trans parser.empty_symbols parser.empty_globals

        list_countable
        option_ret option_bind mret mbind mapM list_rect list_fmap list_eq_dec
        positives_flatten N_countable positives_unflatten positives_flatten_go Byte.to_N Byte.of_N

positives_unflatten_go Pdup Pos.succ
Pos.pred_N Pos.pred_double

        Is_true_canon bool_decide map_Forall_dec map_to_list decide curry pmap.Pto_list list.Forall_dec list.Forall_Exists_dec countable.decode shift pmap.Pto_list_raw from_option List.app curry_dec Preverse decide_rel option_eq_dec fmap option_fmap option_map numbers.positive_eq_dec Pos.eq_dec positive_rec positive_rect Preverse_go sumbool_rect sumbool_rec ].

Export Bytestring.
