(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Export
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Lists.List
        Coq.ZArith.BinInt.

Require Import stdpp.gmap.
Require Import stdpp.stringmap.
Require Export bedrock.lang.cpp.ast.

Definition Nanon (ty : globname) : globname :=
  String "#"%char ty.

Definition Talias (underlying : type) (name : globname) : type :=
  underlying.

Definition NStop : list ident := nil.

Bind Scope string_scope with globname.
Bind Scope string_scope with obj_name.
Bind Scope string_scope with ident.
Bind Scope string_scope with localname.
Bind Scope Z_scope with Z.

Declare Custom Entry cppglobal.
Declare Scope cppfield_scope.
Delimit Scope cppfield_scope with field.
Bind Scope cppfield_scope with field.

Notation "` e `" := e (e custom cppglobal at level 200, at level 0) : cppfield_scope.


(** this is the compatibility layer, cpp2v generates these definitions
 *)
(* HACK to get around the fact that [gmap_empty] is opaque. *)
Local Definition empty_symbols : stringmap ObjValue :=
  Eval vm_compute in gmap_empty.
Local Definition empty_globals : stringmap GlobDecl :=
  Eval vm_compute in gmap_empty.
Local Instance gmap_empty_trans {T} : Empty (stringmap T) :=
  ltac:(let x := eval vm_compute in (∅ : stringmap T) in exact x).

Definition Dvar (name : obj_name) (t : type) (init : option Expr) : compilation_unit :=
  {| symbols := {[ name := Ovar t init ]}
   ; globals := empty_globals |}.

Definition Dfunction    (name : obj_name) (f : Func) : compilation_unit :=
  {| symbols := {[ name := Ofunction f ]}
   ; globals := empty_globals |}.
Definition Dmethod    (name : obj_name) (f : Method) : compilation_unit :=
  {| symbols := {[ name := Omethod f ]}
   ; globals := empty_globals |}.
Definition Dconstructor    (name : obj_name) (f : Ctor) : compilation_unit :=
  {| symbols := {[ name := Oconstructor f ]}
   ; globals := empty_globals |}.
Definition Ddestructor    (name : obj_name) (f : Dtor) : compilation_unit :=
  {| symbols := {[ name := Odestructor f ]}
   ; globals := empty_globals |}.
Definition Dunion (name : globname) (o : option Union) : compilation_unit :=
  {| symbols := empty_symbols
   ; globals := {[ name := match o with
                           | None => Gtype
                           | Some u => Gunion u
                           end ]} |}.
Definition Dstruct (name : globname) (o : option Struct) : compilation_unit :=
  {| symbols := empty_symbols
   ; globals := {[ name := match o with
                           | None => Gtype
                           | Some u => Gstruct u
                           end ]} |}.

Definition Denum (name : globname) (t : option type) (branches : list (ident * BinNums.Z)) : compilation_unit :=
  {| symbols := empty_symbols
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
       | None => empty_globals
       end ∪
       list_to_map (List.map (fun '(nm, oe) => (nm, Gconstant enum_ty (Some (Eint oe raw_ty)))) branches) |}.
  (* ^ enumerations (the initializers need to be constant expressions) *)

Definition Dconstant    (name : globname) (t : type) (e : Expr) : compilation_unit :=
  {| symbols := empty_symbols
   ; globals := {[ name := Gconstant t (Some e) ]} |}.
Definition Dconstant_undef  (name : globname) (t : type) : compilation_unit :=
  {| symbols := empty_symbols
   ; globals := {[ name := Gconstant t None ]} |}.
Definition Dtypedef     (name : globname) (t : type) : compilation_unit :=
  {| symbols := empty_symbols
   ; globals := {[ name := Gtypedef t ]} |}.
Definition Dtype (name : globname) : compilation_unit :=
  {| symbols := empty_symbols
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

Definition stringmap_canon {K} (s : stringmap K) : stringmap K.
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

Definition compilation_union_canon (c : compilation_unit) : compilation_unit :=
  {| symbols := stringmap_canon c.(symbols)
   ; globals := stringmap_canon c.(globals) |}.

Fixpoint decls' (ls : list compilation_unit) : compilation_unit :=
  match ls with
  | nil => {| symbols := empty_symbols ; globals := empty_globals |}
  | m :: ms =>
    let res := decls' ms in
    {| symbols := m.(symbols) ∪ res.(symbols)
     ; globals := m.(globals) ∪ res.(globals) |}
  end.

Definition decls ls : compilation_unit :=
  compilation_union_canon (decls' ls).

Declare Reduction reduce_compilation_unit :=
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
        option_union_with string_countable
        string_to_pos digits_to_pos ascii_to_digits Papp
        gmap_empty_trans empty pmap.Psingleton_raw flip mbind compose option_bind
        pmap.PNode'
        List.map fst snd
        list_to_map
        names.globname_eq
        names.localname_eq
        names.ident_eq
        names.obj_name_eq
        string_rec string_rect string_eq_dec decide_rel ascii_rec ascii_rect
        ascii_eq_dec ascii_dec negb
        foldr Ascii.shift

        Is_true_canon bool_decide map_Forall_dec map_to_list decide curry pmap.Pto_list list.Forall_dec list.Forall_Exists_dec countable.decode zero string_of_pos string_of_digits shift digits_of_pos ascii_of_digits pmap.Pto_list_raw from_option List.app curry_dec Preverse decide_rel option_eq_dec fmap option_fmap option_map numbers.positive_eq_dec Pos.eq_dec positive_rec positive_rect Preverse_go sumbool_rect sumbool_rec ].
