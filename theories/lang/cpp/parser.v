(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bedrock.prelude.base.	(* for, e.g., <<::>> *)
Require Export bedrock.prelude.bytestring.	(* for <<%bs>> *)
Require Import bedrock.prelude.avl.
Require Export bedrock.lang.cpp.syntax. (* NOTE: too much *)
Require Export bedrock.lang.cpp.parser.stmt.
Require Import bedrock.lang.cpp.parser.lang.
Require Import bedrock.lang.cpp.parser.type.
Require Import bedrock.lang.cpp.parser.name.
Require Import bedrock.lang.cpp.parser.expr.
Require Import bedrock.lang.cpp.parser.decl.
Require Import bedrock.lang.cpp.parser.notation.
Require Import bedrock.lang.cpp.parser.reduction.

#[local] Definition parser_lang : lang.t := lang.cpp.
Include ParserName.
Include ParserType.
Include ParserExpr.
Include ParserDecl.

Module Import translation_unit.

  (**
  We work with an exploded [translation_unit] and raw trees for
  efficiency.
  *)

  Definition raw_symbol_table : Type := NM.Raw.t ObjValue.
  Definition raw_type_table : Type := NM.Raw.t GlobDecl.
  Definition raw_alias_table : Type := NM.Raw.t type.

  #[global] Instance raw_structured_insert : forall {T}, Insert globname T (NM.Raw.t T) := _.

  Definition t : Type :=
    raw_symbol_table -> raw_type_table -> raw_alias_table -> list name ->
    (raw_symbol_table -> raw_type_table -> raw_alias_table -> list name -> translation_unit * list name) ->
    translation_unit * list name.

  Definition _symbols (n : name) (v : ObjValue) : t :=
    fun s t a dups k =>
      match s !! n with
      | None => k (<[n := v]> s) t a dups
      | _ => k s t a (n :: dups)
      end.
  Definition _types (n : name) (v : GlobDecl) : t :=
    fun s t a dups k =>
      match t !! n with
      | None => k s (<[n := v]> t) a dups
      | _ => k s t a (n :: dups)
      end.
  Definition _aliases (n : name) (v : type) : t :=
    fun s t a dups k =>
      match a !! n with
      | None => k s t (<[n:=v]> a) dups
      | _ => k s t a (n :: dups)
      end.
  Definition _skip : t :=
    fun s t a dups k => k s t a dups.

  Fixpoint decls' (ds : list t) : t :=
    match ds with
    | nil => fun s t a dups k => k s t a dups
    | d :: ds => fun s t a dups k => d s t a dups (fun s t a dups' => decls' ds s t a dups' k)
    end.

  Definition decls (ds : list t) (e : endian) : translation_unit * list name :=
    decls' ds ∅ ∅ ∅ [] $ fun s t a => pair {|
      symbols := NM.from_raw s;
      types := NM.from_raw t;
      aliases := NM.from_raw a;
      initializer := nil;	(** TODO *)
      byte_order := e;
    |}.

  Definition the_tu (result : translation_unit * list name)
    : match result.2 with
      | [] => translation_unit
      | _ => unit
      end :=
    match result.2 as X return match X with [] => translation_unit | _ => unit end with
    | [] => result.1
    | _ => tt
    end.

End translation_unit.
Export translation_unit(decls).
#[local] Notation K := translation_unit.t (only parsing).

Definition Dvariable (n : obj_name) (t : type) (init : global_init.t lang.cpp) : K :=
  _symbols n $ Ovar t init.

Definition Dfunction (n : obj_name) (f : Func) : K :=
  _symbols n $ Ofunction f.

Definition Dmethod (n : obj_name) (static : bool) (f : Method) : K :=
  _symbols n $ if static then Ofunction $ static_method f else Omethod f.

Definition Dconstructor (n : obj_name) (f : Ctor) : K :=
  _symbols n $ Oconstructor f.

Definition Ddestructor (n : obj_name) (f : Dtor) : K :=
  _symbols n $ Odestructor f.

Definition Dtype (n : globname) : K :=
  _types n $ Gtype.

Definition Dstruct (n : globname) (f : option Struct) : K :=
  _types n $ if f is Some f then Gstruct f else Gtype.

Definition Dunion (n : globname) (f : option Union) : K :=
  _types n $ if f is Some f then Gunion f else Gtype.

Definition Denum (n : globname) (u : type) (cs : list ident) : K :=
  _types n $ Genum u cs.

Definition Denum_constant (n : globname)
    (gn : globname) (ut : exprtype) (v : N + Z) (init : option Expr) : K :=
  _types n $
  let v := match v with inl n => Echar n ut | inr z => Eint z ut end in
  let t := Tenum gn in
  Gconstant t $ Some $ Ecast (Cintegral t) v.

Definition Dtypedef (n : globname) (t : type) : K :=
  _aliases n t.

Definition Dstatic_assert (msg : option bs) (e : Expr) : K :=
  _skip.

Definition Qconst_volatile : type -> type := tqualified QCV.
Definition Qconst : type -> type := tqualified QC.
Definition Qvolatile : type -> type := tqualified QV.
