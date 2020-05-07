(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Bool.Bool.
Require Import stdpp.gmap.
(* Require Import ExtLib.Structures.Monad. *)
(* Require Import ExtLib.Data.Monads.OptionMonad. *)
Require Import bedrock.bytestring.
Require Import bedrock.Util.
From bedrock.lang.cpp.syntax Require Import names expr stmt types.


Set Primitive Projections.

Record LayoutInfo : Set :=
{ li_offset : Z }.
Instance: EqDecision LayoutInfo.
Proof. solve_decision. Defined.

Record Ctor : Set :=
{ c_class  : globname
; c_params : list (ident * type)
; c_body   : option (OrDefault (list Initializer * Stmt))
}.
Instance: EqDecision Ctor.
Proof. solve_decision. Defined.

Record Dtor : Set :=
{ d_class  : globname
; d_body   : option (OrDefault (Stmt * list (FieldOrBase * obj_name)))
; d_virtual : bool
}.
Instance: EqDecision Dtor.
Proof. solve_decision. Defined.

Record Func : Set :=
{ f_return : type
; f_params : list (ident * type)
; f_body   : option Stmt
}.
Instance: EqDecision Func.
Proof. solve_decision. Defined.

Record Method : Set :=
{ m_return  : type
; m_class   : globname
; m_this_qual : type_qualifiers
; m_params  : list (ident * type)
; m_body    : option Stmt
; m_virtual : bool
}.
Instance: EqDecision Method.
Proof. solve_decision. Defined.

Record Union : Set :=
{ u_fields : list (ident * type * LayoutInfo)
  (* ^ fields with layout information *)
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
; s_fields : list (ident * type * LayoutInfo)
  (* ^ fields with layout information *)
; s_layout : LayoutType
  (* ^ the type of layout semantics *)
; s_size : N
  (* ^ size of the structure (including padding) *)
}.
Instance: EqDecision Struct.
Proof. solve_decision. Defined.

Variant Ctor_type : Set := Ct_Complete | Ct_Base | Ct_Comdat.
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
(*   end%string. *)

Variant Dtor_type : Set := Dt_Deleting | Dt_Complete | Dt_Base | Dt_Comdat.
Instance: EqDecision Dtor_type.
Proof. solve_decision. Defined.

Definition dtor_name (type : Dtor_type) (cls : globname) : obj_name :=
  match cls with
  | Bytestring.String _ (Bytestring.String _ s) =>
    ("_ZN" ++ s ++ "D" ++ ("0" (*match type with
                          | Dt_Deleting => "0"
                          | Dt_Complete => "1"
                          | Dt_Base => "2"
                          | Dt_Comdat => "5"
                          end *)) ++ "Ev")
  | _ => ""
  end%bs.

(* these can be externed *)
Variant ObjValue : Set :=
| Ovar         (_ : type) (_ : option Expr)
| Ofunction    (_ : Func)
| Omethod      (_ : Method)
| Oconstructor (_ : Ctor)
| Odestructor  (_ : Dtor).
Instance: EqDecision ObjValue.
Proof. solve_decision. Defined.

Variant GlobDecl : Set :=
| Gtype     (* this is a type declaration, but not a definition *)
| Gunion    (_ : Union)
| Gstruct   (_ : Struct)
| Genum     (_ : type) (_ : list ident)
| Gconstant (_ : type) (_ : option Expr)
| Gtypedef  (_ : type).
Instance: EqDecision GlobDecl.
Proof. solve_decision. Defined.

Definition symbol_table :=
  gmap obj_name ObjValue.

Definition type_table :=
  gmap globname GlobDecl.

Record translation_unit : Type :=
{ symbols : symbol_table
; globals : type_table
}.

Instance global_lookup : Lookup globname GlobDecl translation_unit :=
  fun k m => m.(globals) !! k.
Instance symbol_lookup : Lookup obj_name ObjValue translation_unit :=
  fun k m => m.(symbols) !! k.

(*
Instance Empty_symbol_table : Empty symbol_table := ∅.
  ltac:(let x := eval vm_compute in (∅ : symbol_table) in exact x).
Instance Empty_type_table : Empty type_table :=
  ltac:(let x := eval vm_compute in (∅ : type_table) in exact x).
*)
