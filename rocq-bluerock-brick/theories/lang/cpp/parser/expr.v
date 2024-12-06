(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.syntax.types(drop_qualifiers).
Require Import bedrock.lang.cpp.parser.prelude.
Require Import bedrock.lang.cpp.parser.lang.

#[local] Arguments force_some _ {_} : assert.	(** TODO: Upstream? *)

(** * Derived expressions emitted by cpp2v *)

Module ParserExpr (Import Lang : PARSER_LANG).
  #[local] Notation name := (name' parser_lang).
  #[local] Notation obj_name := (obj_name' parser_lang).
  #[local] Notation type := (type' parser_lang).
  #[local] Notation exprtype := (exprtype' parser_lang).
  #[local] Notation decltype := (decltype' parser_lang).
  #[local] Notation Expr := (Expr' parser_lang).
  #[local] Notation Cast := (Cast' parser_lang).

  Definition Ecstyle_cast (c : Cast) (t : type) (e : Expr) : Expr :=
    Eexplicit_cast cast_style.c t (Ecast c e).
  Definition Efunctional_cast (c : Cast) (t : type) (e : Expr) : Expr :=
    Eexplicit_cast cast_style.functional t (Ecast c e).

  Definition fuse_dependent_cast (s : cast_style.t) (c : Cast) (t : type) (e : Expr) : Expr :=
    Eexplicit_cast s t (Ecast c e).
(*
    match c with
    | Cdependent t' =>
        if bool_decide (t = t') then
          Eexplicit_cast s t e
        else
          Eexplicit_cast s t (Ecast c e)
    (* TODO: use [Eunsupported] *)
    | _ =>
        Eexplicit_cast s t (Ecast c e)
    end.
*)

  (* Keeping [Eexplicit_cast] as an annotation (with a no-op semantics) makes it easy
     to give it semantics.
     Alternatively, we could fuse these symbols, but then we would need to give
     separate rules for each type of cast at each WP.
   *)
  Definition Edynamic_cast (c : Cast) (t : type) (e : Expr) : Expr :=
    Eexplicit_cast cast_style.dynamic t (Ecast c e).

    (*
    match c with
    | Cdynamic t' =>
        if bool_decide (t = t') then
          Eexplicit_cast cast_style.dynamic t e
        else
          Eexplicit_cast cast_style.dynamic t (Ecast c e)
    | _ =>
        fuse_dependent_cast cast_style.dynamic c t e
    end. *)
  Definition Estatic_cast := fuse_dependent_cast cast_style.static.
  Definition Econst_cast := fuse_dependent_cast cast_style.const.
  Definition Ereinterpret_cast := fuse_dependent_cast cast_style.reinterpret.
  Definition Ebuiltin_bit_cast := fuse_dependent_cast cast_style.functional.

  (* These are syntactic markers to avoid parse errors when features are not
     supported.

     See <https://gcc.gnu.org/onlinedocs/gcc/Alternate-Keywords.html>
   *)
  Definition Eextension (e : Expr) : Expr := e.

  Definition Egnu_null (t : type) : Expr :=
    Ecast (Cptr2int t) Enull.

  Definition Ealignof_preferred (e : Expr) (t : type) :=
    Eunsupported "alignof_preferred" t.

  Definition Eoperator_member_call (oo : OverloadableOperator) (nm : obj_name) (ct : dispatch_type) (ft : type) (obj : Expr) (es : list Expr) : Expr :=
    Eoperator_call oo (operator_impl.MFunc nm ct ft) (obj :: es).

  Definition Eoperator_call (oo : OverloadableOperator) (f : obj_name) (ft : type) (es : list Expr) : Expr :=
    Eoperator_call oo (operator_impl.Func f ft) es.

  Definition Eenum_const_at (gn : name) (c : ident) (ty : exprtype) : Expr :=
    Ecast (Cintegral ty) (Eenum_const gn c).

  Definition Ebuiltin (nm : obj_name) (ty : type) : Expr :=
    Ecast (Cbuiltin2fun $ Tptr ty) (Eglobal nm ty).

  (* [Esource_loc name e] represents a call to the source location builtin <<name>>.
     The result of this function call is the value returned by the expression <<e>>.
   *)
  Definition Esource_loc (name : bs) (e : Expr) : Expr := e.

  Variant member_type : Set :=
    | Field (_ : atomic_name_ type) (_ : bool) (_ : type)
    | Enum (_ : name)
    | Static (_ : name) (_ : type).

  Definition Emember (arrow : bool) (e_orig : Expr) (f : member_type) : force_some Expr :=
    option.get_some $
      match f with
      | Field f mut ty => Some $ Emember arrow e_orig f mut ty
      | Enum (Nscoped en (Nid arg)) =>
          Some $ Emember_ignore arrow e_orig (Eenum_const en arg)
      | Static on ty =>
          Some $ Emember_ignore arrow e_orig (Eglobal on ty)
      | _ => None
      end.

  Definition Edefault_init_expr (e : Expr) : Expr := e.

  Definition Eunevaluated_var (var : bs) (t : type): Expr :=
    Eunsupported ("Unevaluated variable: " ++ var) (Tref t).

  Definition Ecapture (qual : type_qualifiers) (fld : field_name.t parser_lang) (lambda : name) (capture_field_type : type) : Expr :=
    Emember true (Ethis (Tptr $ tqualified qual (Tnamed lambda))) (Field fld false capture_field_type).

  Notation Ecapture_var qual lambda_class name capture_field_type :=
    (Ecapture qual (field_name.CaptureVar name) lambda_class capture_field_type) (only parsing).

  (* NOTE: [Ecapture] always produces a GLvalue and <<this>> is a PR value.
     The field will store a pointer, so we must read the pointer with [Ecast Cl2r] *)
  Notation Ecapture_this qual lambda_class capture_field_type :=
    (Ecast Cl2r (Ecapture qual field_name.CaptureThis lambda_class capture_field_type)) (only parsing).

End ParserExpr.
