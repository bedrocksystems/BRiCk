(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import base list_numbers.
From bedrock.lang.cpp.syntax Require Import names expr types.

(** [type_of e] returns the type of the expression [e]. *)
Fixpoint type_of (e : Expr) : exprtype :=
  match e with
  | Econst_ref _ t
  | Evar _ t
  | Echar _ t => t
  | Estring vs t => Tarray (Qconst t) (1 + lengthN vs)
  | Eint _ t => t
  | Ebool _ => Tbool
  | Eunop _ _ t
  | Ebinop _ _ _ t => t
  | Eread_ref e => type_of e
  | Ederef _ t => t
  | Eaddrof e => Tptr (type_of e)
  | Eassign _ _ t
  | Eassign_op _ _ _ t
  | Epreinc _ t
  | Epostinc _ t
  | Epredec _ t
  | Epostdec _ t => t
  | Eseqand _ _ => Tbool
  | Eseqor _ _ => Tbool
  | Ecomma _ e2 => type_of e2
  | Ecall _ _ t
  | Ecast _ _ _ t
  | Emember _ _ t
  | Emember_call _ _ _ t
  | Eoperator_call _ _ _ t
  | Esubscript _ _ t
  | Esize_of _ t
  | Ealign_of _ t
  | Eoffset_of _ t
  | Econstructor _ _ t => t
  | Eimplicit e => type_of e
  | Eif _ _ _ _ t
  | Eif2 _ _ _ _ _ _ t
  | Ethis t => t
  | Enull => Tnullptr
  | Einitlist _ _ t
  | Eimplicit_init t => t
  | Enew _ _ aty _ _ => Tptr aty
  | Edelete _ _ _ _ => Tvoid
  | Eandclean e => type_of e
  | Ematerialize_temp e _ => type_of e
  | Eatomic _ _ t => t
  | Eva_arg _ t => t
  | Epseudo_destructor _ _ => Tvoid
  | Earrayloop_init _ _ _ _ _ t => t
  | Earrayloop_index _ t => t
  | Eopaque_ref _ _ t => t
  | Eunsupported _ _ t => t
  end.

(**
Setting aside uninstantiated template arguments, there's a total
function from expressions to value categories.
*)
Definition UNEXPECTED_valcat {A} (tm : A) : ValCat.
Proof. exact Prvalue. Qed.

(**
The value category of an explicit cast to type [t] or a call to a
function returning type [t] or a [__builtin_va_arg] of type [t].
*)
Definition valcat_from_type (t : decltype) : ValCat :=
  (*
  Dropping qualifiers may not be necessary. Cppreference says
  "Reference types cannot be cv-qualified at the top level".
  *)
  match drop_qualifiers t with
  | Tref _ => Lvalue
  | Trv_ref u =>
    match drop_qualifiers u with
    | @Tfunction _ _ _ _ => Lvalue
    | _ => Xvalue
    end
  | _ => Prvalue
  end.

(* See <https://eel.is/c++draft/expr.call#13> *)
Definition valcat_from_function_type (t : functype) : ValCat :=
  match t with
  | @Tfunction _ _ ret _ => valcat_from_type ret
  | _ => UNEXPECTED_valcat t
  end.

Fixpoint valcat_of (e : Expr) : ValCat :=
  match e with
  | Econst_ref _ _ => Prvalue
  | Evar _ _ => Lvalue
  | Echar _ _ => Prvalue
  | Estring _ _ => Lvalue
  | Eint _ _ => Prvalue
  | Ebool _ => Prvalue
  | Eunop _ _ _ => Prvalue
  | Ebinop op e1 _ _ =>
    match op with
    | Bdotp =>
      (**
      The value category of [e1.*e2] is (i) that of [e1] (xvalue or
      lvalue) when [e2] points to a field and (ii) prvalue when [e2]
      points to a method.

      We need only address (i) here because when [e2] is a method, the
      result of [e1.*e2] must be immediately applied, and cpp2v emits
      [Emember_call] rather than [Ebinop] for indirect method calls.

      https://www.eel.is/c++draft/expr.mptr.oper#6
      *)
      match e1 with
      | Eread_ref _ => Lvalue
      | Ematerialize_temp _ _ => Xvalue
      | _ => UNEXPECTED_valcat e
      end
    | Bdotip => Lvalue	(* derived from [Bdotp] *)
    | _ => Prvalue
    end
  | Eread_ref e =>
    (*
    cpp2v ensures [e] is either a variable [Evar] or a field [Emember]
    with reference type. According to cppreference, "the name of a
    variable, [...], or a data member, regardless of type" is an
    lvalue.
    *)
    Lvalue
  | Ederef _ _ => Lvalue
  | Eaddrof _ => Prvalue
  | Eassign _ _ _ => Lvalue
  | Eassign_op _ _ _ _ => Lvalue
  | Epreinc _ _ => Lvalue
  | Epostinc _ _ => Prvalue
  | Epredec _ _ => Lvalue
  | Epostdec _ _ => Prvalue
  | Eseqand _ _ => Prvalue
  | Eseqor _ _ => Prvalue
  | Ecomma _ e2 => valcat_of e2
  | Ecast _ _ vc _ => vc
  | Ecall f _ _ =>
    match f with
    | Ecast Cfun2ptr _ _ (Tptr t) => valcat_from_function_type t
    | _ => UNEXPECTED_valcat e
    end
  | Emember e _ _ => valcat_of e
  | Emember_call f _ _ _ =>
    match f with
    | inl (_, _, t)
    | inr (Ecast Cl2r _  _ (Tmember_pointer _ t)) => valcat_from_function_type t
    | _ => UNEXPECTED_valcat e
    end
  | Eoperator_call _ f _ _ =>
    match f with
    | operator_impl.Func _ t => valcat_from_function_type t
    | operator_impl.MFunc _ _ ft => valcat_from_function_type ft
    end

  | Esubscript e1 e2 _ =>
    (**
    Neither operand ever has type [Tarray _ _] due to implicitly
    inserted array-to-pointer conversions. To compute the right value
    category, we skip over such conversions.
    *)
    let valcat_of_array (ar : Expr) : ValCat :=
      match valcat_of ar with
      | Lvalue => Lvalue
      | Prvalue | Xvalue => Xvalue
      end
    in
    let valcat_of_base (ei : Expr) : ValCat :=
      match ei with
      | Ecast Carray2ptr ar _ _ => valcat_of_array ar
      | _ => Lvalue
      end
    in
    match drop_qualifiers (type_of e1) with
    | Tptr _ => valcat_of_base e1
    | _ => valcat_of_base e2
    end
  | Esize_of _ _ => Prvalue
  | Ealign_of _ _ => Prvalue
  | Eoffset_of _ _ => Prvalue
  | Econstructor _ _ _ => Prvalue (* init *)
  | Eimplicit e => valcat_of e
  | Eif _ e1 e2 vc _ => vc
  | Eif2 _ _ _ _ _ vc _ => vc
  | Ethis _ => Prvalue
  | Enull => Prvalue
  | Einitlist _ _ _ => Prvalue (* operand | init *)
  | Eimplicit_init _ =>
    (**
    "References cannot be value-initialized".

    https://en.cppreference.com/w/cpp/language/value_initialization
    *)
    Prvalue
  | Enew _ _ _ _ _ => Prvalue
  | Edelete _ _ _ _ => Prvalue
  | Eandclean e => valcat_of e
  | Ematerialize_temp _ vc => vc
  | Eatomic _ _ _ => Prvalue
  | Eva_arg _ t => valcat_from_type t
  | Epseudo_destructor _ _ => Prvalue
  | Earrayloop_init _ _ _ _ _ _ => Prvalue (* init *)
  | Earrayloop_index _ _ => Prvalue
  | Eopaque_ref _ vc _ => vc
  | Eunsupported _ vc _ => vc
  end.
#[global] Arguments valcat_of !_ / : simpl nomatch, assert.

#[projections(primitive)]
Record vctype : Set := VCType { vctype_type : exprtype; vctype_valcat : ValCat }.
Add Printing Constructor vctype.

#[global] Instance vctype_eq_dec : EqDecision vctype.
Proof. solve_decision. Defined.

#[global] Instance vctype_countable : Countable vctype.
Proof.
  apply (inj_countable'
    (fun r => (r.(vctype_type), r.(vctype_valcat)))
    (fun p => VCType p.1 p.2)
  ).
  abstract (by intros []).
Defined.

Definition vctype_of (e : Expr) : vctype :=
  VCType (type_of e) (valcat_of e).

Lemma vctype_of_type e : vctype_type (vctype_of e) = type_of e.
Proof. done. Qed.
Lemma vctype_of_valcat e : vctype_valcat (vctype_of e) = valcat_of e.
Proof. done. Qed.
Lemma vctype_of_inv e vt :
  vctype_of e = vt ->
  type_of e = vt.(vctype_type) /\ valcat_of e = vt.(vctype_valcat).
Proof. by intros <-. Qed.
