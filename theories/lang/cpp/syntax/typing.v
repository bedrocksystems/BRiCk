(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.cpp.syntax Require Import names expr types.

(** [type_of e] returns the type of the expression [e]. *)
Fixpoint type_of (e : Expr) : type :=
  match e with
  | Econst_ref _ t
  | Evar _ t
  | Echar _ t
  | Estring _ t
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
  | Esubscript _ _ _ t
  | Esize_of _ t
  | Ealign_of _ t
  | Eoffset_of _ t
  | Econstructor _ _ t => t
  | Eimplicit e => type_of e
  | Eif _ _ _ _ t
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

(** [erase_qualifiers t] erases *all* qualifiers that occur everywhere in the type.

    NOTE we currently use this because we do not track [const]ness in the logic, this
    is somewhat reasonable because we often opt to express this in separation logic.
    And the type system also enforces some of the other criteria.
 *)
Fixpoint erase_qualifiers (t : type) : type :=
  match t with
  | Tpointer t => Tpointer (erase_qualifiers t)
  | Tref t => Tref (erase_qualifiers t)
  | Trv_ref t => Trv_ref (erase_qualifiers t)
  | Tnum _ _
  | Tbool
  | Tvoid
  | Tfloat _
  | Tnamed _
  | Tenum _ => t
  | Tarray t sz => Tarray (erase_qualifiers t) sz
  | @Tfunction cc ar t ts => Tfunction (cc:=cc) (ar:=ar) (erase_qualifiers t) (List.map erase_qualifiers ts)
  | Tmember_pointer cls t => Tmember_pointer cls (erase_qualifiers t)
  | Tqualified _ t => erase_qualifiers t
  | Tnullptr => Tnullptr
  | Tarch sz nm => Tarch sz nm
  end.

(** [drop_qualifiers t] drops all the *leading* quallifiers of the type [t].
    e.g. [drop_qualifiers (Qconst (Qmut t)) = t]
 *)
Fixpoint drop_qualifiers (t : type) : type :=
  match t with
  | Tqualified _ t => drop_qualifiers t
  | _ => t
  end.

Lemma drop_qualifiers_Tptr : forall [ty ty'],
    drop_qualifiers ty = Tptr ty' -> erase_qualifiers ty = Tptr (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tref : forall [ty ty'],
    drop_qualifiers ty = Tref ty' -> erase_qualifiers ty = Tref (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Trv_ref : forall [ty ty'],
    drop_qualifiers ty = Trv_ref ty' -> erase_qualifiers ty = Trv_ref (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tmember_pointer : forall [ty cls ty'],
    drop_qualifiers ty = Tmember_pointer cls ty' ->
    erase_qualifiers ty = Tmember_pointer cls (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tint : forall [ty sz sgn],
    drop_qualifiers ty = Tnum sz sgn -> erase_qualifiers ty = Tnum sz sgn.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tfloat : forall [ty sz],
    drop_qualifiers ty = Tfloat sz -> erase_qualifiers ty = Tfloat sz.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tbool : forall [ty],
    drop_qualifiers ty = Tbool -> erase_qualifiers ty = Tbool.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tvoid : forall [ty],
    drop_qualifiers ty = Tvoid -> erase_qualifiers ty = Tvoid.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tnullptr : forall [ty],
    drop_qualifiers ty = Tnullptr -> erase_qualifiers ty = Tnullptr.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tenum : forall [ty nm],
    drop_qualifiers ty = Tenum nm -> erase_qualifiers ty = Tenum nm.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.


Lemma drop_erase : forall t, drop_qualifiers (erase_qualifiers t) = erase_qualifiers t.
Proof. induction t; simpl; eauto. Qed.

Lemma erase_drop : forall t, erase_qualifiers (drop_qualifiers t) = erase_qualifiers t.
Proof. induction t; simpl; eauto. Qed.

(** simplify instances where you have [drop_qualifiers ty = Txxx ..] for some [Txxx] *)
Ltac simpl_drop_qualifiers :=
  match goal with
  | H : drop_qualifiers _ = _ |- _ =>
    first [ rewrite (drop_qualifiers_Tbool H)
          | rewrite (drop_qualifiers_Tfloat H)
          | rewrite (drop_qualifiers_Tint H)
          | rewrite (drop_qualifiers_Tmember_pointer H)
          | rewrite (drop_qualifiers_Tnullptr H)
          | rewrite (drop_qualifiers_Tvoid H)
          | rewrite (drop_qualifiers_Tptr H)
          | rewrite (drop_qualifiers_Tenum H) ]
  end.


(** [unptr t] returns the type of the object that a value of type [t] points to
    or [None] if [t] is not a pointer type.
 *)
Definition unptr (t : type) : option type :=
  match drop_qualifiers t with
  | Tptr p => Some p
  | _ => None
  end.

(** [drop_reference t] drops leading reference and qualifiers to get the underlying
    type.
 *)
Fixpoint drop_reference (t : type) : type :=
  match t with
  | Tref t => drop_reference t
  | Trv_ref t => drop_reference t
  | Tqualified q t => drop_reference t
  | _ => t
  end.

(** [class_name t] returns the name of the class that this type refers to
 *)
Definition class_name (t : type) : option globname :=
  match drop_qualifiers t with
  | Tnamed gn => Some gn
  | _ => None
  end.

(** [is_value_type t] returns [true] if [t] has value semantics.
    A value type is one that can be represented by [val].
 *)
Definition is_value_type (t : type) : bool :=
  match drop_qualifiers t with
  | Tnum _ _
  | Tbool
  | Tptr _
  | Tnullptr
  | Tfloat _
  | Tmember_pointer _ _
  | Tenum _ (* enum types are value types *)
  | Tvoid => true
  | _ => false
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
Definition valcat_from_type (t : type) : ValCat :=
  (*
  Dropping qualifiers may not be necessary. Cppreference says
  "Reference types cannot be cv-qualified at the top level".
  *)
  match drop_qualifiers t with
  | Tref _
  | Trv_ref (@Tfunction _ _ _ _) => Lvalue
  | Trv_ref _ => Xvalue
  | _ => Prvalue
  end.

Definition valcat_from_function_type (t : type) : ValCat :=
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
  | Esubscript _ _ vc _ => vc
  | Esize_of _ _ => Prvalue
  | Ealign_of _ _ => Prvalue
  | Eoffset_of _ _ => Prvalue
  | Econstructor _ _ _ => Prvalue (* init *)
  | Eimplicit e => valcat_of e
  | Eif _ e1 e2 vc _ => vc
  | Ethis _ => Prvalue
  | Enull => Prvalue
  | Einitlist _ _ t => Prvalue (* operand | init *)
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

Definition vctype_of (e : Expr) : type :=
  match valcat_of e with
  | Prvalue => id
  | Lvalue => Tref
  | Xvalue => Trv_ref
  end (type_of e).
