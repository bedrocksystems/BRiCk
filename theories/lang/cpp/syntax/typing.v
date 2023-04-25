(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import base list_numbers.
From bedrock.lang.cpp.syntax Require Import names expr types.

(** [type_of e] returns the type of the expression [e]. *)
Fixpoint type_of (e : Expr) : type :=
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
  | Tchar_ _
  | Tbool
  | Tvoid
  | Tfloat_ _
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

Lemma decompose_type_drop ty :
  (decompose_type ty).2 = drop_qualifiers ty.
Proof. induction ty => //=. rewrite -IHty /= decompose_type_qual/=. by case: decompose_type. Qed.

Lemma unqual_drop_qualifiers ty tq ty' : drop_qualifiers ty <> Tqualified tq ty'.
Proof. by induction ty. Qed.
Lemma unqual_erase_qualifiers ty tq ty' : erase_qualifiers ty <> Tqualified tq ty'.
Proof. by induction ty. Qed.

Lemma erase_drop_idemp ty :
  erase_qualifiers ty = ty -> drop_qualifiers ty = ty.
Proof. by destruct ty => // /unqual_erase_qualifiers. Qed.

(* Lemmas for all [type] constructors; in constructor order for easy review. *)
Lemma drop_qualifiers_Tptr : forall [ty ty'],
    drop_qualifiers ty = Tptr ty' -> erase_qualifiers ty = Tptr (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tref : forall [ty ty'],
    drop_qualifiers ty = Tref ty' -> erase_qualifiers ty = Tref (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Trv_ref : forall [ty ty'],
    drop_qualifiers ty = Trv_ref ty' -> erase_qualifiers ty = Trv_ref (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tnum : forall [ty sz sgn],
    drop_qualifiers ty = Tnum sz sgn -> erase_qualifiers ty = Tnum sz sgn.
Proof. by induction ty. Qed.
Lemma drop_qualifiers_Tchar_ : forall [ty ct],
    drop_qualifiers ty = Tchar_ ct -> erase_qualifiers ty = Tchar_ ct.
Proof. by induction ty. Qed.
Lemma drop_qualifiers_Tvoid : forall [ty],
    drop_qualifiers ty = Tvoid -> erase_qualifiers ty = Tvoid.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tarray : forall [ty ty' n],
    drop_qualifiers ty = Tarray ty' n -> erase_qualifiers ty = Tarray (erase_qualifiers ty') n.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tnamed : forall [ty n],
    drop_qualifiers ty = Tnamed n -> erase_qualifiers ty = Tnamed n.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tenum : forall [ty nm],
    drop_qualifiers ty = Tenum nm -> erase_qualifiers ty = Tenum nm.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tfunction : forall [ty c ar ty' tArgs],
    drop_qualifiers ty = @Tfunction c ar ty' tArgs ->
    erase_qualifiers ty = @Tfunction c ar (erase_qualifiers ty') (map erase_qualifiers tArgs).
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tbool : forall [ty],
    drop_qualifiers ty = Tbool -> erase_qualifiers ty = Tbool.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tmember_pointer : forall [ty cls ty'],
    drop_qualifiers ty = Tmember_pointer cls ty' ->
    erase_qualifiers ty = Tmember_pointer cls (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tfloat : forall [ty sz],
    drop_qualifiers ty = Tfloat_ sz -> erase_qualifiers ty = Tfloat_ sz.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
(* Omit Tqualified on purpose *)
Lemma drop_qualifiers_Tnullptr : forall [ty],
    drop_qualifiers ty = Tnullptr -> erase_qualifiers ty = Tnullptr.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.


Lemma drop_erase : forall t, drop_qualifiers (erase_qualifiers t) = erase_qualifiers t.
Proof. induction t; simpl; eauto. Qed.

Lemma erase_drop : forall t, erase_qualifiers (drop_qualifiers t) = erase_qualifiers t.
Proof. induction t; simpl; eauto. Qed.

(** simplify instances where you have [drop_qualifiers ty = Txxx ..] for some [Txxx]. *)
(* Same order as above, for easier review. *)
Ltac simpl_drop_qualifiers :=
  match goal with
  | H : drop_qualifiers _ = _ |- _ => first
          [ rewrite (drop_qualifiers_Tptr H)
          | rewrite (drop_qualifiers_Tref H)
          | rewrite (drop_qualifiers_Trv_ref H)
          | rewrite (drop_qualifiers_Tnum H)
          | rewrite (drop_qualifiers_Tchar_ H)
          | rewrite (drop_qualifiers_Tvoid H)
          | rewrite (drop_qualifiers_Tarray H)
          | rewrite (drop_qualifiers_Tnamed H)
          | rewrite (drop_qualifiers_Tenum H)
          | rewrite (drop_qualifiers_Tfunction H)
          | rewrite (drop_qualifiers_Tbool H)
          | rewrite (drop_qualifiers_Tmember_pointer H)
          | rewrite (drop_qualifiers_Tfloat H)
          | rewrite (drop_qualifiers_Tnullptr H)
          ]
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

(** [is_arithmetic ty] states whether [ty] is an arithmetic type *)
Definition is_arithmetic (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tnum _ _
  | Tchar_ _
  | Tenum _
  | Tbool => true
  | _ => false
  end.

(** [is_pointer ty] is [true] if [ty] is a pointer type *)
Definition is_pointer (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tptr _ => true
  | _ => false
  end.

Lemma is_pointer_not_arithmetic : forall ty, is_pointer ty = true -> is_arithmetic ty = false.
Proof. induction ty; simpl; intros; eauto. Qed.
Lemma is_arithmetic_not_pointer : forall ty, is_arithmetic ty = true -> is_pointer ty = false.
Proof. induction ty; simpl; intros; eauto. Qed.

(** Formalizes https://eel.is/c++draft/basic.types.general#term.scalar.type.
  *)
Definition scalar_type (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tnullptr | Tptr _
  | Tmember_pointer _ _
  | Tfloat_ _
  | Tchar_ _
  | Tbool
  | Tnum _ _ | Tenum _ => true
  | _ => false
  end.
Lemma scalar_type_erase_drop ty :
  scalar_type (erase_qualifiers ty) = scalar_type (drop_qualifiers ty).
Proof. by induction ty. Qed.

(** [is_value_type t] returns [true] if [t] has value semantics.
    A value type is one that can be represented by [val].

    NOTE: The only difference between a value type and a scalar type is
    that [Tvoid] is a value type and not a scalar type.
 *)
Definition is_value_type (t : type) : bool :=
  match drop_qualifiers t with
  | Tnum _ _
  | Tchar_ _
  | Tbool
  | Tptr _
  | Tnullptr
  | Tfloat_ _
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

#[projections(primitive)]
Record vctype : Set := VCType { vctype_type : type; vctype_valcat : ValCat }.
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
