(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From bedrock.prelude.elpi Require Import derive.
From bedrock.prelude Require Import base bool list.
Require Export bedrock.lang.cpp.arith.types.
Require Import bedrock.lang.cpp.syntax.names.

Set Primitive Projections.

(* Type qualifiers *)
Variant type_qualifiers : Set :=
| QCV (* const volatile *)
| QC (* const *)
| QV (* volatile *)
| QM (* no qualifiers *)
.
#[only(inhabited,eq_dec,countable)] derive type_qualifiers.

Definition q_const (q : type_qualifiers) : bool :=
  match q with
  | QCV | QC => true
  | _ => false
  end.
Definition q_volatile (q : type_qualifiers) : bool :=
  match q with
  | QCV | QV => true
  | _ => false
  end.
Definition CV (const volatile : bool) :=
  match const , volatile with
  | true , true => QCV
  | true , false => QC
  | false , true => QV
  | false , false => QM
  end.

(* [merge_tq a b] computes the join of the restrictions of [a] and [b],
   i.e. if either [a] or [b] is const/volatile, the result will be const/volatile.
   This is used to compress adjacent qualifiers.
 *)
Definition merge_tq (a b : type_qualifiers) : type_qualifiers :=
  CV (q_const a || q_const b) (q_volatile a || q_volatile b).

#[global] Instance merge_tq_idemp : IdemP (=) merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_left_id : LeftId (=) QM merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_right_id : RightId (=) QM merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_left_absorb : LeftAbsorb (=) QCV merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_right_absorb : RightAbsorb (=) QCV merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_comm : Comm (=) merge_tq.
Proof. by intros [] []. Qed.
#[global] Instance merge_tq_assoc : Assoc (=) merge_tq.
Proof. by intros [] [] []. Qed.

Lemma merge_tq_QM_inj q1 q2 : merge_tq q1 q2 = QM -> q1 = QM /\ q2 = QM.
Proof. destruct q1, q2; naive_solver. Qed.

(**
The preorder from
<https://eel.is/c++draft/basic.type.qualifier#5>
*)
Definition tq_le (a b : type_qualifiers) : Prop :=
  ∃ c, b = merge_tq a c.

Definition is_tq_le (a b : type_qualifiers) : bool :=
  bool_decide (a = b) ||
  match a , b with
  | QM , _ => true
  | QC , QCV => true
  | QV , QCV => true
  | _, _ => false
  end.

Lemma tq_le_is_tq_le a b : tq_le a b <-> is_tq_le a b.
Proof.
  split.
  { intros (c & ->). by destruct a, c. }
  { rewrite /is_tq_le=>?. case_bool_decide.
    - subst a. exists QM. by destruct b.
    - destruct a, b; first [ done | by exists QV | by exists QC | by exists QCV ]. }
Qed.

#[global] Instance tq_le_dec : RelDecision tq_le.
Proof.
  refine (fun a b => cast_if (decide (is_tq_le a b))).
  all: abstract (by rewrite tq_le_is_tq_le).
Defined.

(* Calling conventions are a little bit beyond what is formally blessed by
   C++, but the are necessary for low level code that links with other
   languages.

   From the C++ standard point of view, we view these as opaque symbols with
   no particular meaning. All that matters is that when you call a function,
   that this calling convention matches between the caller and the callee.
   This is what ensures, for example, that when you call a function implemented
   in another language, that you have the appropriate annotations in place.
   For example, if you were calling an OpenCL kernel, then the function would
   have type [Tfunction (cc:=CC_OpenCLKernel) ..], and you would require that
   annotation in your program.
 *)
Variant calling_conv : Set :=
| CC_C
| CC_MsAbi
| CC_RegCall.
#[only(inhabited,eq_dec,countable)] derive calling_conv.

(* in almost all contexts, we are going to use [CC_C], so we're going to make
   that the default. Clients interested in specifying another calling convention
   should write, e.g., [Tfunction (cc:=CC_PreserveAll) ..] to specify the
   calling convention explicitly.
 *)
Existing Class calling_conv.
#[global] Existing Instance CC_C.

Variant function_arity : Set :=
| Ar_Definite
| Ar_Variadic.
#[only(inhabited,eq_dec,countable)] derive function_arity.

(* In almost all contexts, we will use [Ar_Definite], so that is the default. *)
Existing Class function_arity.
#[global] Existing Instance Ar_Definite.

(** Character types
    See https://en.cppreference.com/w/cpp/language/types
 *)
Module char_type.
  Variant t : Set :=
    | Cchar (* signedness defined by platform *)
    | Cwchar (* signedness defined by platform *)
    | C8 (* unsigned *)
    | C16 (* unsigned *)
    | C32. (* unsigned *)
  #[global] Instance t_eq_dec: EqDecision t.
  Proof. solve_decision. Defined.
  #[global] Instance t_countable : Countable t.
  Proof.
    apply (inj_countable'
      (λ cc,
        match cc with
        | Cchar => 0 | Cwchar => 1 | C8 => 2 | C16 => 3 | C32 => 4
        end)
      (λ n,
        match n with
        | 0 => Cchar | 1 => Cwchar | 2 => C8 | 3 => C16 | 4 => C32
        | _ => Cchar	(** dummy *)
        end)).
    abstract (by intros []).
  Defined.

  Definition bytesN (t : t) : N :=
    match t with
    | Cchar => 1
    | Cwchar => 4 (* TODO: actually 16-bits on Windows *)
    | C8 => 1
    | C16 => 2
    | C32 => 4
    end.
  #[global] Arguments bytesN !_ /.

  Definition bitsN (t : t) : N :=
    8 * bytesN t.
  #[global] Arguments bitsN !_ /.

End char_type.
Notation char_type := char_type.t.

(** Integer types
    See https://en.cppreference.com/w/cpp/language/types
 *)
Module int_type.
  (* the rank <https://eel.is/c++draft/conv.rank> *)
  Notation t := bitsize (only parsing).
  Notation rank := t (only parsing).

  Notation Ichar := W8 (only parsing).
  Notation Ishort := W16 (only parsing).
  Notation Iint := W32 (only parsing).
  Notation Ilong := W64 (only parsing).
  (** warning: LLP64 model uses [long_bits := W32] *)
  Notation Ilonglong := W64 (only parsing).

  Definition bytesN (t : t) : N :=
    arith.types.bytesN t. (* from [arith.types] *)

  Definition bitsN (t : t) : N :=
    8 * bytesN t.

  Definition t_le (a b : t) : Prop :=
    (bytesN a <= bytesN b)%N.

  #[global] Instance t_le_dec : RelDecision t_le :=
    fun a b => N.le_dec (bytesN a) (bytesN b).

  (* [max] on the rank. *)
  Definition t_max (a b : bitsize) : bitsize :=
    if bool_decide (t_le a b) then b else a.

End int_type.
Notation int_type := int_type.t.

Module float_type.
  Variant t : Set :=
    | Ffloat
    | Fdouble
    | Flongdouble.

  #[global] Instance t_eq_dec : EqDecision t := ltac:(solve_decision).
  #[global] Instance t_countable : Countable t.
  Proof.
    apply (inj_countable'
      (λ cc,
        match cc with
        | Ffloat => 0 | Fdouble => 1 | Flongdouble => 2
        end)
      (λ n,
        match n with
        | 0 => Ffloat | 1 => Fdouble | 2 => Flongdouble
        | _ => Ffloat	(** dummy *)
        end)).
    abstract (by intros []).
  Defined.

  Definition bytesN (t : t) : N :=
    match t with
    | Ffloat => 4
    | Fdouble => 8
    | Flongdouble => 16
    end.

  Definition bitsN (t : t) : N :=
    8 * bytesN t.

End float_type.

(* types *)
Inductive type : Set :=
| Tptr (_ : (*expr*)type)
| Tref (_ : (*expr*)type)
| Trv_ref (_ : (*expr*)type)
  (**
  Note: cpp2v (really, clang's parser) handles so-called "reference
  collapsing": We do not see references to references.

  Background:
  https://en.cppreference.com/w/cpp/language/reference#Reference_collapsing
  https://www.eel.is/c++draft/dcl.ref#5
  *)
| Tnum (size : int_type.t) (signed : signed)
| Tchar_ (_ : char_type)
| Tvoid
| Tarray (_ : type) (_ : N) (* unknown sizes are represented by pointers *)
| Tnamed (_ : globname)
| Tenum (_ : globname) (* enumerations *)
| Tfunction {cc : calling_conv} {ar : function_arity} (_ : (*decl*)type) (_ : list (*decl*)type)
| Tbool
| Tmember_pointer (_ : globname) (_ : (*expr*)type)
| Tfloat_ (_ : float_type.t)
| Tqualified (_ : type_qualifiers) (_ : type)
| Tnullptr
(* architecture-specific types; currently unused.
   some [Tarch] types, e.g. ARM SVE, are "sizeless", hence [option size]. *)
| Tarch (_ : option bitsize) (name : bs)
.
(**
For documentation purposes, we often use the following aliases.

- [decltype] _declaration types_ arise in variable declarations
(including function arguments)

- [exprtype] _expression types_ are assigned to expressions
(together with value categories) by the static semantics of C++

- [functype] _function types_ are known to be [Tfunction]

Roughly, we have an isomorphism [decltype ≅ exprtype × ValCat]. While
variables can be declared with reference types, expressions never have
reference types (that information being present in the expression's
value category).
*)
Definition decltype : Set := type.
Definition exprtype : Set := type.
Definition functype : Set := type.

#[only(inhabited)] derive type.

(** Strengthened Induction Principle for [type]

    [type] is a `Nested Inductive Type` due to the use of [list type]
    in the [Tfunction] constructor. In Coq, the default induction
    principle generated for a nested inductive type is too weak because
    it fails to thread the indexed predicate through the structure
    of the parameterized type family. While strengthened induction
    principles are not generally derivable, we can manually strengthen
    it if we can find a way to incorporate the nested uses of the Type.
    Luckily, we can use [List.Forall] to express that the indexed
    predicate must hold on each element of the list which is sufficient
    for the [normalize_type_idempotent] Lemma. For more information on
    this topic, please refer to [1].

    [1] http://adam.chlipala.net/cpdt/html/InductiveTypes.html;
          "Nested Inductive Types" Section
 *)
Section type_ind'.
  Variable P : type -> Prop.

  Hypothesis Tptr_ind' : forall (ty : type),
    P ty -> P (Tptr ty).
  Hypothesis Tref_ind' : forall (ty : type),
    P ty -> P (Tref ty).
  Hypothesis Trv_ref_ind' : forall (ty : type),
    P ty -> P (Trv_ref ty).
  Hypothesis Tnum_ind' : forall (size : bitsize) (sign : signed),
    P (Tnum size sign).
  Hypothesis Tchar__ind' : forall ct, P (Tchar_ ct).
  Hypothesis Tvoid_ind' : P Tvoid.
  Hypothesis Tarray_ind' : forall (ty : type) (sz : N),
    P ty -> P (Tarray ty sz).
  Hypothesis Tnamed_ind' : forall (name : globname),
    P (Tnamed name).
  Hypothesis Tenum_ind' : forall (name : globname),
    P (Tenum name).
  Hypothesis Tfunction_ind' : forall {cc : calling_conv} {ar : function_arity} (ty : type) (tys : list type),
    P ty -> Forall P tys -> P (Tfunction ty tys).
  Hypothesis Tbool_ind' : P Tbool.
  Hypothesis Tmember_pointer_ind' : forall (name : globname) (ty : type),
    P ty -> P (Tmember_pointer name ty).
  Hypothesis Tfloat_ind' : forall (size : float_type.t),
    P (Tfloat_ size).
  Hypothesis Tqualified_ind' : forall (q : type_qualifiers) (ty : type),
    P ty -> P (Tqualified q ty).
  Hypothesis Tnullptr_ind' : P Tnullptr.
  Hypothesis Tarch_ind' : forall (osize : option bitsize) (name : bs),
    P (Tarch osize name).

  Fixpoint type_ind' (ty : type) : P ty :=
    match ty with
    | Tptr ty                 => Tptr_ind' ty (type_ind' ty)
    | Tref ty                 => Tref_ind' ty (type_ind' ty)
    | Trv_ref ty              => Trv_ref_ind' ty (type_ind' ty)
    | Tnum sz sgn             => Tnum_ind' sz sgn
    | Tchar_ sz               => Tchar__ind' sz
    | Tvoid                   => Tvoid_ind'
    | Tarray ty sz            => Tarray_ind' ty sz (type_ind' ty)
    | Tnamed name             => Tnamed_ind' name
    | Tenum name              => Tenum_ind' name
    | Tfunction ty tys        =>
      Tfunction_ind' ty tys (type_ind' ty)
                     (* NOTE: We must use a nested [fix] in order to convince Coq that
                          the elements of [tys] are actually subterms of
                          [Tfunction ty tys]
                      *)
                     ((fix list_tys_ind' (tys : list type) : Forall P tys :=
                         match tys with
                         | []        => List.Forall_nil P
                         | ty :: tys' => List.Forall_cons P ty tys'
                                                        (type_ind' ty) (list_tys_ind' tys')
                         end) tys)
    | Tbool                   => Tbool_ind'
    | Tmember_pointer name ty => Tmember_pointer_ind' name ty (type_ind' ty)
    | Tfloat_ sz               => Tfloat_ind' sz
    | Tqualified q ty         => Tqualified_ind' q ty (type_ind' ty)
    | Tnullptr                => Tnullptr_ind'
    | Tarch osize name        => Tarch_ind' osize name
    end.
End type_ind'.

(* XXX merge type_eq_dec into type_eq. *)
Definition type_eq_dec : forall (ty1 ty2 : type), { ty1 = ty2 } + { ty1 <> ty2 }.
Proof.
  (* rewrite /RelDecision /Decision. *)
  fix IHty1 1.
  rewrite -{1}/(EqDecision type) in IHty1.
  decide equality; try solve_trivial_decision.
Defined.
#[global] Instance type_eq: EqDecision type := type_eq_dec.
Section type_countable.
  #[local] Notation BS x        := (GenLeaf (inr x)).
  #[local] Notation QUAL x      := (GenLeaf (inl (inr x))).
  #[local] Notation BITSIZE x   := (GenLeaf (inl (inl (inr x)))).
  #[local] Notation SIGNED x    := (GenLeaf (inl (inl (inl (inr x))))).
  #[local] Notation CC x        := (GenLeaf (inl (inl (inl (inl (inr x)))))).
  #[local] Notation AR x        := (GenLeaf (inl (inl (inl (inl (inl (inr x))))))).
  #[local] Notation N x         := (GenLeaf (inl (inl (inl (inl (inl (inl (inr x)))))))).
  #[local] Notation CHAR_TYPE x := (GenLeaf (inl (inl (inl (inl (inl (inl (inl (inr x))))))))).
  #[local] Notation FLOAT_TYPE x := (GenLeaf (inl (inl (inl (inl (inl (inl (inl (inl x))))))))).

  #[global] Instance type_countable : Countable type.
  Proof.
    set enc := fix go (t : type) :=
      match t with
      | Tptr t => GenNode 0 [go t]
      | Tref t => GenNode 1 [go t]
      | Trv_ref t => GenNode 2 [go t]
      | Tnum sz sgn => GenNode 3 [BITSIZE sz; SIGNED sgn]
      | Tvoid => GenNode 4 []
      | Tarray t n => GenNode 5 [go t; N n]
      | Tnamed gn => GenNode 6 [BS gn]
      | @Tfunction cc ar ret args => GenNode 7 $ (CC cc) :: (AR ar) :: go ret :: (go <$> args)
      | Tbool => GenNode 8 []
      | Tmember_pointer gn t => GenNode 9 [BS gn; go t]
      | Tfloat_ sz => GenNode 10 [FLOAT_TYPE sz]
      | Tqualified q t => GenNode 11 [QUAL q; go t]
      | Tnullptr => GenNode 12 []
      | Tarch None gn => GenNode 13 [BS gn]
      | Tarch (Some sz) gn => GenNode 14 [BITSIZE sz; BS gn]
      | Tenum gn => GenNode 15 [BS gn]
      | Tchar_ sz => GenNode 16 [CHAR_TYPE sz]
      end.
    set dec := fix go t :=
      match t with
      | GenNode 0 [t] => Tptr (go t)
      | GenNode 1 [t] => Tref (go t)
      | GenNode 2 [t] => Trv_ref (go t)
      | GenNode 3 [BITSIZE sz; SIGNED sgn] => Tnum sz sgn
      | GenNode 4 [] => Tvoid
      | GenNode 5 [t; N n] => Tarray (go t) n
      | GenNode 6 [BS gn] => Tnamed gn
      | GenNode 7 (CC cc :: AR ar :: ret :: args) => @Tfunction cc ar (go ret) (go <$> args)
      | GenNode 8 [] => Tbool
      | GenNode 9 [BS gn; t] => Tmember_pointer gn (go t)
      | GenNode 10 [FLOAT_TYPE sz] => Tfloat_ sz
      | GenNode 11 [QUAL q; t] => Tqualified q (go t)
      | GenNode 12 [] => Tnullptr
      | GenNode 13 [BS gn] => Tarch None gn
      | GenNode 14 [BITSIZE sz; BS gn] => Tarch (Some sz) gn
      | GenNode 15 [BS gn] => Tenum gn
      | GenNode 16 [CHAR_TYPE sz] => Tchar_ sz
      | _ => Tvoid	(** dummy *)
      end.
    apply (inj_countable' enc dec). refine (fix go t := _).
    destruct t as [| | | | | | | | |cc ar ret args| | | | | |[]]; simpl; f_equal; try done.
    induction args; simpl; f_equal; done.
  Defined.
End type_countable.

(**
An equivalence relation on types that quotients by "identical to C++".
The equations here are dictated by the fact that [type] is too big for
C++.
*)

Inductive type_equiv : Equiv type :=

(**
Qualifier normalization
*)
| Tqualified_id t : Tqualified QM t ≡ t
| Tqualified_merge q q' t : Tqualified q (Tqualified q' t) ≡ Tqualified (merge_tq q q') t
(*
"An array type whose elements are cv-qualified is also considered to
have the same cv-qualifications as its elements. [...] Cv-qualifiers
applied to an array type attach to the underlying element type."
<https://www.eel.is/c++draft/basic.type.qualifier#3>
*)
| Tqualified_array q t n : Tqualified q (Tarray t n) ≡ Tarray (Tqualified q t) n
(*
"A function or reference type is always cv-unqualified."
<https://www.eel.is/c++draft/basic.type.qualifier#1>
*)
| Tqualified_ref q t : Tqualified q (Tref t) ≡ Tref t
| Tqualified_rv_ref q t : Tqualified q (Trv_ref t) ≡ Trv_ref t
| Tqualified_func q cc ar ret args : Tqualified q (@Tfunction cc ar ret args) ≡ @Tfunction cc ar ret args
(**
"After producing the list of parameter types, any top-level
cv-qualifiers modifying a parameter type are deleted when forming the
function type."
<https://www.eel.is/c++draft/dcl.fct#5>
*)
| Tqualified_func_param cc ar ret q t args args' : @Tfunction cc ar ret (args ++ Tqualified q t :: args') ≡ @Tfunction cc ar ret (args ++ t :: args')

(** Equivalence *)
| type_equiv_refl t : t ≡ t
| type_equiv_sym t u : t ≡ u -> u ≡ t
| type_equiv_trans t u v : t ≡ u -> u ≡ v -> t ≡ v

(** Compatibility *)
| Tptr_proper : Proper (equiv ==> equiv) Tptr
| Tref_proper : Proper (equiv ==> equiv) Tref
| Trv_ref_proper : Proper (equiv ==> equiv) Trv_ref
| Tarray_proper : Proper (equiv ==> eq ==> equiv) Tarray
| Tfunction_proper cc ar : Proper (equiv ==> equiv ==> equiv) (@Tfunction cc ar)
| Tmember_pointer_proper gn : Proper (equiv ==> equiv) (Tmember_pointer gn)
| Tqualified_proper q : Proper (equiv ==> equiv) (Tqualified q)
.
#[global] Existing Instances
  type_equiv
  Tptr_proper
  Tref_proper
  Trv_ref_proper
  Tarray_proper
  Tfunction_proper
  Tmember_pointer_proper
  Tqualified_proper
.
#[global] Instance type_equivalence : Equivalence (≡@{type}) :=
  Build_Equivalence _ type_equiv_refl type_equiv_sym type_equiv_trans.

Notation Tpointer := Tptr (only parsing).
Notation Treference := Tref (only parsing).
Notation Trv_reference := Trv_ref (only parsing).
Notation Tfun := Tfunction (only parsing).

Definition Qconst_volatile : type -> type :=
  Tqualified QCV.
Definition Qconst : type -> type :=
  Tqualified QC.
Definition Qmut_volatile : type -> type :=
  Tqualified QV.
Definition Qmut : type -> type :=
  Tqualified QM.

#[global] Hint Opaque
  Qconst_volatile Qconst Qmut_volatile Qmut
: typeclass_instances.

#[global] Instance Qconst_volatile_proper : Proper (equiv ==> equiv) Qconst_volatile.
Proof. solve_proper. Qed.
#[global] Instance Qconst_proper : Proper (equiv ==> equiv) Qconst.
Proof. solve_proper. Qed.
#[global] Instance Qmut_volatile_proper : Proper (equiv ==> equiv) Qmut_volatile.
Proof. solve_proper. Qed.
#[global] Instance Qmut_proper : Proper (equiv ==> equiv) Qmut.
Proof. solve_proper. Qed.

Lemma Qmut_equiv t : Qmut t ≡ t.
Proof. by rewrite /Qmut Tqualified_id. Qed.

(** ** Qualifier normalization *)
(**
[decompose_type t] strips any top-level qualifiers from [t] and
returns them, paired with the rest of the type.

The underlying functions [qual_norm] and [qual_norm'] are similar
(see, e.g., [qual_norm_decompose_type]).
*)

Section qual_norm.
  Context {A : Type}.
  Variable f : type_qualifiers -> type -> A.

  Fixpoint qual_norm' (q : type_qualifiers) (t : type) : A :=
    match t with
    | Tqualified q' t => qual_norm' (merge_tq q q') t
    | _ => f q t
    end.
  #[global] Hint Opaque qual_norm' : typeclass_instances.

  Definition qual_norm : type -> A :=
    qual_norm' QM.
  #[global] Hint Opaque qual_norm : typeclass_instances.
End qual_norm.

Definition decompose_type : type -> type_qualifiers * type :=
  qual_norm (fun q t => (q, t)).
#[global] Hint Opaque decompose_type : typeclass_instances.
#[global] Arguments decompose_type !_ / : simpl nomatch, assert.

(**
[drop_qualifiers t] drops all the *leading* qualifiers of the type [t],
e.g. [drop_qualifiers (Qconst (Qmut t)) = t].
 *)
Fixpoint drop_qualifiers (t : type) : type :=
  match t with
  | Tqualified _ t => drop_qualifiers t
  | _ => t
  end.

(**
It would be nice to make this the default.
*)
#[local] Arguments decompose_type : simpl never.

(**
[is_qualified t] decides if [t] has top-level qualifiers.

Note: [is_qualified] is incompatible with the equivalence on types.
Counterexample: [Tqualified QM (Tref t) ≡ Tref t].
*)
Definition is_qualified (t : type) : bool :=
  if t is Tqualified _ _ then true else false.

Lemma is_qualified_spec t : is_qualified t <-> ∃ q t', t = Tqualified q t'.
Proof. split=>Hq. by destruct t; eauto. by destruct Hq as (?&?&->). Qed.

Lemma is_qualified_qual q t : is_qualified (Tqualified q t).
Proof. done. Qed.

Section qual_norm.
  Context {A : Type}.
  Implicit Types (f : type_qualifiers -> type -> A).

  (** [qual_norm'] *)

  Lemma qual_norm'_unfold f q t :
    qual_norm' f q t =
      if t is Tqualified q' t'
      then qual_norm' f (merge_tq q q') t'
      else f q t.
  Proof. by destruct t. Qed.

  (**
  We use this relation to state induction principles for things
  defined in terms of [qual_norm'] and [qual_norm].

  Example: [elim: (qual_norm_ok _ ty)] in a goal involving [qual_norm
  f ty] tends to be easier to use than [pattern (qual_norm f ty);
  induction using qual_norm_ind] because one need not repeat the
  function [f] in the proof script.
  *)

  Inductive qual_norm_spec f : type_qualifiers -> type -> A -> Prop :=
  | qual_norm_spec_unqual q t : ~~ is_qualified t -> qual_norm_spec f q t (f q t)
  | qual_norm_spec_qual q q' t' ret :
    qual_norm_spec f (merge_tq q q') t' ret ->
    qual_norm_spec f q (Tqualified q' t') ret
  .
  #[local] Hint Constructors qual_norm_spec : core.

  Lemma qual_norm'_ok f q t : qual_norm_spec f q t (qual_norm' f q t).
  Proof.
    move: q. induction t=>q.
    all: rewrite qual_norm'_unfold; auto.
  Qed.

  Lemma qual_norm'_unqual f q t : ~~ is_qualified t -> qual_norm' f q t = f q t.
  Proof.
    intros. rewrite qual_norm'_unfold. by destruct t.
  Qed.

  Lemma qual_norm'_idemp f q t : qual_norm' (qual_norm' f) q t = qual_norm' f q t.
  Proof.
    induction (qual_norm'_ok f q t).
    { by rewrite !qual_norm'_unqual. }
    { done. }
  Qed.

  (** [qual_norm] *)

  Lemma qual_norm_unfold f t :
    qual_norm f t =
      if t is Tqualified q' t'
      then qual_norm' f q' t'
      else f QM t.
  Proof.
    rewrite /qual_norm qual_norm'_unfold. f_equiv.
    by rewrite left_id_L.
  Qed.

  Lemma qual_norm_ok f t : qual_norm_spec f QM t (qual_norm f t).
  Proof. apply qual_norm'_ok. Qed.

  Lemma qual_norm_unqual f t : ~~ is_qualified t -> qual_norm f t = f QM t.
  Proof. apply qual_norm'_unqual. Qed.

  Lemma qual_norm_idemp f t : qual_norm (qual_norm' f) t = qual_norm f t.
  Proof. apply qual_norm'_idemp. Qed.
End qual_norm.

Lemma qual_norm'_bind {A B} (f : type_qualifiers -> type -> A) (g : A -> B) q t :
  g (qual_norm' f q t) = qual_norm' (fun q => g ∘ f q) q t.
Proof.
  induction (qual_norm'_ok f q t).
  { by rewrite qual_norm'_unqual. }
  { done. }
Qed.
Lemma qual_norm_bind {A B} (f : type_qualifiers -> type -> A) (g : A -> B) t :
  g (qual_norm f t) = qual_norm (fun q => g ∘ f q) t.
Proof. apply qual_norm'_bind. Qed.

Lemma qual_norm'_equiv q t : qual_norm' Tqualified q t ≡ Tqualified q t.
Proof.
  induction (qual_norm'_ok Tqualified q t).
  { done. }
  { by rewrite Tqualified_merge. }
Qed.
Lemma qual_norm_equiv t : qual_norm Tqualified t ≡ t.
Proof. by rewrite /qual_norm qual_norm'_equiv Tqualified_id. Qed.

(** [decompose_type] *)

Lemma decompose_type_unfold t :
  decompose_type t =
    if t is Tqualified q t' then
      let p := decompose_type t' in
      (merge_tq q p.1, p.2)
    else (QM, t).
Proof.
  rewrite /decompose_type qual_norm_unfold.
  destruct t as [| | | | | | | | | | | | |q t| |]; try done. set pair := fun x y => (x, y).
  move: q. induction t=>q; cbn; try by rewrite right_id_L.
  rewrite left_id_L !IHt /=. f_equal. by rewrite assoc_L.
Qed.

Inductive decompose_type_spec : type -> type_qualifiers * type -> Prop :=
| decompose_type_spec_unqual t : ~~ is_qualified t -> decompose_type_spec t (QM, t)
| decompose_type_spec_qual q t p :
  decompose_type_spec t p ->
  decompose_type_spec (Tqualified q t) (merge_tq q p.1, p.2)
.
#[local] Hint Constructors decompose_type_spec : core.

Lemma decompose_type_ok t : decompose_type_spec t (decompose_type t).
Proof.
  induction t.
  all: rewrite decompose_type_unfold; cbn; auto.
Qed.

Lemma is_qualified_decompose_type t : ~~ is_qualified (decompose_type t).2.
Proof. by induction (decompose_type_ok t). Qed.
#[global] Hint Resolve is_qualified_decompose_type | 0 : core.

Lemma decompose_type_unqual t : ~~ is_qualified t -> decompose_type t = (QM, t).
Proof. apply qual_norm_unqual. Qed.

Lemma decompose_type_qual q t :
  decompose_type (Tqualified q t) =
    let p := decompose_type t in
    (merge_tq q p.1, p.2).
Proof. by rewrite decompose_type_unfold. Qed.

Lemma decompose_type_idemp t :
  decompose_type (decompose_type t).2 = (QM, (decompose_type t).2).
Proof. by rewrite decompose_type_unqual. Qed.

Lemma decompose_type_equiv t : let p := decompose_type t in Tqualified p.1 p.2 ≡ t.
Proof.
  elim: (decompose_type_ok t); cbn.
  { intros. by rewrite Tqualified_id. }
  { intros ???? <-. by rewrite Tqualified_merge. }
Qed.

(** [qual_norm], [qual_norm'] in terms of [decompose_type] *)

Lemma qual_norm'_decompose_type {A} (f : type_qualifiers -> type -> A) q t :
  qual_norm' f q t =
    let p := decompose_type t in
    f (merge_tq q p.1) p.2.
Proof.
  move: q. induction t=>q /=; try by rewrite right_id_L.
  rewrite decompose_type_unfold IHt /=. by rewrite assoc_L.
Qed.

Lemma qual_norm_decompose_type {A} (f : type_qualifiers -> type -> A) t :
  qual_norm f t =
    let p := decompose_type t in
    f p.1 p.2.
Proof.
  rewrite /qual_norm qual_norm'_decompose_type. cbn.
  by rewrite left_id_L.
Qed.

(** [drop_qualifeirs] *)

Lemma is_qualified_drop_qualifiers ty : ~~ is_qualified (drop_qualifiers ty).
Proof. by induction ty. Qed.
#[global] Hint Resolve is_qualified_drop_qualifiers | 0 : core.

Lemma drop_qualifiers_unqual t : ~~ is_qualified t -> drop_qualifiers t = t.
Proof. by destruct t; cbn; auto. Qed.

Lemma drop_qualifiers_qual_norm' q t : drop_qualifiers t = qual_norm' (fun _ t => t) q t.
Proof.
  elim: (qual_norm'_ok _ q t).
  { intros. by rewrite drop_qualifiers_unqual. }
  { done. }
Qed.
Lemma drop_qualifiers_qual_norm t : drop_qualifiers t = qual_norm (fun _ t => t) t.
Proof. apply drop_qualifiers_qual_norm'. Qed.
Lemma drop_qualifiers_decompose_type t : drop_qualifiers t = (decompose_type t).2.
Proof. by rewrite drop_qualifiers_qual_norm qual_norm_decompose_type. Qed.

Lemma drop_qualifiers_idemp t : drop_qualifiers (drop_qualifiers t) = drop_qualifiers t.
Proof. by rewrite drop_qualifiers_unqual. Qed.

Lemma unqual_drop_qualifiers ty tq ty' : drop_qualifiers ty <> Tqualified tq ty'.
Proof. by induction ty. Qed.

Variant qual_norm_decomp_spec {A} (f : type_qualifiers → type → A) t : A -> Prop :=
| QualNormDecomp q' t' : (q', t') = decompose_type t -> qual_norm_decomp_spec f t (f q' t')
.

Lemma qual_norm_decomp_ok {A} (f : type_qualifiers → type → A) t : qual_norm_decomp_spec f t (qual_norm f t).
Proof.
  rewrite qual_norm_decompose_type.
  by constructor; rewrite -?surjective_pairing -?drop_qualifiers_decompose_type.
Qed.

(** ** Erasing qualifiers *)
(**
[erase_qualifiers t] erases *all* qualifiers that occur everywhere in
the type.

NOTE we currently use this because we do not track [const]ness in the
logic, this is somewhat reasonable because we often opt to express
this in separation logic. And the type system also enforces some of
the other criteria.
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

Lemma is_qualified_erase_qualifiers ty : ~~ is_qualified (erase_qualifiers ty).
Proof. by induction ty. Qed.
#[global] Hint Resolve is_qualified_erase_qualifiers | 0 : core.

Lemma erase_qualifiers_qual_norm' q t :
  erase_qualifiers t = qual_norm' (fun _ t => erase_qualifiers t) q t.
Proof. by elim: (qual_norm'_ok _ q t). Qed.
Lemma erase_qualifiers_qual_norm t :
  erase_qualifiers t = qual_norm (fun _ t => erase_qualifiers t) t.
Proof. apply erase_qualifiers_qual_norm'. Qed.
Lemma erase_qualifiers_decompose_type t :
  erase_qualifiers t = erase_qualifiers (decompose_type t).2.
Proof. by rewrite erase_qualifiers_qual_norm qual_norm_decompose_type. Qed.

Lemma erase_qualifiers_idemp t : erase_qualifiers (erase_qualifiers t) = erase_qualifiers t.
Proof.
  move: t. fix IHt 1=>t.
  destruct t as [| | | | | | | | |cc ar ret args| | | | | |]; cbn; auto with f_equal.
  { (* functions *) rewrite IHt. f_equal. induction args; cbn; auto with f_equal. }
Qed.

Lemma drop_erase_qualifiers t : drop_qualifiers (erase_qualifiers t) = erase_qualifiers t.
Proof. by rewrite drop_qualifiers_unqual. Qed.
Lemma erase_drop_qualifiers t : erase_qualifiers (drop_qualifiers t) = erase_qualifiers t.
Proof. induction t; cbn; auto. Qed.

#[deprecated(since="20230531", note="Use [drop_erase_qualifiers]")]
Notation drop_erase := drop_erase_qualifiers.
#[deprecated(since="20230531", note="Use [erase_drop_qualifiers]")]
Notation erase_drop := drop_erase_qualifiers.

Lemma unqual_erase_qualifiers ty tq ty' : erase_qualifiers ty <> Tqualified tq ty'.
Proof. by induction ty. Qed.

(** ** Qualifier simplification tactic *)
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

(** ** Smart constructors *)

(**
Qualify a type, merging nested qualifiers, suppressing [QM]
qualifiers, and (https://www.eel.is/c++draft/dcl.ref#1) discarding any
cv-qualifiers on reference types.
*)
Definition tqualified' (q : type_qualifiers) (t : type) : type :=
  match t with
  | Tref _ | Trv_ref _ => t
  | _ => match q with QM => t | _ => Tqualified q t end
  end.
#[global] Hint Opaque tqualified' : typeclass_instances.
#[global] Arguments tqualified' _ !_ / : simpl nomatch, assert.

Definition tqualified : type_qualifiers -> type -> type :=
  qual_norm' tqualified'.
#[global] Hint Opaque tqualified : typeclass_instances.
#[global] Arguments tqualified _ !_ / : simpl nomatch, assert.

(**
[drop_reference t] removes any leading reference types.
*)
Fixpoint drop_reference (t : type) : exprtype :=
  match drop_qualifiers t with
  | Tref u | Trv_ref u => drop_reference u
  | _ => t	(** We do not normalize qualifiers here to promote sharing *)
  end.

Succeed Example TEST_drop_reference : drop_reference (Qconst (Tnamed "T")) = Qconst (Tnamed "T") := eq_refl.
Succeed Example TEST_drop_reference : drop_reference (Qconst (Tref (Tnamed "T"))) = Tnamed "T" := eq_refl.
Succeed Example TEST_drop_reference : drop_reference (Qconst (Tref (Qconst $ Tnamed "T"))) = Qconst (Tnamed "T") := eq_refl.

(**
[tref], [trv_ref] implement reference collapsing.

Background:
https://en.cppreference.com/w/cpp/language/reference#Reference_collapsing
https://www.eel.is/c++draft/dcl.ref#5
*)
Fixpoint tref (acc : type_qualifiers) (t : type) : type :=
  match t with
  | Tref t | Trv_ref t => tref QM t
  | Tqualified q t => tref (merge_tq acc q) t
  | _ => Tref (tqualified acc t)
  end.
#[global] Hint Opaque tref : typeclass_instances.
#[global] Arguments tref _ !_ / : simpl nomatch, assert.

Fixpoint trv_ref (acc : type_qualifiers) (t : type) : type :=
  match t with
  | Tref t => tref QM t
  | Trv_ref t => trv_ref QM t
  | Tqualified q t => trv_ref (merge_tq acc q) t
  | _ => Trv_ref (tqualified acc t)
  end.
#[global] Hint Opaque trv_ref : typeclass_instances.
#[global] Arguments trv_ref _ !_ / : simpl nomatch, assert.

(**
[is_ref t] decides if [t] a reference type

Note: [is_ref] is incompatible with the equivalence on types.
Counterexample: [Tqualified QM (Tref t) ≡ Tref t].
*)
Definition is_ref (t : type) : bool :=
  if t is (Tref _ | Trv_ref _) then true else false.

Lemma is_ref_spec t : is_ref t <-> ∃ t', t = Tref t' \/ t = Trv_ref t'.
Proof. split=>Href. by destruct t; eauto. by destruct Href as (?&[-> | ->]). Qed.

Lemma is_ref_unqualified t : is_ref t -> ~~ is_qualified t.
Proof. by destruct t. Qed.

Lemma is_ref_drop_qualifiers t : is_ref t -> is_ref (drop_qualifiers t).
Proof. by destruct t. Qed.

(**
[is_QM cv] decides if [cv] is the neutral qualifier [QM]
*)
Definition is_QM (cv : type_qualifiers) : bool :=
  if cv is QM then true else false.

Lemma is_QM_spec cv : is_QM cv <-> cv = QM.
Proof. by destruct cv. Qed.
Lemma is_QM_bool_decide cv : is_QM cv = bool_decide (cv = QM).
Proof. by destruct cv. Qed.

(** [tqualified] *)

Variant tqualified'_spec : type_qualifiers -> type -> type -> Prop :=
| tqualified'_spec_ref q t : is_ref t -> tqualified'_spec q t t
| tqualified'_spec_unqual t : ~~ is_ref t -> tqualified'_spec QM t t
| tqualified'_spec_qual q t : ~~ is_ref t -> ~~ is_QM q -> tqualified'_spec q t (Tqualified q t)
.
#[local] Hint Constructors tqualified'_spec : core.

Lemma tqualified'_ok q t : tqualified'_spec q t (tqualified' q t).
Proof.
  rewrite /tqualified'. destruct (boolP (is_ref t)); [by destruct t; auto|].
  destruct t; try done.
  all: destruct (boolP (is_QM q)); by destruct q; auto.
Qed.

Lemma tqualified'_equiv q t : tqualified' q t ≡ Tqualified q t.
Proof.
  case: (tqualified'_ok q t).
  { intros ?? (?&[-> | ->])%is_ref_spec.
    by rewrite Tqualified_ref. by rewrite Tqualified_rv_ref. }
  { intros. by rewrite Tqualified_id. }
  { done. }
Qed.

#[global] Instance: Params (@tqualified') 1 := {}.
#[global] Instance tqualified'_proper q : Proper (equiv ==> equiv) (tqualified' q).
Proof. intros t1 t2 Ht. by rewrite !tqualified'_equiv Ht. Qed.

Lemma tqualified'_ref q t : is_ref t -> tqualified' q t = t.
Proof. by destruct t. Qed.

Lemma tqualified'_QM t : tqualified' QM t = t.
Proof. by destruct t. Qed.

Lemma tqualified'_non_ref q t : ~~ is_ref t -> ~~ is_QM q -> tqualified' q t = Tqualified q t.
Proof. by destruct t, q. Qed.

Lemma tqualified_ok q t : qual_norm_spec tqualified' q t (tqualified q t).
Proof. apply qual_norm'_ok. Qed.

Lemma tqualified_equiv q t : tqualified q t ≡ Tqualified q t.
Proof.
  induction (tqualified_ok q t).
  { by rewrite tqualified'_equiv. }
  { by rewrite Tqualified_merge. }
Qed.

#[global] Instance: Params (@tqualified) 1 := {}.
#[global] Instance tqualified_proper q : Proper (equiv ==> equiv) (tqualified q).
Proof. intros t1 t2 Ht. by rewrite !tqualified_equiv Ht. Qed.

Lemma tqualified_tqualified' q t : tqualified q t ≡ tqualified' q t.
Proof. by rewrite tqualified_equiv tqualified'_equiv. Qed.

Lemma tqualified_qual_norm' q t : tqualified q t = qual_norm' tqualified' q t.
Proof. done. Qed.

Lemma tqualified_decompose_type q t :
  tqualified q t =
    let p := decompose_type t in
    tqualified' (merge_tq q p.1) p.2.
Proof.
  by rewrite tqualified_qual_norm' qual_norm'_decompose_type.
Qed.

Lemma tqualified_unqual q t : ~~ is_qualified t -> tqualified q t = tqualified' q t.
Proof. intros. by rewrite /tqualified qual_norm'_unqual. Qed.

Lemma tqualified_idemp q1 q2 t :
  tqualified q1 (tqualified q2 t) = tqualified (merge_tq q1 q2) t.
Proof.
  elim: (tqualified_ok q2 t) q1; last first.
  { intros ????? IH ?. rewrite {}IH /=. by rewrite !assoc_L. }
  intros q2' t' ? q1. destruct (tqualified'_ok q2' t').
  - rewrite !tqualified_unqual//. by rewrite !tqualified'_ref.
  - rewrite !tqualified_unqual//. by rewrite right_id_L.
  - done.
Qed.

Lemma drop_qualifiers_tqualified q t :
  drop_qualifiers (tqualified q t) = drop_qualifiers t.
Proof.
  induction (tqualified_ok q t).
  { by destruct (tqualified'_ok q t). }
  { done. }
Qed.

Lemma erase_qualifiers_tqualified q t :
  erase_qualifiers (tqualified q t) = erase_qualifiers t.
Proof.
  induction (tqualified_ok q t).
  { by destruct (tqualified'_ok q t). }
  { done. }
Qed.

(** [tref] *)

Inductive tref_spec : type_qualifiers -> type -> type -> Prop :=
| tref_spec_nonref_unqual q t : ~~ is_ref t -> ~~ is_qualified t -> tref_spec q t (Tref $ tqualified q t)
| tref_spec_ref q t ret : tref_spec QM t ret -> tref_spec q (Tref t) ret
| tref_spec_rv_ref q t ret : tref_spec QM t ret -> tref_spec q (Trv_ref t) ret
| tref_spec_qual q q' t ret : tref_spec (merge_tq q q') t ret -> tref_spec q (Tqualified q' t) ret
.
#[local] Hint Constructors tref_spec : core.

Lemma tref_ok q t : tref_spec q t (tref q t).
Proof. move: q. induction t=>q; auto. Qed.

(*
Lemma tref_equiv' q t : tref q t ≡ Tref (Tqualified q t).
Proof.
  elim: (tref_ok q t).
  { intros. by rewrite tqualified_equiv. }
  { intros ???? ->. by rewrite Tqualified_id Tqualified_ref Tref_ref. }
  { intros ???? ->. by rewrite Tqualified_id Tqualified_rv_ref Tref_rv_ref. }
  { intros. by rewrite Tqualified_merge. }
Qed.
Lemma tref_equiv t : tref QM t ≡ Tref t.
Proof. by rewrite tref_equiv' Tqualified_id. Qed.

#[global] Instance: Params (@tref) 1 := {}.
#[global] Instance tref_proper q : Proper (equiv ==> equiv) (tref q).
Proof. intros t1 t2 Ht. by rewrite !tref_equiv' Ht. Qed.
*)

Lemma tref_unfold q t :
  tref q t =
    qual_norm' (fun q' t' =>
      match t' with
      | Tref t'' | Trv_ref t'' => tref QM t''
      | _ => Tref (tqualified q' t')
      end
    ) q t.
Proof. move: q. by induction t; cbn. Qed.

(** [trv_ref] *)

Inductive trv_ref_spec : type_qualifiers -> type -> type -> Prop :=
| trv_ref_nonref_unqual q t : ~~ is_ref t -> ~~ is_qualified t -> trv_ref_spec q t (Trv_ref $ tqualified q t)
| trv_ref_spec_ref q t : trv_ref_spec q (Tref t) (tref QM t)
| trv_ref_spec_rv_ref q t ret : trv_ref_spec QM t ret -> trv_ref_spec q (Trv_ref t) ret
| trv_ref_spec_qual q q' t ret : trv_ref_spec (merge_tq q q') t ret -> trv_ref_spec q (Tqualified q' t) ret
.
#[local] Hint Constructors trv_ref_spec : core.

Lemma trv_ref_ok q t : trv_ref_spec q t (trv_ref q t).
Proof. move: q; induction t=>q; auto. Qed.

(*
Lemma trv_ref_equiv' q t : trv_ref q t ≡ Trv_ref (Tqualified q t).
Proof.
  elim: (trv_ref_ok q t).
  { intros. by rewrite tqualified_equiv. }
  { intros. by rewrite tref_equiv' Tqualified_id Tqualified_ref Trv_ref_ref. }
  { intros ???? ->. by rewrite Tqualified_id Tqualified_rv_ref Trv_ref_rv_ref. }
  { intros. by rewrite Tqualified_merge. }
Qed.
Lemma trv_ref_equiv t : trv_ref QM t ≡ Trv_ref t.
Proof. by rewrite trv_ref_equiv' Tqualified_id. Qed.

#[global] Instance: Params (@trv_ref) 1 := {}.
#[global] Instance trv_ref_proper q : Proper (equiv ==> equiv) (trv_ref q).
Proof. intros t1 t2 Ht. by rewrite !trv_ref_equiv' Ht. Qed.
*)

Lemma trv_ref_unfold q t :
  trv_ref q t =
    qual_norm' (fun q' t' =>
      match t' with
      | Tref t'' => tref QM t''
      | Trv_ref t'' => trv_ref QM t''
      | _ => Trv_ref (tqualified q' t')
      end
    ) q t.
Proof. move: q. by induction t; cbn. Qed.

(** ** Type normalization *)
(**
normalization of types
- compresses adjacent [Tqualified] constructors
- drops (irrelevant) qualifiers on function arguments
 *)
Fixpoint normalize_type (t : type) : type :=
  let drop_norm := qual_norm (fun _ t => normalize_type t) in
  let qual_norm :=
    (* merge adjacent qualifiers and then normalize *)
    qual_norm' (fun q t => tqualified q (normalize_type t))
  in
  match t with
  | Tpointer t => Tpointer (normalize_type t)
  | Tref t => Tref (normalize_type t)
  | Trv_ref t => Trv_ref (normalize_type t)
  | Tarray t n => Tarray (normalize_type t) n
  | @Tfunction cc ar r args =>
    Tfunction (cc:=cc) (ar:=ar) (normalize_type r) (List.map drop_norm args)
  | Tmember_pointer gn t => Tmember_pointer gn (normalize_type t)
  | Tqualified q t => qual_norm q t
  | Tnum _ _ => t
  | Tchar_ _ => t
  | Tbool => t
  | Tvoid => t
  | Tnamed _ => t
  | Tenum _ => t
  | Tnullptr => t
  | Tfloat_ _ => t
  | Tarch _ _ => t
  end.

Section normalize_type_idempotent.

  Fixpoint _drop_norm_idempotent q q' ty {struct ty}:
    qual_norm' (fun _ t => normalize_type t) q (qual_norm' (fun _ t => normalize_type t) q' ty) =
    qual_norm' (fun _ t => normalize_type t) (merge_tq q q') ty
  with _qual_norm_idempotent q ty {struct ty}:
    normalize_type (qual_norm' (fun q t => tqualified q (normalize_type t)) q ty) =
    qual_norm' (fun q t => tqualified q (normalize_type t)) q ty
  with normalize_type_idempotent ty {struct ty}:
    normalize_type (normalize_type ty) = normalize_type ty.
  Proof.
    { (* _drop_norm_involutive *)
      generalize dependent q; generalize dependent q';
        induction ty using type_ind'; intros *;
        rewrite /qual_norm/= ?normalize_type_idempotent//.
      - f_equal.
        rewrite map_map /qual_norm /merge_tq/=;
          erewrite map_ext_Forall; first done; eapply Forall_impl;
          [eassumption|]; intros * HForall; simpl in HForall; apply HForall.
      - by rewrite IHty !assoc_L.
    }
    { (* _qual_norm_involutive *)
      intros *; generalize dependent q;
        induction ty using type_ind'; intros *; simpl;
        try solve[destruct q; simpl; now rewrite ?normalize_type_idempotent].
      destruct q; simpl;
        rewrite map_map /qual_norm ?_drop_norm_idempotent /merge_tq/=;
        rewrite normalize_type_idempotent;
        try solve[erewrite map_ext_Forall; eauto; induction tys;
                  [ now constructor
                  | constructor;
                    [ now apply _drop_norm_idempotent
                    | apply IHtys; now apply Forall_inv_tail in H]]]. }
    { (* normalize_type_involutive *)
      intros *; induction ty using type_ind'; simpl; rewrite ?IHty; eauto.
      rewrite map_map /qual_norm /merge_tq/=.
      erewrite map_ext_Forall; eauto; induction tys;
        [ now constructor
        | constructor;
          [ now apply _drop_norm_idempotent
          | apply IHtys; now apply Forall_inv_tail in H]]. }
  Qed.
End normalize_type_idempotent.

Lemma normalize_type_qual_norm t :
  normalize_type t = qual_norm (fun q t' => tqualified q (normalize_type t')) t.
Proof. rewrite qual_norm_unfold. by destruct t. Qed.

(** ** Qualifier-aware type operations *)

(**
[unptr t] returns the type of the object that a value of type [t]
points to or [None] if [t] is not a pointer type.
*)
Definition unptr (t : type) : option type :=
  match drop_qualifiers t with
  | Tptr p => Some p
  | _ => None
  end.

(**
[class_name t] returns the name of the class that this type refers to
*)
Definition class_name (t : type) : option globname :=
  match drop_qualifiers t with
  | Tnamed gn => Some gn
  | _ => None
  end.

(**
[is_arithmetic ty] states whether [ty] is an arithmetic type
*)
Definition is_arithmetic (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tnum _ _
  | Tchar_ _
  | Tenum _
  | Tbool => true
  | _ => false
  end.

(**
[is_pointer ty] is [true] if [ty] is a pointer type
*)
Definition is_pointer (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tptr _ => true
  | _ => false
  end.

Lemma is_pointer_not_arithmetic : forall ty, is_pointer ty = true -> is_arithmetic ty = false.
Proof. induction ty; simpl; intros; eauto. Qed.
Lemma is_arithmetic_not_pointer : forall ty, is_arithmetic ty = true -> is_pointer ty = false.
Proof. induction ty; simpl; intros; eauto. Qed.

(**
Formalizes https://eel.is/c++draft/basic.types.general#term.scalar.type.
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

(**
[is_value_type t] returns [true] if [t] has value semantics. A value
type is one that can be represented by [val].

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
  (**
  NOTE: In C++ the the underlying type of an enumeration must be an
  integral type. This definition pre-supposes [t] a valid enumeration.
  *)
  | Tenum _ (* enum types are value types *)
  | Tvoid => true
  | _ => false
  end.

Lemma is_value_type_erase_qualifiers ty :
  is_value_type (erase_qualifiers ty) = is_value_type ty.
Proof. induction ty; cbn; auto. Qed.
Lemma is_value_type_drop_qualifiers ty :
  is_value_type (drop_qualifiers ty) = is_value_type ty.
Proof. induction ty; cbn; auto. Qed.

Lemma is_value_type_qual_norm' q t :
  is_value_type t = qual_norm' (fun _ t' => is_value_type t') q t.
Proof. by elim: (qual_norm'_ok _ q t). Qed.
Lemma is_value_type_qual_norm t :
  is_value_type t = qual_norm (fun _ t' => is_value_type t') t.
Proof. apply is_value_type_qual_norm'. Qed.
Lemma is_value_type_decompose_type t :
  is_value_type t = is_value_type (decompose_type t).2.
Proof. by rewrite is_value_type_qual_norm qual_norm_decompose_type. Qed.

(** For use in [init_validR] *)
Fixpoint zero_sized_array ty : bool :=
  qual_norm (fun _ t => match t with
                     | Tarray ety n =>
                         if bool_decide (n = 0%N) then true
                         else zero_sized_array ety
                     | _ => false
                     end) ty.
#[global] Arguments zero_sized_array !_ /.

(**
[is_reference_type t] returns [true] if [t] is a (possibly
cv-qualified) reference type.
*)
Definition is_reference_type (t : type) : bool :=
  is_ref (drop_qualifiers t).

Lemma is_ref_incl t : is_ref t -> is_reference_type t.
Proof. apply is_ref_drop_qualifiers. Qed.

Lemma value_type_non_ref {ty} : is_value_type ty -> ~~ is_reference_type ty.
Proof. by induction ty. Qed.

Lemma is_reference_type_erase_qualifiers t :
  is_reference_type (erase_qualifiers t) = is_reference_type t.
Proof. induction t; cbn; auto. Qed.
Lemma is_reference_type_drop_qualifiers t :
  is_reference_type (drop_qualifiers t) = is_reference_type t.
Proof. induction t; cbn; auto. Qed.

Lemma is_reference_type_qual_norm' q t :
  is_reference_type t = qual_norm' (fun _ t => is_reference_type t) q t.
Proof. by elim: (qual_norm'_ok _ q t). Qed.
Lemma is_reference_type_qual_norm t :
  is_reference_type t = qual_norm (fun _ t => is_reference_type t) t.
Proof. apply is_reference_type_qual_norm'. Qed.
Lemma is_reference_type_decompose_type t :
  is_reference_type t = is_reference_type (decompose_type t).2.
Proof. by rewrite is_reference_type_qual_norm qual_norm_decompose_type. Qed.

(**
[as_ref' f x t] applies [f u] if [t] is a (possibly cv-qualified)
reference type with underlying type [u], defaulting to [x] if [t] is
not a reference type.

The special cases [as_ref t : type] and [as_ref_option : option type]
return the underlying type [u] (defaulting, respectively, to a dummy
type and to [None]).
*)

Definition as_ref' {A} (f : exprtype -> A) (x : A) (t : type) : A :=
  if drop_qualifiers t is (Tref u | Trv_ref u) then f u else x.
Notation as_ref := (as_ref' (fun u => u) Tvoid).
Notation as_ref_option := (as_ref' Some None).

Lemma as_ref'_erase_qualifiers {A} (f : exprtype -> A) (x : A) t :
  as_ref' f x (erase_qualifiers t) = as_ref' (f ∘ erase_qualifiers) x t.
Proof. induction t; cbn; auto. Qed.
Lemma as_ref_erase_qualifiers t :
  as_ref (erase_qualifiers t) = erase_qualifiers (as_ref t).
Proof. induction t; cbn; auto. Qed.

Section as_ref'.
  Context {A : Type} (f : exprtype -> A) (x : A).
  #[local] Notation as_ref' := (as_ref' f x).

  Lemma as_ref_drop_qualifiers t : as_ref' (drop_qualifiers t) = as_ref' t.
  Proof. induction t; cbn; auto. Qed.
  Lemma as_ref_qual_norm' q t : as_ref' t = qual_norm' (fun _ t => as_ref' t) q t.
  Proof. by elim: (qual_norm'_ok _ q t). Qed.
  Lemma as_ref_qual_norm t : as_ref' t = qual_norm (fun _ t => as_ref' t) t.
  Proof. apply as_ref_qual_norm'. Qed.
  Lemma as_ref_decompose_type t : as_ref' t = as_ref' (decompose_type t).2.
  Proof. by rewrite as_ref_qual_norm qual_norm_decompose_type. Qed.
End as_ref'.

(**
[is_aggregate_type t] returns [true] if [t] is a (possibly qualified)
structure or array type.
*)
Definition is_aggregate_type (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tnamed _ | Tarray _ _ => true
  | _ => false
  end.

Lemma is_aggregate_type_drop_qualifiers ty :
  is_aggregate_type (drop_qualifiers ty) = is_aggregate_type ty.
Proof.
  by rewrite /is_aggregate_type drop_qualifiers_idemp.
Qed.
Lemma is_aggregate_type_erase_qualifiers ty :
  is_aggregate_type (erase_qualifiers ty) = is_aggregate_type ty.
Proof. by induction ty. Qed.

Lemma is_aggregate_type_qual_norm' cv ty :
  is_aggregate_type ty = qual_norm' (fun _ ty' => is_aggregate_type ty') cv ty.
Proof. by elim: (qual_norm'_ok _ _ _). Qed.
Lemma is_aggregate_type_qual_norm ty :
  is_aggregate_type ty = qual_norm (fun _ ty' => is_aggregate_type ty')  ty.
Proof. apply is_aggregate_type_qual_norm'. Qed.
Lemma is_aggregate_type_decompose_type ty :
  is_aggregate_type ty = is_aggregate_type (decompose_type ty).2.
Proof.
  by rewrite is_aggregate_type_qual_norm qual_norm_decompose_type.
Qed.

Lemma aggregate_type_non_ref ty : is_aggregate_type ty -> ~~ is_reference_type ty.
Proof. by induction ty. Qed.
Lemma aggregate_type_non_val ty : is_aggregate_type ty -> ~~ is_value_type ty.
Proof. by induction ty. Qed.

(** ** Notation for character types *)
Coercion Tchar_ : char_type.t >-> type.
Notation Tchar   := (Tchar_ char_type.Cchar).
Notation Twchar  := (Tchar_ char_type.Cwchar).
Notation Tchar8  := (Tchar_ char_type.C8).
Notation Tchar16 := (Tchar_ char_type.C16).
Notation Tchar32 := (Tchar_ char_type.C32).

(** ** Types with explicit size information. *)

Notation Ti8    := (Tnum W8 Signed).
Notation Tu8    := (Tnum W8 Unsigned).
Notation Ti16   := (Tnum W16 Signed).
Notation Tu16   := (Tnum W16 Unsigned).
Notation Ti32   := (Tnum W32 Signed).
Notation Tu32   := (Tnum W32 Unsigned).
Notation Ti64   := (Tnum W64 Signed).
Notation Tu64   := (Tnum W64 Unsigned).
Notation Ti128  := (Tnum W128 Signed).
Notation Tu128  := (Tnum W128 Unsigned).

(* note(gmm): types without explicit size information need to
 * be parameters of the underlying code, otherwise we can't
 * describe the semantics correctly.
 * - cpp2v should probably insert these types.
 *)
(**
https://en.cppreference.com/w/cpp/language/types
The 4 definitions below use the LP64 data model.
LLP64 and LP64 agree except for the [long] type: see
the warning below.
In future, we may want to parametrize by a data model, or
the machine word size.
(** warning: LLP64 model uses [long_bits := W32] *)
*)
Notation char_bits      := (int_type.Ichar)     (only parsing).
Notation short_bits     := (int_type.Ishort)    (only parsing).
Notation int_bits       := (int_type.Iint)      (only parsing).
Notation long_bits      := (int_type.Ilong)     (only parsing).
Notation long_long_bits := (int_type.Ilonglong) (only parsing).

(** ** Types with implicit size information. *)

Notation Tschar  := (Tnum int_type.Ichar Signed) (only parsing).
Notation Tuchar  := (Tnum int_type.Ichar Unsigned) (only parsing).

Notation Tushort := (Tnum int_type.Ishort Unsigned) (only parsing).
Notation Tshort  := (Tnum int_type.Ishort Signed) (only parsing).

Notation Tint  := (Tnum int_type.Iint Signed) (only parsing).
Notation Tuint := (Tnum int_type.Iint Unsigned) (only parsing).

Notation Tulong := (Tnum int_type.Ilong Unsigned) (only parsing).
Notation Tlong  := (Tnum int_type.Ilong Signed) (only parsing).

Notation Tulonglong := (Tnum int_type.Ilonglong Unsigned) (only parsing).
Notation Tlonglong  := (Tnum int_type.Ilonglong Signed) (only parsing).

Notation Tfloat := (Tfloat_ float_type.Ffloat).
Notation Tdouble := (Tfloat_ float_type.Fdouble).
Notation Tlongdouble := (Tfloat_ float_type.Flongdouble).
