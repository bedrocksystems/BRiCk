(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Export bedrock.lang.cpp.arith.types.
Require Import bedrock.lang.cpp.syntax.names.

From bedrock.prelude.elpi Require Import derive.

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

  Definition bitsN (t : t) : N :=
    8 * bytesN t.

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
    fun a b => N_le_dec (bytesN a) (bytesN b).

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
| Tptr (_ : type)
| Tref (_ : type)
| Trv_ref (_ : type)
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
| Tfunction {cc : calling_conv} {ar : function_arity} (_ : type) (_ : list type)
| Tbool
| Tmember_pointer (_ : globname) (_ : type)
| Tfloat_ (_ : float_type.t)
| Tqualified (_ : type_qualifiers) (_ : type)
| Tnullptr
(* architecture-specific types; currently unused.
   some [Tarch] types, e.g. ARM SVE, are "sizeless", hence [option size]. *)
| Tarch (_ : option bitsize) (name : bs)
.

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
    | Tqualified q' t => qual_norm' (merge_tq q' q) t
    | _ => f q t
    end.

  Definition qual_norm : type -> A :=
    qual_norm' QM.
End qual_norm.

Definition decompose_type : type -> type_qualifiers * type :=
  qual_norm (fun q t => (q, t)).
#[global] Arguments decompose_type !_ / : simpl nomatch, assert.
(**
It would be nice to make this the default.
*)
#[local] Arguments decompose_type : simpl never.

(**
[Unqualified t] means [t] lacks top-level qualifiers.

Aside: An equivalence relation on types identifying [Tqualified QM t]
and [t] might enable simplifications elsewhere.
*)
Definition Unqualified (t : type) : Prop := ¬ ∃ q t', t = Tqualified q t'.
#[global] Arguments Unqualified : simpl never.
#[global] Hint Opaque Unqualified : typeclass_instances.

#[local] Definition qualifiedb (t : type) : bool :=
  if t is Tqualified _ _ then true else false.
#[local] Lemma Unqualified_qualifiedb t : Unqualified t <-> ¬ qualifiedb t.
Proof.
  rewrite /Unqualified. f_equiv. split.
  - by intros (q & t' & ->).
  - rewrite /qualifiedb. case_match; naive_solver.
Qed.

#[global] Instance Unqualified_dec t : Decision (Unqualified t).
Proof.
  refine (cast_if (decide (¬ qualifiedb t)));
    abstract (by rewrite Unqualified_qualifiedb).
Defined.

Lemma unqualified_qual q t : ¬ Unqualified (Tqualified q t).
Proof. by rewrite Unqualified_qualifiedb dec_stable_iff. Qed.

(**
Teach TC resolution to prove [Unqualified t] when [t] a constructor.
*)
Existing Class Unqualified.
#[global] Hint Mode Unqualified ! : typeclass_instances.
#[global] Instance Unqualified_instance t :
  TCEq (qualifiedb t) false -> Unqualified t | 50.
Proof. rewrite TCEq_eq Unqualified_qualifiedb=>->. tauto. Qed.

Section qual_norm.
  Context {A : Type}.
  Implicit Types (f : type_qualifiers -> type -> A).

  (** [qual_norm'] *)

  Lemma qual_norm'_unfold f q t :
    qual_norm' f q t =
      if t is Tqualified q' t
      then qual_norm' f (merge_tq q' q) t
      else f q t.
  Proof. by destruct t. Qed.

  Lemma qual_norm'_prepost
      (Pre : type_qualifiers -> type -> Prop)
      (Post : A -> Prop) q t f :
    Pre q t ->
    (∀ q q' t', Pre q (Tqualified q' t') -> Pre (merge_tq q' q) t') ->
    (∀ q' t', Unqualified t' -> Pre q' t' -> Post (f q' t')) ->
    Post (qual_norm' f q t).
  Proof.
    intros Hpre HR Hf. move: q Hpre. induction t=>q; try exact: Hf.
    rewrite qual_norm'_unfold. move/HR. apply IHt.
  Qed.

  (** [qual_norm] *)

  Lemma qual_norm_unfold f t :
    qual_norm f t =
      if t is Tqualified q t
      then qual_norm' f q t
      else f QM t.
  Proof.
    rewrite /qual_norm qual_norm'_unfold. f_equiv.
    by rewrite right_id_L.
  Qed.

  Lemma qual_norm_prepost
      (Pre : type_qualifiers -> type -> Prop)
      (Post : A -> Prop) f t :
    Pre QM t ->
    (∀ q q' t', Pre q (Tqualified q' t') -> Pre (merge_tq q' q) t') ->
    (∀ q' t', Unqualified t' -> Pre q' t' -> Post (f q' t')) ->
    Post (qual_norm f t).
  Proof. apply qual_norm'_prepost. Qed.
End qual_norm.

(** [decompose_type] *)

Lemma decompose_type_unfold t :
  decompose_type t =
    if t is Tqualified q t then
      let p := decompose_type t in
      (merge_tq q p.1, p.2)
    else (QM, t).
Proof.
  rewrite /decompose_type qual_norm_unfold.
  destruct t as [| | | | | | | | | | | | |q t| |]; try done. set pair := fun x y => (x, y).
  move: q. induction t=>q; try by rewrite right_id_L.
  cbn. rewrite right_id_L !IHt /=. f_equal.
  rewrite assoc_L. f_equal. by rewrite comm_L.
Qed.

Lemma decompose_type_qual q t :
  decompose_type (Tqualified q t) =
    let p := decompose_type t in
    (merge_tq q p.1, p.2).
Proof. by rewrite decompose_type_unfold. Qed.

Lemma decompose_type_prepost
    (Pre : type_qualifiers -> type -> Prop)
    (Post : type_qualifiers * type -> Prop) t :
  Pre QM t ->
  (∀ q q' t', Pre q (Tqualified q' t') -> Pre (merge_tq q' q) t') ->
  (∀ q' t', Unqualified t' -> Pre q' t' -> Post (q', t')) ->
  Post (decompose_type t).
Proof. apply qual_norm_prepost. Qed.

(** [qual_norm], [qual_norm'] in terms of [decompose_type] *)

Lemma qual_norm'_decompose_type {A} (f : type_qualifiers -> type -> A) q t :
  qual_norm' f q t =
    let p := decompose_type t in
    f (merge_tq p.1 q) p.2.
Proof.
  move: q. induction t=>q /=; try by rewrite left_id_L.
  rewrite decompose_type_unfold IHt /=.
  f_equal. rewrite assoc_L. f_equal. by rewrite comm_L.
Qed.

Lemma qual_norm_decompose_type {A} (f : type_qualifiers -> type -> A) t :
  qual_norm f t =
    let p := decompose_type t in
    f p.1 p.2.
Proof.
  rewrite /qual_norm qual_norm'_decompose_type. cbn.
  by rewrite right_id_L.
Qed.

(** Smart constructors *)

(**
Qualify a type, merging nested qualifiers, suppressing [QM]
qualifiers, and (https://www.eel.is/c++draft/dcl.ref#1) discarding any
cv-qualifiers on reference types.
*)
Definition tqualified : type_qualifiers -> type -> type :=
  qual_norm' $ fun q t =>
  match t with
  | Tref _ | Trv_ref _ => t
  | _ => match q with QM => t | _ => Tqualified q t end
  end.
#[global] Arguments tqualified _ !_ / : simpl nomatch, assert.

(**
[tref], [trv_ref] implement reference collapsing.

Background:
https://en.cppreference.com/w/cpp/language/reference#Reference_collapsing
https://www.eel.is/c++draft/dcl.ref#5
*)
Fixpoint tref (acc : type_qualifiers) (t : type) : type :=
  match t with
  | Tref t | Trv_ref t => tref QM t
  | Tqualified q t => tref (merge_tq q acc) t
  | _ => Tref (tqualified acc t)
  end.
#[global] Arguments tref _ !_ / : simpl nomatch, assert.

Fixpoint trv_ref (acc : type_qualifiers) (t : type) : type :=
  match t with
  | Tref t => tref QM t
  | Trv_ref t => trv_ref QM t
  | Tqualified q t => trv_ref (merge_tq q acc) t
  | _ => Trv_ref (tqualified acc t)
  end.
#[global] Arguments trv_ref _ !_ / : simpl nomatch, assert.

(** [IsRef] vs [NonRef] types *)

(**
[IsRef t] ([NonRef t]) means [t] is (is not) a reference type.
*)
Definition IsRef (t : type) : Prop := ∃ t', t = Tref t' \/ t = Trv_ref t'.
#[global] Arguments IsRef : simpl never.
#[global] Hint Opaque IsRef : typeclass_instances.

Definition NonRef (t : type) : Prop := ¬ IsRef t.
#[global] Arguments NonRef : simpl never.
#[global] Hint Opaque NonRef : typeclass_instances.

#[local] Definition is_refb (t : type) : bool :=
  if t is (Tref _ | Trv_ref _) then true else false.
#[local] Lemma IsRef_is_refb t : IsRef t <-> is_refb t.
Proof.
  split.
  - by intros (t' & [-> | ->]).
  - rewrite /IsRef. destruct t; first [done|naive_solver].
Qed.
#[local] Lemma NonRef_is_refb t : NonRef t <-> ¬ is_refb t.
Proof. by rewrite /NonRef IsRef_is_refb. Qed.

#[global] Instance IsRef_dec t : Decision (IsRef t).
Proof.
  refine (cast_if (decide (is_refb t)));
    abstract (by rewrite IsRef_is_refb).
Defined.

#[global] Instance NonRef_dec t : Decision (NonRef t).
Proof.
  refine (cast_if (decide (¬ is_refb t)));
    abstract (by rewrite NonRef_is_refb).
Defined.

Lemma ref_unqualified t : IsRef t -> Unqualified t.
Proof. intros (t' & [-> | ->]); apply _. Qed.

Lemma ref_nonref {t} : IsRef t -> NonRef t -> False.
Proof. rewrite /NonRef. auto. Qed.

Lemma ref_cases t : IsRef t \/ NonRef t.
Proof.
  rewrite /NonRef. destruct (decide (IsRef t)); auto.
Qed.

(**
Teach TC resolution to prove [IsRef t], [NonRef t] when [t] a
constructor.
*)

Existing Class IsRef.
#[global] Hint Mode IsRef ! : typeclass_instances.
#[global] Instance IsRef_instance t :
  TCEq (is_refb t) true -> IsRef t | 50.
Proof. by rewrite TCEq_eq IsRef_is_refb=>->. Qed.

Existing Class NonRef.
#[global] Hint Mode NonRef ! : typeclass_instances.
#[global] Instance NonRef_instance t :
  TCEq (is_refb t) false -> NonRef t | 50.
Proof. rewrite TCEq_eq NonRef_is_refb=>->. tauto. Qed.

(** [tqualified] *)

Lemma tqualified_unfold q t :
  tqualified q t =
    match t with
    | Tqualified q' t => tqualified (merge_tq q' q) t
    | Tref _ | Trv_ref _ => t
    | _ => match q with QM => t | _ => Tqualified q t end
    end.
Proof.
  rewrite {1}/tqualified qual_norm'_unfold -/tqualified.
  by destruct t.
Qed.

Lemma tqualified_prepost
    (Pre : type_qualifiers -> type -> Prop)
    (Post : type -> Prop) q t :
  Pre q t ->
  (∀ q q' t, Pre q (Tqualified q' t) -> Pre (merge_tq q' q) t) ->
  (∀ q t, Pre q t -> IsRef t -> Post t) ->
  (∀ q t, Pre q t -> Unqualified t -> NonRef t -> Post (if q is QM then t else Tqualified q t)) ->
  Post (tqualified q t).
Proof.
  intros. apply (qual_norm'_prepost Pre Post); [done..|]=>q' t'.
  destruct (ref_cases t') as [Hr|Hnr].
  - intros _ ?. move: (Hr). intros (t'' & [-> | ->]); by eauto.
  - destruct t'; first [by auto|by case: (ref_nonref _ Hnr)].
Qed.

(** [tref] *)

Lemma tref_unfold q t :
  tref q t =
    qual_norm' (fun q' t' =>
      match t' with
      | Tref t'' | Trv_ref t'' => tref QM t''
      | _ => Tref (tqualified q' t')
      end
    ) q t.
Proof. move: q. by induction t; cbn. Qed.

Lemma tref_prepost
    (Pre : type_qualifiers -> type -> Prop)
    (Post : type -> Prop) q t :
  Pre q t ->
  (∀ q q' t, Pre q (Tqualified q' t) -> Pre (merge_tq q' q) t) ->
  (∀ q t, Pre q (Tref t) -> Pre QM t) ->
  (∀ q t, Pre q (Trv_ref t) -> Pre QM t) ->
  (∀ q t, Pre q t -> Unqualified t -> NonRef t -> Post $ Tref $ tqualified q t) ->
  Post (tref q t).
Proof.
  intros Hpre Hq Hl Hr Hret.
  move: q Hpre. induction t=>q Hpre; cbn; first [exact: Hret|eauto].
Qed.

(** [trv_ref] *)

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

Lemma trv_ref_prepost
    (Pre : type_qualifiers -> type -> Prop)
    (Post : type -> Prop) q t :
  Pre q t ->
  (∀ q q' t, Pre q (Tqualified q' t) -> Pre (merge_tq q' q) t) ->
  (∀ q t, Pre q (Trv_ref t) -> Pre QM t) ->
  (∀ q t, Pre q (Tref t) -> Post (tref QM t)) ->
  (∀ q t, Pre q t -> Unqualified t -> NonRef t -> Post $ Trv_ref $ tqualified q t) ->
  Post (trv_ref q t).
Proof.
  intros Hpre ??? Hret.
  move: q Hpre. induction t=>q ?; cbn; first [exact: Hret|eauto].
Qed.

(**
normalization of types
- compresses adjacent [Tqualified] constructors
- drops (irrelevant) qualifiers on function arguments and return types
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
    Tfunction (cc:=cc) (ar:=ar) (drop_norm r) (List.map drop_norm args)
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
      - rewrite map_map /qual_norm !IHty /merge_tq/=;
          erewrite map_ext_Forall; eauto; eapply Forall_impl;
          [|eassumption]; intros * HForall; simpl in HForall; apply HForall.
      - rewrite IHty !assoc_L. f_equal. f_equal. by rewrite comm_L.
    }
    { (* _qual_norm_involutive *)
      intros *; generalize dependent q;
        induction ty using type_ind'; intros *; simpl;
        try solve[destruct q; simpl; now rewrite ?normalize_type_idempotent].
      destruct q; simpl;
        rewrite map_map /qual_norm ?_drop_norm_idempotent /merge_tq/=;
        try solve[erewrite map_ext_Forall; eauto; induction tys;
                  [ now constructor
                  | constructor;
                    [ now apply _drop_norm_idempotent
                    | apply IHtys; now apply Forall_inv_tail in H]]].
    }
    { (* normalize_type_involutive *)
      intros *; induction ty using type_ind'; simpl; rewrite ?IHty; eauto.
      rewrite map_map /qual_norm _drop_norm_idempotent /merge_tq/=.
      erewrite map_ext_Forall; eauto; induction tys;
        [ now constructor
        | constructor;
          [ now apply _drop_norm_idempotent
          | apply IHtys; now apply Forall_inv_tail in H]].
    }
  Qed.
End normalize_type_idempotent.

Lemma normalize_type_qual_norm t :
  normalize_type t = qual_norm (fun q t' => tqualified q (normalize_type t')) t.
Proof. rewrite qual_norm_unfold. by destruct t. Qed.

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
