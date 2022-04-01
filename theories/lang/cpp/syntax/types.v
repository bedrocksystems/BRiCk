(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Export bedrock.lang.cpp.arith.types.
Require Import bedrock.lang.cpp.syntax.names.

Set Primitive Projections.

(* Type qualifiers *)
Record type_qualifiers : Set :=
{ q_const : bool
; q_volatile : bool }.
#[global] Instance qual_eq: EqDecision type_qualifiers.
Proof. solve_decision. Defined.
#[global] Instance qual_countable : Countable type_qualifiers.
Proof.
  apply (inj_countable'
    (λ q, (q_const q, q_volatile q))
    (λ q, {| q_const := q.1; q_volatile := q.2 |})).
  abstract (by intros []).
Defined.

Definition merge_tq (a b : type_qualifiers) : type_qualifiers :=
  {| q_const := a.(q_const) || b.(q_const)
   ; q_volatile := a.(q_volatile) || b.(q_volatile)
   |}.

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
#[global] Instance calling_conv_inhabited : Inhabited calling_conv := populate CC_C.
#[global] Instance calling_conv_eq_dec: EqDecision calling_conv.
Proof. solve_decision. Defined.
#[global] Instance calling_conv_countable : Countable calling_conv.
Proof.
  apply (inj_countable'
    (λ cc,
      match cc with
      | CC_C => 0 | CC_MsAbi => 1 | CC_RegCall => 2
      end)
    (λ n,
      match n with
      | 0 => CC_C | 1 => CC_MsAbi | 2 => CC_RegCall
      | _ => CC_C	(** dummy *)
      end)).
  abstract (by intros []).
Defined.

(* in almost all contexts, we are going to use [CC_C], so we're going to make
   that the default. Clients interested in specifying another calling convention
   should write, e.g., [Tfunction (cc:=CC_PreserveAll) ..] to specify the
   calling convention explicitly.
 *)
Existing Class calling_conv.
#[global] Existing Instance CC_C.

(* types *)
Inductive type : Set :=
| Tptr (_ : type)
| Tref (_ : type)
| Trv_ref (_ : type)
| Tnum (size : bitsize) (signed : signed)
| Tvoid
| Tarray (_ : type) (_ : N) (* unknown sizes are represented by pointers *)
| Tnamed (_ : globname)
| Tfunction {cc : calling_conv} (_ : type) (_ : list type)
| Tbool
| Tmember_pointer (_ : globname) (_ : type)
| Tfloat (_ : bitsize)
| Tqualified (_ : type_qualifiers) (_ : type)
| Tnullptr
(* architecture-specific types; currently unused.
   some Tarch types, like ARM SVE, are "sizeless", hence [option size]. *)
| Tarch (_ : option bitsize) (name : bs)
.
#[global] Instance type_inhabited : Inhabited type := populate Tvoid.

Notation Tchar := Tnum (only parsing).

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
  Hypothesis Tvoid_ind' : P Tvoid.
  Hypothesis Tarray_ind' : forall (ty : type) (sz : N),
    P ty -> P (Tarray ty sz).
  Hypothesis Tnamed_ind' : forall (name : globname),
    P (Tnamed name).
  Hypothesis Tfunction_ind' : forall {cc : calling_conv} (ty : type) (tys : list type),
    P ty -> Forall P tys -> P (Tfunction ty tys).
  Hypothesis Tbool_ind' : P Tbool.
  Hypothesis Tmember_pointer_ind' : forall (name : globname) (ty : type),
    P ty -> P (Tmember_pointer name ty).
  Hypothesis Tfloat_ind' : forall (size : bitsize),
    P (Tfloat size).
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
    | Tvoid                   => Tvoid_ind'
    | Tarray ty sz            => Tarray_ind' ty sz (type_ind' ty)
    | Tnamed name             => Tnamed_ind' name
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
    | Tfloat sz               => Tfloat_ind' sz
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
  #[local] Notation BS x      := (GenLeaf (inr x)).
  #[local] Notation QUAL x    := (GenLeaf (inl (inr x))).
  #[local] Notation BITSIZE x := (GenLeaf (inl (inl (inr x)))).
  #[local] Notation SIGNED x  := (GenLeaf (inl (inl (inl (inr x))))).
  #[local] Notation CC x      := (GenLeaf (inl (inl (inl (inl (inr x)))))).
  #[local] Notation N x       := (GenLeaf (inl (inl (inl (inl (inl x)))))).
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
      | @Tfunction cc ret args => GenNode 7 $ (CC cc) :: go ret :: (go <$> args)
      | Tbool => GenNode 8 []
      | Tmember_pointer gn t => GenNode 9 [BS gn; go t]
      | Tfloat sz => GenNode 10 [BITSIZE sz]
      | Tqualified q t => GenNode 11 [QUAL q; go t]
      | Tnullptr => GenNode 12 []
      | Tarch None gn => GenNode 13 [BS gn]
      | Tarch (Some sz) gn => GenNode 14 [BITSIZE sz; BS gn]
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
      | GenNode 7 (CC cc :: ret :: args) => @Tfunction cc (go ret) (go <$> args)
      | GenNode 8 [] => Tbool
      | GenNode 9 [BS gn; t] => Tmember_pointer gn (go t)
      | GenNode 10 [BITSIZE sz] => Tfloat sz
      | GenNode 11 [QUAL q; t] => Tqualified q (go t)
      | GenNode 12 [] => Tnullptr
      | GenNode 13 [BS gn] => Tarch None gn
      | GenNode 14 [BITSIZE sz; BS gn] => Tarch (Some sz) gn
      | _ => Tvoid	(** dummy *)
      end.
    apply (inj_countable' enc dec). refine (fix go t := _).
    destruct t as [| | | | | | |cc ret args| | | | | |[]]; simpl; f_equal; try done.
    induction args; simpl; f_equal; done.
  Defined.
End type_countable.

Notation Tpointer := Tptr (only parsing).
Notation Treference := Tref (only parsing).
Notation Trv_reference := Trv_ref (only parsing).
Notation Tfun := Tfunction (only parsing).
Definition QCV := {| q_const := true ; q_volatile := true |}.
Definition QC := {| q_const := true ; q_volatile := false |}.
Definition QV := {| q_const := false ; q_volatile := true |}.
Definition QM := {| q_const := false ; q_volatile := false |}.

Definition Qconst_volatile : type -> type :=
  Tqualified QCV.
Definition Qconst : type -> type :=
  Tqualified QC.
Definition Qmut_volatile : type -> type :=
  Tqualified QV.
Definition Qmut : type -> type :=
  Tqualified QM.

Section qual_norm.
  Context {A : Type}.
  Variable f : type_qualifiers -> type -> A.

  Fixpoint qual_norm' (q : type_qualifiers) (t : type) : A :=
    match t with
    | Tqualified q' t =>
      qual_norm' (merge_tq q q') t
    | _ =>
      f q t
    end.

  Definition qual_norm : type -> A :=
    qual_norm' {| q_const := false ; q_volatile := false |}.

End qual_norm.

Definition tqualified (q : type_qualifiers) (t : type) : type :=
  match q with
  | {| q_const := false ; q_volatile := false |} => t
  | _ => Tqualified q t
  end.


(** normalization of types
    - compresses adjacent [Tqualified] constructors
    - drops (irrelevant) qualifiers on function arguments and return types
 *)
Fixpoint normalize_type (t : type) : type :=
  let drop_norm :=
      qual_norm (fun _ t => normalize_type t)
  in
  let qual_norm :=
      (* merge adjacent qualifiers and then normalize *)
      qual_norm' (fun q t => tqualified q (normalize_type t))
  in
  match t with
  | Tpointer t => Tpointer (normalize_type t)
  | Tref t => Tref (normalize_type t)
  | Trv_ref t => Trv_ref (normalize_type t)
  | Tarray t n => Tarray (normalize_type t) n
  | @Tfunction cc r args =>
    Tfunction (cc:=cc) (drop_norm r) (List.map drop_norm args)
  | Tmember_pointer gn t => Tmember_pointer gn (normalize_type t)
  | Tqualified q t => qual_norm q t
  | Tnum _ _ => t
  | Tbool => t
  | Tvoid => t
  | Tnamed _ => t
  | Tnullptr => t
  | Tfloat _ => t
  | Tarch _ _ => t
  end.

Section normalize_type_idempotent.
  Lemma merge_tq_assoc:
    forall q q' q'',
      merge_tq q (merge_tq q' q'') = merge_tq (merge_tq q q') q''.
  Proof. now intros *; rewrite /merge_tq/= !orb_assoc. Qed.

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
          erewrite map_ext_Forall; eauto; eapply Forall_impl; eauto;
          intros * HForall; simpl in HForall; apply HForall.
      - now rewrite IHty merge_tq_assoc.
    }
    { (* _qual_norm_involutive *)
      intros *; generalize dependent q;
        induction ty using type_ind'; intros *; simpl;
        try solve[destruct q as [[|] [|]]; simpl; now rewrite ?normalize_type_idempotent].
      destruct q as [[|] [|]]; simpl;
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

Definition decompose_type : type -> type_qualifiers * type :=
  qual_norm (fun q t => (q, t)).


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
*)
Notation char_bits :=  (W8)  (only parsing).
Notation short_bits := (W16) (only parsing).
Notation int_bits :=   (W32) (only parsing).

(** warning: LLP64 model uses [long_bits := W32] *)
Notation long_bits :=      (W64) (only parsing).
Notation long_long_bits := (W64) (only parsing).

(** ** Types with implicit size information. *)

Notation Tschar  := Ti8 (only parsing).
Notation Tuchar  := Tu8 (only parsing).

Notation Tushort := (Tnum short_bits Unsigned) (only parsing).
Notation Tshort := (Tnum short_bits Signed) (only parsing).

(** XXX This is the odd-name out, but [Tnum] is taken. *)
(* #[deprecated(since="2022-04-1", note="use [Ti32]")] *)
Notation T_int := (Tnum int_bits Signed) (only parsing).
Notation Tuint := (Tnum int_bits Unsigned) (only parsing).

Notation Tulong := (Tnum long_bits Unsigned) (only parsing).
Notation Tlong := (Tnum long_bits Signed) (only parsing).

Notation Tulonglong := (Tnum long_long_bits Unsigned) (only parsing).
Notation Tlonglong := (Tnum long_long_bits Signed) (only parsing).
