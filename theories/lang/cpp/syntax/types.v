(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.prelude.base.
Require Import bedrock.lang.cpp.syntax.names.

Set Primitive Projections.

(* Type qualifiers *)
Record type_qualifiers : Set :=
{ q_const : bool
; q_volatile : bool }.
Instance qual_eq: EqDecision type_qualifiers.
Proof. solve_decision. Defined.
Instance qual_countable : Countable type_qualifiers.
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

(* Bit-widths *)
Variant bitsize : Set :=
| W8
| W16
| W32
| W64
| W128.
Instance bitsize_eq: EqDecision bitsize.
Proof. solve_decision. Defined.
Instance bitsize_countable : Countable bitsize.
Proof.
  apply (inj_countable'
    (λ b,
      match b with
      | W8 => 0 | W16 => 1 | W32 => 2 | W64 => 3 | W128 => 4
      end)
    (λ n,
      match n with
      | 0 => W8 | 1 => W16 | 2 => W32 | 3 => W64 | 4 => W128
      | _ => W8	(* dummy *)
      end)).
  abstract (by intros []).
Defined.

Definition bitsN (s : bitsize) : N :=
  match s with
  | W8   => 8
  | W16  => 16
  | W32  => 32
  | W64  => 64
  | W128 => 128
  end.

Definition bitsZ (s : bitsize) : Z :=
  Z.of_N (bitsN s).

Definition bytesNat (s : bitsize) : nat :=
  match s with
  | W8 => 1
  | W16 => 2
  | W32 => 4
  | W64 => 8
  | W128 => 16
  end.

Definition bytesN (s : bitsize) : N :=
  N.of_nat (bytesNat s).

Definition bytesZ (s : bitsize) : Z :=
  Z.of_N (bytesN s).

Bind Scope N_scope with bitsize.

Lemma of_size_gt_O w :
  (0 < 2 ^ bitsZ w)%Z.
Proof. destruct w; reflexivity. Qed.
(* Hint Resolve of_size_gt_O. *)

(* Signed and Unsigned *)
Variant signed : Set := Signed | Unsigned.
Instance signed_eq_dec: EqDecision signed.
Proof. solve_decision. Defined.
Instance signed_countable : Countable signed.
Proof.
  apply (inj_countable'
    (λ s, if s is Signed then true else false)
    (λ b, if b then Signed else Unsigned)).
  abstract (by intros []).
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
Instance calling_conv_eq_dec: EqDecision calling_conv.
Proof. solve_decision. Defined.
Instance calling_conv_countable : Countable calling_conv.
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
Existing Instance CC_C.

(* types *)
Inductive type : Set :=
| Tptr (_ : type)
| Tref (_ : type)
| Trv_ref (_ : type)
| Tint (size : bitsize) (signed : signed)
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
  Hypothesis Tint_ind' : forall (size : bitsize) (sign : signed),
    P (Tint size sign).
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
    | Tint sz sgn             => Tint_ind' sz sgn
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

Notation Tchar := Tint (only parsing).
(* XXX merge type_eq_dec into type_eq. *)
Definition type_eq_dec : forall (ty1 ty2 : type), { ty1 = ty2 } + { ty1 <> ty2 }.
Proof.
  (* rewrite /RelDecision /Decision. *)
  fix IHty1 1.
  rewrite -{1}/(EqDecision type) in IHty1.
  decide equality; try solve_trivial_decision.
Defined.
Instance type_eq: EqDecision type := type_eq_dec.
Section type_countable.
  Local Notation BS x      := (GenLeaf (inr x)).
  Local Notation QUAL x    := (GenLeaf (inl (inr x))).
  Local Notation BITSIZE x := (GenLeaf (inl (inl (inr x)))).
  Local Notation SIGNED x  := (GenLeaf (inl (inl (inl (inr x))))).
  Local Notation CC x      := (GenLeaf (inl (inl (inl (inl (inr x)))))).
  Local Notation N x       := (GenLeaf (inl (inl (inl (inl (inl x)))))).
  Global Instance type_countable : Countable type.
  Proof.
    set enc := fix go (t : type) :=
      match t with
      | Tptr t => GenNode 0 [go t]
      | Tref t => GenNode 1 [go t]
      | Trv_ref t => GenNode 2 [go t]
      | Tint sz sgn => GenNode 3 [BITSIZE sz; SIGNED sgn]
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
      | GenNode 3 [BITSIZE sz; SIGNED sgn] => Tint sz sgn
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

Variant PrimCast : Set :=
| Cdependent (* this doesn't have any semantics *)
| Cbitcast
| Clvaluebitcast
| Cl2r
| Cnoop
| Carray2pointer
| Cfunction2pointer
| Cint2pointer
| Cpointer2int
| Cptr2bool
| Cderived2base
| Cbase2derived
| Cintegral
| Cint2bool
| Cnull2ptr
| Cbuiltin2function
| Cconstructorconversion
| C2void.
Instance PrimCast_eq: EqDecision PrimCast.
Proof. solve_decision. Defined.

Variant Cast : Set :=
| CCcast       (_ : PrimCast)
| Cuser        (conversion_function : obj_name)
| Creinterpret (_ : type)
| Cstatic      (from to : globname)
| Cdynamic     (from to : globname)
| Cconst       (_ : type).
Instance Case_eq: EqDecision Cast.
Proof. solve_decision. Defined.


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
  | Treference t => Treference (normalize_type t)
  | Trv_reference t => Trv_reference (normalize_type t)
  | Tarray t n => Tarray (normalize_type t) n
  | @Tfunction cc r args =>
    Tfunction (cc:=cc) (drop_norm r) (List.map drop_norm args)
  | Tmember_pointer gn t => Tmember_pointer gn (normalize_type t)
  | Tqualified q t => qual_norm q t
  | Tint _ _ => t
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


(* types with explicit size information
 *)
Definition T_int8    := Tint W8 Signed.
Definition T_uint8   := Tint W8 Unsigned.
Definition T_int16   := Tint W16 Signed.
Definition T_uint16  := Tint W16 Unsigned.
Definition T_int32   := Tint W32 Signed.
Definition T_uint32  := Tint W32 Unsigned.
Definition T_int64   := Tint W64 Signed.
Definition T_uint64  := Tint W64 Unsigned.
Definition T_int128  := Tint W128 Signed.
Definition T_uint128 := Tint W128 Unsigned.

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
Definition char_bits : bitsize := W8.
Definition short_bits : bitsize := W16.
Definition int_bits : bitsize := W32.
Definition long_bits : bitsize := W64. (** warning: LLP64 model uses 32 *)
Definition long_long_bits : bitsize := W64.

Definition T_ushort : type := Tint short_bits Unsigned.
Definition T_short : type := Tint short_bits Signed.
Definition T_ulong : type := Tint long_bits Unsigned.
Definition T_long : type := Tint long_bits Signed.
Definition T_ulonglong : type := Tint long_long_bits Unsigned.
Definition T_longlong : type := Tint long_long_bits Signed.
Definition T_uint : type := Tint int_bits Unsigned.
Definition T_int : type := Tint int_bits Signed.

Notation T_schar := (Tchar char_bits Signed) (only parsing).
Notation T_uchar := (Tchar char_bits Unsigned) (only parsing).


Coercion CCcast : PrimCast >-> Cast.
