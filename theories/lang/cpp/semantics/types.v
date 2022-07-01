(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import base.
From bedrock.lang.cpp.syntax Require Import names expr stmt types typing.
From bedrock.lang.cpp.semantics Require Import genv.


Definition GlobDecl_size_of (g : GlobDecl) : option N :=
  match g with
  | Gstruct s => Some s.(s_size)
  | Gunion u => Some u.(u_size)
  | _ => None
  end.
Definition GlobDecl_align_of (g : GlobDecl) : option N :=
  match g with
  | Gstruct s => Some s.(s_alignment)
  | Gunion u => Some u.(u_alignment)
  | _ => None
  end.
Variant Roption_leq {T} (R : T -> T -> Prop) : option T -> option T -> Prop :=
| Rleq_None {x} : Roption_leq R None x
| Rleq_Some {x y} (_ : R x y) : Roption_leq R (Some x) (Some y).


#[global] Instance proper_GlobDecl_size_of: Proper (GlobDecl_ler ==> Roption_leq eq) GlobDecl_size_of.
Proof.
  rewrite /GlobDecl_size_of => x y Heq.
  repeat (case_match; try constructor);
    simplify_eq/= => //;
    apply require_eq_success in Heq; naive_solver.
Qed.
#[global] Instance proper_GlobDecl_align_of: Proper (GlobDecl_ler ==> Roption_leq eq) GlobDecl_align_of.
Proof.
  rewrite /GlobDecl_align_of => x y Heq.
  repeat (case_match; try constructor);
    simplify_eq/= => //;
    apply require_eq_success in Heq; naive_solver.
Qed.

(** * sizeof() *)
(** this is a partial implementation of [size_of], it doesn't indirect through
    typedefs, but the cpp2v generator flattens these for us anyways.
 *)
Fixpoint size_of (resolve : genv) (t : type) : option N :=
  match t with
  | Tpointer _ => Some (pointer_size resolve)
  | Tref _ => None
  | Trv_ref _ => None
  | Tnum sz _ => Some (bytesN sz)
  | Tvoid => None
  | Tarray t n => N.mul n <$> size_of resolve t
  | Tnamed nm => glob_def resolve nm ≫= GlobDecl_size_of
  | Tfunction _ _ => None
  | Tbool => Some 1
  | Tmember_pointer _ _ => None (* TODO these are not well supported right now *)
  | Tqualified _ t => size_of resolve t
  | Tnullptr => Some (pointer_size resolve)
  | Tfloat sz => Some (bytesN sz)
  | Tarch sz _ => bytesN <$> sz
  end%N.

#[global] Instance Proper_size_of
  : Proper (genv_leq ==> eq ==> Roption_leq eq) (@size_of).
Proof.
  intros ?? Hle ? t ->; induction t; simpl; (try constructor) => //.
  all: try exact: pointer_size_proper.
  - by destruct IHt; constructor; subst.
  - move: Hle => [[ /(_ g) Hle _] _ _].
    unfold glob_def. rewrite -tu_lookup_globals in Hle.
    destruct ((genv_tu x) !! g) as [g1| ]; last constructor.
    move: Hle => /(_ _ eq_refl). rewrite -tu_lookup_globals.
    move => [g2 [-> HH]] /=.
    exact: proper_GlobDecl_size_of.
  - by destruct o; constructor.
Qed.


Theorem size_of_int : forall {c : genv} s w,
    @size_of c (Tnum w s) = Some (bytesN w).
Proof. reflexivity. Qed.
Theorem size_of_char : forall {c : genv} s w,
    @size_of c (Tchar w s) = Some (bytesN w).
Proof. reflexivity. Qed.
Theorem size_of_bool : forall {c : genv},
    @size_of c Tbool = Some 1%N.
Proof. reflexivity. Qed.
Theorem size_of_pointer : forall {c : genv} t,
    @size_of c (Tpointer t) = Some (pointer_size c).
Proof. reflexivity. Qed.
Theorem size_of_qualified : forall {c : genv} t q,
    @size_of c t = @size_of c (Tqualified q t).
Proof. reflexivity. Qed.
Theorem size_of_array_0 : forall {c : genv} t sz,
    @size_of c t = Some sz ->
    @size_of c (Tarray t 0) = Some 0%N.
Proof. intros; simpl. by rewrite H. Qed.

Theorem size_of_array_pos : forall {c : genv} t n sz,
    (0 < n)%N ->
    @size_of c t = Some sz <-> @size_of c (Tarray t n) = Some (n * sz)%N.
Proof.
  simpl. intros. destruct (size_of c t) => /=; split; try congruence.
  inversion 1. f_equal. apply N.mul_cancel_l in H2.  auto. lia.
Qed.

Theorem size_of_array : forall {c : genv} t n sz,
    @size_of c t = Some sz -> @size_of c (Tarray t n) = Some (n * sz)%N.
Proof.
  simpl. intros. destruct (size_of c t) => /=; try congruence.
Qed.

Lemma size_of_Qmut : forall {c} t,
    @size_of c t = @size_of c (Qmut t).
Proof. reflexivity. Qed.

Lemma size_of_Qconst : forall {c} t ,
    @size_of c t = @size_of c (Qconst t).
Proof. reflexivity. Qed.

(* XXX: since size_of simplifies eagerly, this might be hard to apply, so you
might need to inline the proof. *)
Lemma size_of_genv_compat tu σ gn st
      (Hσ : tu ⊧ σ)
      (Hl : tu !! gn = Some (Gstruct st)) :
  size_of σ (Tnamed gn) = GlobDecl_size_of (Gstruct st).
Proof. by rewrite /= (glob_def_genv_compat_struct st Hl). Qed.

(** [SizeOf ty n] means that C++ type [ty] has size [n] bytes *)
Class SizeOf {σ : genv} (ty : type) (n : N) : Prop :=
  size_of_spec : size_of σ ty = Some n.
#[global] Hint Mode SizeOf - + - : typeclass_instances.

#[global] Instance SizeOf_mono :
  Proper (genv_leq ==> eq ==> eq ==> impl) (@SizeOf).
Proof.
  rewrite /SizeOf=>σ1 σ2 Hσ t1 t2 Ht n ? <- ?.
  by destruct (Proper_size_of _ _ Hσ _ _ Ht); simplify_eq.
Qed.

#[global] Instance array_size_of {σ : genv} ty a n b :
  SizeOf ty a ->
  TCEq (n * a)%N b ->
  SizeOf (Tarray ty n) b.
Proof.
  rewrite /SizeOf TCEq_eq=>Hty <-.
  cbn. by rewrite Hty.
Qed.

#[global] Instance named_struct_size_of tu σ gn st n :
  genv_compat tu σ ->
  TCEq (tu !! gn) (Some (Gstruct st)) ->
  TCEq st.(s_size) n ->
  SizeOf (Tnamed gn) n.
Proof.
  rewrite /SizeOf !TCEq_eq=>? /glob_def_genv_compat_struct Htu <-.
  cbn. by rewrite Htu.
Qed.

#[global] Instance named_union_size_of tu σ gn u n :
  genv_compat tu σ ->
  TCEq (tu !! gn) (Some (Gunion u)) ->
  TCEq u.(u_size) n ->
  SizeOf (Tnamed gn) n.
Proof.
  rewrite /SizeOf !TCEq_eq=>? /glob_def_genv_compat_union Htu <-.
  cbn. by rewrite Htu.
Qed.

#[global] Instance bool_size_of {σ : genv} : SizeOf Tbool 1.
Proof. done. Qed.

#[global] Instance int_size_of {σ : genv} sz sgn n :
  TCEq (bytesN sz) n -> SizeOf (Tnum sz sgn) n.
Proof. by rewrite /SizeOf TCEq_eq=><-. Qed.

#[global] Instance qualified_size_of {σ : genv} qual ty n :
  SizeOf ty n -> SizeOf (Tqualified qual ty) n.
Proof. done. Qed.

#[global] Instance ptr_size_of {σ : genv} ty n :
  TCEq (pointer_size σ) n -> SizeOf (Tptr ty) n.
Proof. by rewrite /SizeOf TCEq_eq=><-. Qed.

#[global] Instance arch_size_of {σ : genv} sz name n :
  TCEq (bytesN sz) n -> SizeOf (Tarch (Some sz) name) n.
Proof. by rewrite /SizeOf TCEq_eq=><-. Qed.

(** [HasSize ty] means that C++ type [ty] has a defined size *)
Class HasSize {σ : genv} (ty : type) : Prop :=
  has_size : is_Some (size_of σ ty).
#[global] Hint Mode HasSize - + : typeclass_instances.
#[global] Arguments has_size {_} _ {_} : assert.

#[global] Instance HasSize_mono :
  Proper (genv_leq ==> eq ==> impl) (@HasSize).
Proof.
  rewrite /HasSize=>σ1 σ2 Hσ t1 t2 Ht H.
  destruct (Proper_size_of _ _ Hσ _ _ Ht).
  - exfalso. exact: is_Some_None.
  - by simplify_eq.
Qed.

#[global] Instance size_of_has_size {σ : genv} ty n :
  SizeOf ty n -> HasSize ty.
Proof.
  intros. rewrite /HasSize size_of_spec. by eexists.
Qed.

(** [sizeof ty : N] is the size of C++ type [ty] (if it has a size) *)
Definition sizeof {σ : genv} (ty : type) `{!HasSize ty} : N :=
  is_Some_proj (has_size ty).

Lemma sizeof_spec {σ : genv} ty `{Hsz : !HasSize ty} :
  size_of σ ty = Some (sizeof ty).
Proof.
  rewrite/sizeof/has_size. by destruct Hsz as [sz ->].
Qed.

(** [offset_of] *)

Fixpoint find_assoc_list {T} (f : ident) (fs : list (ident * T)) : option T :=
  match fs with
  | nil => None
  | (f',v) :: fs =>
    if decide (f = f') then
      Some v
    else find_assoc_list f fs
  end%list.

Lemma find_assoc_list_elem_of {T} base xs :
  (∃ v, (base, v) ∈ xs) ->
  ∃ y, find_assoc_list (T := T) base xs = Some y.
Proof.
  move=>[v]. elim: xs => /= [/elem_of_nil //|[k w] xs IH]
    /elem_of_cons [|] Hin; simplify_eq.
  { rewrite decide_True; eauto. }
  case_decide; eauto.
Qed.

#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.
(* note: we expose the fact that reference fields are compiled to pointers,
   so the [offset_of] a reference field is the offset of the pointer.
 *)
Definition offset_of (resolve : genv) (t : globname) (f : ident) : option Z :=
  match glob_def resolve t with
  | Some (Gstruct s) =>
    find_assoc_list f (List.map (fun m => (m.(mem_name),m.(mem_layout).(li_offset) / 8)) s.(s_fields))
  | Some (Gunion u) =>
    find_assoc_list f (List.map (fun m => (m.(mem_name),m.(mem_layout).(li_offset) / 8)) u.(u_fields))
  | _ => None
  end.

Definition parent_offset_tu (tu : translation_unit) (derived : globname) (base : globname) : option Z :=
  match tu !! derived with
  | Some (Gstruct s) => find_assoc_list base (List.map (fun '(s,l) => (s,l.(li_offset) / 8)) s.(s_bases))
  | _ => None
  end.
Notation parent_offset σ derived base := (parent_offset_tu σ.(genv_tu) derived base).
Notation directly_derives_tu tu derived base := (is_Some (parent_offset_tu tu derived base)).
Notation directly_derives σ derived base := (is_Some (parent_offset σ derived base)).

Lemma find_assoc_list_parent_offset tu derived st base li :
  tu !! derived = Some (Gstruct st) ->
  (base, li) ∈ st.(s_bases) ->
  ∃ z, parent_offset_tu tu derived base = Some z.
Proof.
  rewrite /parent_offset_tu => -> Hin.
  apply /find_assoc_list_elem_of.
  eexists; apply /elem_of_list_fmap; by exists (base, li).
Qed.

Lemma parent_offset_genv_compat {σ tu derived base z} {Hσ : tu ⊧ σ} :
  parent_offset_tu tu derived base = Some z ->
  parent_offset σ derived base = Some z.
Proof.
  rewrite /parent_offset_tu -/(glob_def σ derived).
  case E: (tu !! derived) => [ gd //= | // ]; destruct gd => //.
  by erewrite glob_def_genv_compat_struct.
Qed.

(** * alignof() *)
Parameter align_of : forall {resolve : genv} (t : type), option N.
Axiom align_of_named : ∀ {σ : genv} (nm : globname),
  align_of (Tnamed nm) =
  glob_def σ nm ≫= GlobDecl_align_of.

(** If [size_of] is defined, [align_of] must divide [size_of]. *)
Axiom align_of_size_of' : forall {σ : genv} (t : type) sz,
    size_of σ t = Some sz ->
    (exists al, align_of t = Some al /\ al <> 0 /\ (al | sz))%N.

Lemma align_of_size_of {σ : genv} (t : type) sz :
    size_of σ t = Some sz ->
    exists al, align_of t = Some al /\
          (* size is a multiple of alignment *)
          (sz mod al = 0)%N.
Proof.
  move=>/align_of_size_of' [al [? [? /N.mod_divide ?]]].
  eauto.
Qed.

Axiom align_of_array : forall {σ : genv} (ty : type) n,
    align_of (Tarray ty n) = align_of ty.
Axiom align_of_qualified : ∀ σ t q,
    align_of (resolve:=σ) (Tqualified q t) = align_of (resolve:=σ) t.

Axiom Proper_align_of : Proper (genv_leq ==> eq ==> Roption_leq eq) (@align_of).
#[global] Existing Instance Proper_align_of.

Lemma align_of_genv_compat tu σ gn st
      (Hσ : tu ⊧ σ)
      (Hl : tu !! gn = Some (Gstruct st)) :
  align_of (Tnamed gn) = GlobDecl_align_of (Gstruct st).
Proof. by rewrite /= align_of_named (glob_def_genv_compat_struct st Hl). Qed.


(** [vararg_promote t] returns the type that [t] is promoted to when
    passed as a variadic function argument.

    See: https://eel.is/c++draft/expr.call#12
 *)
Definition vararg_promote (t : type) : option type :=
  match erase_qualifiers t with
  | Tnullptr => Some $ Tptr Tvoid
  (* integral promotions *)
  | Tnum W8 s | Tnum W16 s | Tnum W32 s => Some $ Tnum W32 s
  | Tnum W64 s => Some $ Tnum W64 s
  (* floating point promotions *)
  | Tfloat _ => Some $ Tfloat W64
  (* pointers and member pointers are not changed *)
  | Tptr _ as t
  | Tmember_pointer _ _ as t => Some t
  (* aggregates are conditionally supported if they have a
     corresponding copy-constructor this is handled in the
     logic *)
  | Tnamed _ as t => Some t
  | _ => None
  end.
