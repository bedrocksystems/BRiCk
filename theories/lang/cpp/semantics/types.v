(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import base.
From bedrock.lang.cpp.syntax Require Import names expr stmt types.
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


Instance proper_GlobDecl_size_of: Proper (GlobDecl_ler ==> Roption_leq eq) GlobDecl_size_of.
Proof.
  rewrite /GlobDecl_size_of => x y Heq.
  repeat (case_match; try constructor);
    simplify_eq/= => //;
    apply require_eq_success in Heq; naive_solver.
Qed.
Instance proper_GlobDecl_align_of: Proper (GlobDecl_ler ==> Roption_leq eq) GlobDecl_align_of.
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
  | Treference _ => None
  | Trv_reference _ => None
  | Tint sz _ => Some (bytesN sz)
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

Global Instance Proper_size_of
: Proper (genv_leq ==> eq ==> Roption_leq eq) (@size_of).
Proof.
  intros ?? Hle ? t ->; induction t; simpl; (try constructor) => //.
  all: try exact: pointer_size_proper.
  - by destruct IHt; constructor; subst.
  - move: Hle => [[ /(_ g) Hle _] _ _].
    unfold glob_def, globals in *.
    destruct (globals (genv_tu x) !! g) as [g1| ]; last constructor.
    move: Hle => /(_ _ eq_refl) [g2 [-> HH]] /=.
    exact: proper_GlobDecl_size_of.
  - by destruct o; constructor.
Qed.


Theorem size_of_int : forall {c : genv} s w,
    @size_of c (Tint w s) = Some (bytesN w).
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
  (Hl : tu.(globals) !! gn = Some (Gstruct st)) :
  size_of σ (Tnamed gn) = GlobDecl_size_of (Gstruct st).
Proof. by rewrite /= (glob_def_genv_compat_struct st Hl). Qed.

Fixpoint find_field {T} (f : ident) (fs : list (ident * T)) : option T :=
  match fs with
  | nil => None
  | (f',v) :: fs =>
    if decide (f = f') then
      Some v
    else find_field f fs
  end%list.

Local Close Scope nat_scope.
Local Open Scope Z_scope.
(* note: we expose the fact that reference fields are compiled to pointers,
   so the [offset_of] a reference field is the offset of the pointer.
 *)
Definition offset_of (resolve : genv) (t : globname) (f : ident) : option Z :=
  match glob_def resolve t with
  | Some (Gstruct s) =>
    find_field f (List.map (fun m => (m.(mem_name),m.(mem_layout).(li_offset) / 8)) s.(s_fields))
  | Some (Gunion u) =>
    find_field f (List.map (fun m => (m.(mem_name),m.(mem_layout).(li_offset) / 8)) u.(u_fields))
  | _ => None
  end.

Definition parent_offset (resolve : genv) (t : globname) (f : globname) : option Z :=
  match glob_def resolve t with
  | Some (Gstruct s) => find_field f (List.map (fun '(s,l) => (s,l.(li_offset) / 8)) s.(s_bases))
  | _ => None
  end.

(** * alignof() *)
(* todo: we should embed alignment information in our types *)
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

Axiom Proper_align_of : Proper (genv_leq ==> eq ==> Roption_leq eq) (@align_of).
Global Existing Instance Proper_align_of.
