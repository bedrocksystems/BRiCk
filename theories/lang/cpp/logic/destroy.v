(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import elpi.apps.locker.
Require Import iris.proofmode.proofmode.
Require Import bedrock.lang.bi.errors.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
  pred wp path_pred heap_pred const dispatch.

#[local] Set Printing Coercions.
#[local] Infix "|--" := bi_entails.
#[local] Notation "|={ E }=> P" := (|={E}=> P)%I (only parsing).

#[local] Tactic Notation "solve_fupd_shift" open_constr(lem) :=
  (** This assumes [Proper] instances *)
  etrans; last apply lem; apply fupd_elim; by rewrite -!fupd_intro.
#[local] Tactic Notation "solve_shift_fupd" open_constr(lem) :=
  etrans; last apply lem; apply fupd_intro.

(**
Overview:

- [destroy_val tu ty this Q] destructs [this] (which has [ty] as its
most specific type). The memory is returned to the C++ abstract
machine and the continuation [Q] is invoked. If [this] is a structure
or union, [destroy_val] invokes [ty]'s destructor (leaving any virtual
lookup to the caller).

NOTE in our semantics (unlike the standard) all structures and unions
are destroyed via destructors. This is justified because the only
objects that do not have destructors according to the standard have
no-op destructors. Thus, we can model the "not having a destructor" as
an optimization. This choice makes the semantics more uniform.

- [interp free Q] destroys temporaries described by [free :
FreeTemps.t] using [destroy_val]

TODO: Consider cutting down on the boilerplate in this file by making

- [wp_destroy_array] notation for [wp_gen], [mlock]ing the latter and
using (say) type classes for the side-conditions arising in its theory

- [destroy_val] notation for [wp_destroy_val]
*)

(** [wp_gen] *)
(**
[wp_gen WP n Q] "runs" [WP i] for [0 <= i < n] (in order). It satisfies
<<
  wp_gen WP n Q =
    letI* := WP 0 in
    letI* := WP 1 in
    ..
    letI* := WP (n - 1) in
    Q
>>
and is compatible with fancy updates (see rule [wp_gen_shift]).
*)
Definition wp_gen `{!updates.BiFUpd PROP}
    (WP : N -> PROP -> PROP) (n : N) (Q : PROP) : PROP :=
  foldl (fun acc i => WP i acc) (|={top}=> Q) (seqN 0 n).
#[global] Hint Opaque wp_gen : typeclass_instances.

Section wp_gen.
  Context {PROP : bi} `{!updates.BiFUpd PROP}.
  Implicit Types (WP : N -> PROP -> PROP).

  #[local] Notation FRAME WP WP' :=
    (∀ i Q Q', Q -* Q' |-- WP i Q -* WP' i Q') (only parsing).
  Lemma wp_gen_frame WP WP' n Q Q' :
    FRAME WP WP' ->
    Q -* Q' |-- wp_gen WP n Q -* wp_gen WP' n Q'.
  Proof.
    intros wp_frame. rewrite /wp_gen -!foldr_rev.
    induction n using N.peano_ind.
    { rewrite !seqN_0/=. iIntros "HQ >Q !>". by iApply "HQ". }
    rewrite {}IHn seqN_S_end_app left_id_L rev_app_distr /=.
    by apply wp_frame.
  Qed.

  #[local] Notation SHIFT WP :=
    (∀ i Q, (|={top}=> WP i (|={top}=> Q)) |-- WP i Q) (only parsing).
  Lemma wp_gen_shift WP n Q :
    FRAME WP WP -> SHIFT WP ->
    (|={top}=> wp_gen WP n (|={top}=> Q)) |-- wp_gen WP n Q.
  Proof.
    intros wp_frame wp_shift. rewrite /wp_gen -!foldr_rev.
    induction n using N.peano_ind.
    { rewrite !seqN_0 /=. auto using fupd_elim. }
    rewrite seqN_S_end_app left_id_L rev_app_distr /=.
    iIntros "tail".
    iApply wp_shift. iMod "tail". iModIntro.
    iApply (wp_frame with "[] tail").
    iIntros "tail !>". by iApply (IHn with "[$tail]").
  Qed.

  Lemma wp_gen_intro WP n Q :
    FRAME WP WP ->
    foldl (fun acc i => WP i acc) Q (seqN 0 n) |-- wp_gen WP n Q.
  Proof.
    intros wp_frame. rewrite /wp_gen -!foldr_rev.
    induction n using N.peano_ind.
    { rewrite !seqN_0/=. by iIntros "$". }
    rewrite seqN_S_end_app left_id_L rev_app_distr /=. iIntros "wp".
    iApply (wp_frame with "[] wp"). rewrite {}IHn. by iIntros "$".
  Qed.
End wp_gen.


(** ** Destroying primitives *)

#[local] Definition wp_destroy_prim_body `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cv : type_qualifiers) (ty : type) (this : ptr) (Q : epred) : mpred :=
  |={top}=> this |-> anyR (erase_qualifiers ty) (cQp.mk (q_const cv) 1) ** Q.

mlock Definition wp_destroy_prim `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cv : type_qualifiers) (ty : type) (this : ptr) (Q : epred) : mpred :=
  wp_destroy_prim_body tu cv ty this Q.
#[global] Arguments wp_destroy_prim {_ _ _} _ _ _ _ _ : assert.	(* mlock bug *)

Section unfold.
  Context `{Σ : cpp_logic thread_info, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wp_destroy_prim_unfold ty tu :
    wp_destroy_prim tu ty = Reduce (wp_destroy_prim_body tu ty).
  Proof. by rewrite wp_destroy_prim.unlock. Qed.
End unfold.

(**
Unfold for one type, failing if there's nothing to do.
*)
Ltac wp_destroy_prim_unfold :=
  lazymatch goal with
  | |- context [wp_destroy_prim _ ?ty] => rewrite !(wp_destroy_prim_unfold ty)
  | _ => fail "[wp_destroy_prim] not found"
  end.

Section prim.
  Context `{Σ : cpp_logic thread_info, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wp_destroy_prim_intro tu cv ty (this : ptr) Q :
    this |-> anyR (erase_qualifiers ty) (cQp.mk (q_const cv) 1) ** Q
    |-- wp_destroy_prim tu cv ty this Q.
  Proof. wp_destroy_prim_unfold. by iIntros "[$$]". Qed.

  Lemma wp_destroy_prim_elim tu cv ty this Q :
    wp_destroy_prim tu cv ty this Q
    |-- |={top}=> this |-> anyR (erase_qualifiers ty) (cQp.mk (q_const cv) 1) ** Q.
  Proof. by wp_destroy_prim_unfold. Qed.

  Lemma wp_destroy_prim_erase_qualifiers tu cv ty :
    wp_destroy_prim tu cv (erase_qualifiers ty) =
    wp_destroy_prim tu cv ty.
  Proof.
    by rewrite !wp_destroy_prim_unfold erase_qualifiers_idemp.
  Qed.

  (**
  We skip [sub_module] in the [Proper] instances in this file because
  that relation interferes with tactics like [f_equiv]; specifically,
  [Proper] instances mentioning [sub_module] cause goals that ought to
  reduce to entailments after [f_equiv] to instead reduce to
  equalities.
  *)
  #[global] Instance: Params (@wp_destroy_prim) 7 := {}.
  #[local] Notation PROPER R := (
    ∀ tu cv ty p,
    Proper (R ==> R) (wp_destroy_prim tu cv ty p)
  ) (only parsing).
  #[global] Instance wp_destroy_prim_mono : PROPER bi_entails.
  Proof. rewrite wp_destroy_prim.unlock. solve_proper. Qed.
  #[global] Instance wp_destroy_prim_flip_mono : PROPER (flip bi_entails).
  Proof. repeat intro. by apply wp_destroy_prim_mono. Qed.
  #[global] Instance wp_destroy_prim_proper : PROPER equiv.
  Proof.
    intros * Q1 Q2 HQ. split'; by apply wp_destroy_prim_mono; rewrite HQ.
  Qed.

  Lemma wp_destroy_prim_frame tu tu' cv ty this (Q Q' : epred) :
    Q -* Q' |-- wp_destroy_prim tu cv ty this Q -* wp_destroy_prim tu' cv ty this Q'.
  Proof. wp_destroy_prim_unfold. iIntros "HQ >[$ Q]". by iApply "HQ". Qed.

  Lemma wp_destroy_prim_shift tu cv ty this Q :
    (|={top}=> wp_destroy_prim tu cv ty this (|={top}=> Q)) |--
    wp_destroy_prim tu cv ty this Q.
  Proof. wp_destroy_prim_unfold. by iIntros ">>[$ >$]". Qed.

  Lemma fupd_wp_destroy_prim tu cv ty this Q :
    (|={top}=> wp_destroy_prim tu cv ty this Q) |--
    wp_destroy_prim tu cv ty this Q.
  Proof. solve_fupd_shift wp_destroy_prim_shift. Qed.

  Lemma wp_destroy_prim_fupd tu cv ty this Q :
    wp_destroy_prim tu cv ty this (|={top}=> Q) |--
    wp_destroy_prim tu cv ty this Q.
  Proof. solve_shift_fupd wp_destroy_prim_shift. Qed.
End prim.

(** ** Invoking destructors *)
(*
[wp_destructor ty dtor this Q] is the weakest pre-condition of
invoking the destructor [dtor] for type [ty] on [this].
*)
#[local] Definition wp_destructor_body `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ty : type) (dtor : ptr) (this : ptr) (Q : epred) : mpred :=
  (*
  NOTE: Using [Tfunction Tvoid nil] implicitly requires all
  destructors to have C calling convention. Arguments [this :: nil] is
  correct for member functions taking no arguments.
  *)
  letI* p := mspec tu.(types) ty (Tfunction Tvoid nil) dtor (this :: nil) in
  (**
  We inline [operand_receive] (which could be hoisted and shared).
  *)
  Exists v, p |-> primR Tvoid (cQp.mut 1) v **
  this |-> tblockR ty (cQp.mut 1) **
  Q.

mlock Definition wp_destructor `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ty : type) (dtor : ptr) (this : ptr) (Q : epred) : mpred :=
  wp_destructor_body tu ty dtor this Q.
#[global] Arguments wp_destructor {_ _ _} _ _ _ _ _ : assert.	(* mlock bug *)

(** Note: All we need in this file is [type_table_le]. *)
#[local] Notation TULE tu tu' := (sub_module tu tu') (only parsing).
#[local] Hint Resolve types_compat : core.

Section unfold.
  Context `{Σ : cpp_logic thread_info, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wp_destructor_unfold ty tu :
    wp_destructor tu ty = Reduce (wp_destructor_body tu ty).
  Proof. by rewrite wp_destructor.unlock. Qed.
End unfold.

(**
Unfold for one type, failing if there's nothing to do.
*)
Ltac wp_destructor_unfold :=
  lazymatch goal with
  | |- context [wp_destructor _ ?ty] => rewrite !(wp_destructor_unfold ty)
  | _ => fail "[wp_destructor] not found"
  end.

Section dtor.
  Context `{Σ : cpp_logic thread_info, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wp_destructor_intro tu ty dtor this Q :
    Reduce (wp_destructor_body tu ty dtor this Q) |--
    wp_destructor tu ty dtor this Q.
  Proof. by wp_destructor_unfold. Qed.

  Lemma wp_destructor_elim tu ty dtor this Q :
    wp_destructor tu ty dtor this Q |--
    Reduce (wp_destructor_body tu ty dtor this Q).
  Proof. by wp_destructor_unfold. Qed.

  #[global] Instance: Params (@wp_destructor) 7 := {}.
  #[local] Notation PROPER R := (
    ∀ tu ty dtor this,
    Proper (R ==> R) (wp_destructor tu ty dtor this)
  ) (only parsing).
  #[global] Instance wp_destructor_mono : PROPER bi_entails.
  Proof. rewrite wp_destructor.unlock. solve_proper. Qed.
  #[global] Instance wp_destructor_flip_mono : PROPER (flip bi_entails).
  Proof. repeat intro. by apply wp_destructor_mono. Qed.
  #[global] Instance wp_destructor_proper : PROPER equiv.
  Proof. intros * Q1 Q2 HQ. split'; by apply wp_destructor_mono; rewrite HQ. Qed.

  Lemma wp_destructor_frame tu tu' ty dtor this Q Q' :
    TULE tu tu' ->
    Q -* Q' |-- wp_destructor tu ty dtor this Q -* wp_destructor tu' ty dtor this Q'.
  Proof.
    intros. wp_destructor_unfold. iIntros "HQ".
    iApply mspec_frame_fupd_strong; first by auto.
    iIntros "%p (%v & V & B & Q)". iExists v. iFrame "V B". by iApply "HQ".
  Qed.

  Lemma wp_destructor_shift tu ty dtor this Q :
    (|={top}=> wp_destructor tu ty dtor this (|={top}=> Q))
    |-- wp_destructor tu ty dtor this Q.
  Proof.
    wp_destructor_unfold. iIntros "wp".
    iApply mspec_shift. iMod "wp".
    iApply (mspec_frame with "[] wp").
    iIntros (p). iIntros "(%v & V & B & >Q) !>".
    iExists v. iFrame "V B Q".
  Qed.

  Lemma fupd_wp_destructor tu ty dtor this Q :
    (|={top}=> wp_destructor tu ty dtor this Q)
    |-- wp_destructor tu ty dtor this Q.
  Proof. solve_fupd_shift wp_destructor_shift. Qed.

  Lemma wp_destructor_fupd tu ty dtor this Q :
    wp_destructor tu ty dtor this (|={top}=> Q)
    |-- wp_destructor tu ty dtor this Q.
  Proof. solve_shift_fupd wp_destructor_shift. Qed.
End dtor.

(** ** Destroying structures and unions *)

#[local] Definition wp_destroy_named_body `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) (Q : epred) : mpred :=
  match tu.(types) !! cls with
  | Some (Gstruct s) =>
    (*
    In the current implementation, we generate destructors even when
    they are implicit to make the framework a bit more uniform (all
    types have destructors) and allow for direct destructor calls,
    e.g. [c.~C()], which are encoded as [Emember_call ... "~C" ..]

    NOTE the setup with explicit destructors (even when those
    destructors are trivial) abstracts away some of the complexities
    of the underlying C++ semantics that the semantics itself seems
    less than clear about. [CITATION NEEDED]

    TODO let's find some justification in the standard.
    *)
    wp_destructor tu (Tnamed cls) (_global s.(s_dtor)) this Q
  | Some (Gunion u) =>
    (*
    Unions cannot have [virtual] destructors: we directly invoke the
    destructor.
    *)
    wp_destructor tu (Tnamed cls) (_global u.(u_dtor)) this Q
  | _ => |={top}=> ERROR ("wp_destroy_named: cannot resolve", cls)
  end.

mlock Definition wp_destroy_named `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) (Q : epred) : mpred :=
  wp_destroy_named_body tu cls this Q.
#[global] Arguments wp_destroy_named {_ _ _} _ _ _ _ : assert.	(* mlock bug *)

Section unfold.
  Context `{Σ : cpp_logic thread_info, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wp_destroy_named_unfold cls tu :
    wp_destroy_named tu cls = Reduce (wp_destroy_named_body tu cls).
  Proof. by rewrite wp_destroy_named.unlock. Qed.
End unfold.

(**
Unfold for one class, failing if there's nothing to do.
*)
Ltac wp_destroy_named_unfold :=
  lazymatch goal with
  | |- context [wp_destroy_named _ ?cls] => rewrite !(wp_destroy_named_unfold cls)
  | _ => fail "[wp_destroy_named] not found"
  end.

#[local] Hint Resolve ERROR_elim UNSUPPORTED_elim : core.

#[local] Lemma destroy_error_shift `{!BiFUpd PROP} (E P : PROP) :
  E |-- False ->
  (|={top}=> |={top}=> E) |-- |={top}=> P.
Proof. intros ->. by iIntros ">>?". Qed.
#[local] Hint Resolve destroy_error_shift : core.

#[local] Lemma destroy_error_frame_shift `{!BiFUpd PROP} (E P Q R : PROP) :
  E |-- False ->
  (|={top}=> R) |-- Q ->
  P |-- (|={top}=> E) -* Q.
Proof. intros -><-. by iIntros "? >?". Qed.
#[local] Hint Resolve destroy_error_frame_shift : core.

#[local] Hint Resolve bi.False_elim : core.

Section named.
  Context `{Σ : cpp_logic thread_info, σ : genv}.
  Implicit Types (Q : epred).

  Let wp_destroy_named_intro_body (tu : translation_unit)
      (cls : globname) (this : ptr) (Q : epred) : mpred :=
    match tu.(types) !! cls with
    | Some (Gstruct s) => wp_destructor tu (Tnamed cls) (_global s.(s_dtor)) this Q
    | Some (Gunion u) => wp_destructor tu (Tnamed cls) (_global u.(u_dtor)) this Q
    | _ => False
    end.

  Lemma wp_destroy_named_intro tu cls this Q :
    Reduce (wp_destroy_named_intro_body tu cls this Q)
    |-- wp_destroy_named tu cls this Q.
  Proof. wp_destroy_named_unfold. destruct (_ !! _) as [[] |]; auto. Qed.

  Lemma wp_destroy_named_intro_struct tu cls s this Q :
    tu.(types) !! cls = Some (Gstruct s) ->
    wp_destructor tu (Tnamed cls) (_global s.(s_dtor)) this Q
    |-- wp_destroy_named tu cls this Q.
  Proof. by rewrite -wp_destroy_named_intro=>->. Qed.

  Lemma wp_destroy_named_intro_union tu cls u this Q :
    tu.(types) !! cls = Some (Gunion u) ->
    wp_destructor tu (Tnamed cls) (_global u.(u_dtor)) this Q
    |-- wp_destroy_named tu cls this Q.
  Proof. by rewrite -wp_destroy_named_intro=>->. Qed.

  Lemma wp_destroy_named_elim tu cls this Q :
    wp_destroy_named tu cls this Q
    |-- Reduce (wp_destroy_named_body tu cls this Q).
  Proof. by wp_destroy_named_unfold. Qed.

  Lemma wp_destroy_named_elim_struct tu cls s this Q :
    tu.(types) !! cls = Some (Gstruct s) ->
    wp_destroy_named tu cls this Q
    |-- wp_destructor tu (Tnamed cls) (_global s.(s_dtor)) this Q.
  Proof. by rewrite wp_destroy_named_elim=>->. Qed.

  Lemma wp_destroy_named_elim_union tu cls u this Q :
    tu.(types) !! cls = Some (Gunion u) ->
    wp_destroy_named tu cls this Q
    |-- wp_destructor tu (Tnamed cls) (_global u.(u_dtor)) this Q.
  Proof. by rewrite wp_destroy_named_elim=>->. Qed.

  #[global] Instance: Params (@wp_destroy_named) 6 := {}.
  #[local] Notation PROPER R := (
    ∀ tu cls this,
    Proper (R ==> R) (wp_destroy_named tu cls this)
  ) (only parsing).
  #[global] Instance wp_destroy_named_mono : PROPER bi_entails.
  Proof. rewrite wp_destroy_named.unlock. solve_proper. Qed.
  #[global] Instance wp_destroy_named_flip_mono : PROPER (flip bi_entails).
  Proof. repeat intro. by apply wp_destroy_named_mono. Qed.
  #[global] Instance wp_destroy_named_proper : PROPER equiv.
  Proof. intros * Q1 Q2 HQ. split'; by apply wp_destroy_named_mono; rewrite HQ. Qed.

  Lemma wp_destroy_named_frame tu tu' cls this Q Q' :
    TULE tu tu' ->
    Q -* Q' |-- wp_destroy_named tu cls this Q -* wp_destroy_named tu' cls this Q'.
  Proof.
    intros Htu. move: (Htu)=>/types_compat Htt. wp_destroy_named_unfold.
    destruct (_ !! _) as [v1|] eqn:Hv1; last first.
    { case_match; auto. case_match; eauto using fupd_wp_destructor. }
    destruct (Htt cls _ Hv1) as (v2 & -> & Hle). destruct v1, v2; try done.
    all: try solve [ eauto using fupd_wp_destructor ].
    all: cbn in Hle; case_bool_decide; [subst|done].
    all: by apply wp_destructor_frame.
  Qed.

  Lemma wp_destroy_named_shift tu cls this Q :
    (|={top}=> wp_destroy_named tu cls this (|={top}=> Q))
    |-- wp_destroy_named tu cls this Q.
  Proof.
    wp_destroy_named_unfold.
    destruct (_ !! _) as [[] |]; auto using wp_destructor_shift.
  Qed.

  Lemma fupd_wp_destroy_named tu cls this Q :
    (|={top}=> wp_destroy_named tu cls this Q)
    |-- wp_destroy_named tu cls this Q.
  Proof. solve_fupd_shift wp_destroy_named_shift. Qed.

  Lemma wp_destroy_named_fupd tu cls this Q :
    wp_destroy_named tu cls this (|={top}=> Q)
    |-- wp_destroy_named tu cls this Q.
  Proof. solve_shift_fupd wp_destroy_named_shift. Qed.

End named.

(** ** Arrays and values *)
(**
[wp_destroy_val] generalizes [destroy_val], baking in qualifier
normalization (i.e., [destroy_val tm = wp_destroy_val tm QM]).

The following simpler alternatives don't seem to work.

- [destroy_val ty := let '(cv, rty) := decompose_type ty in ⋯]: This
definition does not satisfy Coq's termination checker.

- [destroy_val ty := qual_norm (fun cv rty => ⋯)]: Coq accepts this
definition, but we could not get the theory to go through.
*)
Section body.
  Context `{Σ : cpp_logic, σ : genv}.
  Context (wp_destroy_val : translation_unit -> type_qualifiers -> type -> ptr -> epred -> mpred).
  Context (destroy_val : translation_unit -> type -> ptr -> epred -> mpred).
  Context (wp_destroy_array : translation_unit -> type -> N -> ptr -> epred -> mpred).

  #[local] Definition destroy_val_body (tu : translation_unit)
      (ty : type) (this : ptr) (Q : epred) : mpred :=
    wp_destroy_val tu QM ty this Q.

  #[local] Definition wp_destroy_array_body (tu : translation_unit)
      (ety : type) (sz : N) (this : ptr) (Q : epred) : mpred :=
    (**
    NOTE array elements are destroyed left-to-right with non-virtual
    dispatch.
    *)
    Reduce (wp_gen (fun i => destroy_val tu ety (this .[ erase_qualifiers ety ! Z.of_N i ])) sz Q).

  #[local] Definition wp_destroy_val_body (tu : translation_unit)
      (cv : type_qualifiers) (rty : type) (this : ptr) (Q : epred) : mpred :=
    match rty with
    | Tqualified q ty => wp_destroy_val tu (merge_tq cv q) ty this Q

    | Tnamed cls =>
      |={top}=> |>
      letI* := if q_const cv then wp_make_mutable tu this rty else id in
      letI* := wp_destroy_named tu cls this in
      Q

    | Tarray ety sz =>
      |={top}=> |>
      letI* := if q_const cv then wp_make_mutable tu this rty else id in
      letI* := wp_destroy_array tu ety sz this in
      Q

    | Tref r_ty
    | Trv_ref r_ty =>
      (*
      NOTE rvalue references [Trv_ref] are represented as references
      [Tref].
      *)
      wp_destroy_prim tu cv (Tref r_ty) this Q

    | Tnum _ _
    | Tchar_ _
    | Tfloat_ _
    | Tenum _
    | Tbool
    | Tnullptr
    | Tptr _
    | Tmember_pointer _ _
    | Tvoid =>
      wp_destroy_prim tu cv rty this Q

    | Tfunction _ _ => |={top}=> UNSUPPORTED ("wp_destroy_val: function type", rty)
    | Tarch _ _ => |={top}=> UNSUPPORTED ("wp_destroy_val: arch type", rty)
    end.
End body.

mlock Definition wp_destroy_val `{Σ : cpp_logic, σ : genv}
    : translation_unit -> type_qualifiers -> type -> ptr -> epred -> mpred :=
  (* Written this way because [mlock Fixpoint ⋯] fails. *)
  fix wp_destroy_val tu q ty :=
    let destroy_val := destroy_val_body wp_destroy_val in
    let wp_destroy_array := wp_destroy_array_body destroy_val in
    wp_destroy_val_body wp_destroy_val wp_destroy_array tu q ty.
#[global] Arguments wp_destroy_val {_ _ _} tu cv ty p Q : assert.	(* set names *)

mlock Definition destroy_val `{Σ : cpp_logic, σ : genv}
    : translation_unit -> type -> ptr -> epred -> mpred :=
  destroy_val_body wp_destroy_val.
#[global] Arguments destroy_val {_ _ _} tu ty p Q : assert.	(* set names *)

mlock Definition wp_destroy_array `{Σ : cpp_logic, σ : genv}
    (tu : translation_unit) (ety : type) (sz : N) (base : ptr) (Q : epred) : mpred :=
  wp_destroy_array_body destroy_val tu ety sz base Q.
#[global] Arguments wp_destroy_array {_ _ _} _ _ _ _ _ : assert.	(* mlock bug *)

#[local] Notation V := (wp_destroy_val_body wp_destroy_val wp_destroy_array) (only parsing).
#[local] Notation A := (wp_destroy_array_body destroy_val) (only parsing).

Section unfold.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wp_destroy_val_unfold ty tu cv : wp_destroy_val tu cv ty = Reduce (V tu cv ty).
  Proof.
    trans (V tu cv ty); last done.
    rewrite wp_destroy_array.unlock destroy_val.unlock wp_destroy_val.unlock.
    by destruct ty.
  Qed.

  Lemma destroy_val_unfold ty tu : destroy_val tu ty = Cbn (Reduce (V tu QM ty)).
  Proof.
    rewrite {1}destroy_val.unlock. apply wp_destroy_val_unfold.
  Qed.

  Lemma wp_destroy_array_unfold ety tu : wp_destroy_array tu ety = Reduce (A tu ety).
  Proof. by rewrite wp_destroy_array.unlock. Qed.
End unfold.

(**
These tactics unfold for one type, failing if there's nothing to do.
*)
Ltac wp_destroy_val_unfold :=
  lazymatch goal with
  | |- context [wp_destroy_val _ _ ?ty] => rewrite !(wp_destroy_val_unfold ty)
  | _ => fail "[wp_destroy_val] not found"
  end.
Ltac destroy_val_unfold :=
  lazymatch goal with
  | |- context [destroy_val _ ?ty] => rewrite !(destroy_val_unfold ty)
  | _ => fail "[destroy_val] not found"
  end.
Ltac wp_destroy_array_unfold :=
  lazymatch goal with
  | |- context [wp_destroy_array _ ?ty] => rewrite !(wp_destroy_array_unfold ty)
  | _ => fail "[wp_destroy_array] not found"
  end.

Section val_array.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma destroy_val_wp_destroy_val ty tu :
    destroy_val tu ty = wp_destroy_val tu QM ty.
  Proof. by rewrite destroy_val.unlock. Qed.

  (** Qualifier normalization *)

  Lemma wp_destroy_val_qual_norm' tu cv ty this Q :
    wp_destroy_val tu cv ty this Q =
      qual_norm' (fun cv' ty' => wp_destroy_val tu cv' ty' this Q) cv ty.
  Proof.
    rewrite wp_destroy_val.unlock. move: cv. by induction ty; cbn.
  Qed.
  Lemma destroy_val_qual_norm tu ty this Q :
    destroy_val tu ty this Q =
      qual_norm (fun cv ty' => wp_destroy_val tu cv ty' this Q) ty.
  Proof.
    rewrite {1}destroy_val.unlock /destroy_val_body.
    by rewrite wp_destroy_val_qual_norm'.
  Qed.

  Lemma wp_destroy_val_decompose_type tu cv ty this Q :
    wp_destroy_val tu cv ty this Q =
      let p := decompose_type ty in
      wp_destroy_val tu (merge_tq cv p.1) p.2 this Q.
  Proof.
    by rewrite wp_destroy_val_qual_norm' qual_norm'_decompose_type.
  Qed.
  Lemma destroy_val_decompose_type tu ty this Q :
    destroy_val tu ty this Q =
      let p := decompose_type ty in
      wp_destroy_val tu p.1 p.2 this Q.
  Proof.
    by rewrite destroy_val_qual_norm qual_norm_decompose_type.
  Qed.

  Lemma wp_destroy_val_ref tu cv ty :
    wp_destroy_val tu cv (Tref ty) =
    wp_destroy_val tu cv (Trv_ref ty).
  Proof. by rewrite !wp_destroy_val_unfold. Qed.
  Lemma destroy_val_ref tu ty :
    destroy_val tu (Tref ty) =
    destroy_val tu (Trv_ref ty).
  Proof. by rewrite !destroy_val_unfold. Qed.

  (** Structural properties *)

  #[local] Hint Resolve
    wp_destroy_prim_frame
    wp_destroy_named_frame
    wp_gen_frame
  : core.

  Lemma wp_destroy_val_frame tu tu' cv ty this Q Q' :
    TULE tu tu' ->
    Q -* Q' |-- wp_destroy_val tu cv ty this Q -* wp_destroy_val tu' cv ty this Q'.
  Proof.
    move: tu tu' cv this Q Q'. induction ty=>tu tu' cv this Q Q' Htu.
    all: wp_destroy_val_unfold; auto.
    all: iIntros "? >wp !> !>"; iRevert "wp"; iStopProof.
    all: destruct (q_const cv); [rewrite -wp_const_frame|cbn]; auto.
    all: wp_destroy_array_unfold; rewrite !destroy_val_wp_destroy_val.
    all: apply wp_gen_frame; auto.
  Qed.
  Lemma destroy_val_frame tu tu' ty this Q Q' :
    TULE tu tu' ->
    Q -* Q' |-- destroy_val tu ty this Q -* destroy_val tu' ty this Q'.
  Proof. rewrite !destroy_val_wp_destroy_val. apply wp_destroy_val_frame. Qed.

  Lemma wp_destroy_array_frame tu tu' ety n p Q Q' :
    TULE tu tu' ->
    Q -* Q' |-- wp_destroy_array tu ety n p Q -* wp_destroy_array tu' ety n p Q'.
  Proof.
    intros. wp_destroy_array_unfold. apply wp_gen_frame. intros.
    by apply destroy_val_frame.
  Qed.

  Lemma wp_destroy_val_shift tu cv ty this Q :
    (|={top}=> wp_destroy_val tu cv ty this (|={top}=> Q))
    |-- wp_destroy_val tu cv ty this Q.
  Proof.
    move: tu cv this Q. induction ty=>tu cv this Q.
    all: wp_destroy_val_unfold; auto using wp_destroy_prim_shift.
    (* Laters *)
    all: iIntros ">>wp !> !>".
    all: destruct (q_const cv);
      [ iApply wp_const_shift; iIntros "!>"; iApply (wp_const_frame with "[] wp"); first done; iIntros "wp !>"
      | cbn ].
    all: try by iApply wp_destroy_named_shift; auto.
    all: wp_destroy_array_unfold; rewrite !destroy_val_wp_destroy_val.
    all: iApply (wp_gen_shift with "wp"); auto; intros.
    all: by apply wp_destroy_val_frame.
  Qed.
  Lemma destroy_val_shift tu ty this Q :
    (|={top}=> destroy_val tu ty this (|={top}=> Q))
    |-- destroy_val tu ty this Q.
  Proof. rewrite destroy_val_wp_destroy_val. apply wp_destroy_val_shift. Qed.

  Lemma wp_destroy_array_shift tu ety n p Q :
    (|={top}=> wp_destroy_array tu ety n p (|={top}=> Q))
    |-- wp_destroy_array tu ety n p Q.
  Proof.
    wp_destroy_array_unfold. apply wp_gen_shift; intros.
    by apply destroy_val_frame. by apply destroy_val_shift.
  Qed.

  (** Setoids *)

  #[global] Instance: Params (@wp_destroy_val) 7 := {}.
  #[local] Notation V'PROPER R := (
    ∀ tu cv ty this,
    Proper (R ==> R) (wp_destroy_val tu cv ty this)
  ) (only parsing).
  #[global] Instance wp_destroy_val_mono : V'PROPER bi_entails.
  Proof.
    intros * Q1 Q2 HQ.
    iIntros "wp". iApply (wp_destroy_val_frame with "[] wp"); [done..|].
    by iApply HQ.
  Qed.
  #[global] Instance wp_destroy_val_flip_mono : V'PROPER (flip bi_entails).
  Proof. repeat intro. by apply wp_destroy_val_mono. Qed.
  #[global] Instance wp_destroy_val_proper : V'PROPER equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply wp_destroy_val_mono; rewrite HQ. Qed.

  #[global] Instance: Params (@destroy_val) 6 := {}.
  #[local] Notation VPROPER R := (
    ∀ tu ty this,
    Proper (R ==> R) (destroy_val tu ty this)
  ) (only parsing).
  #[global] Instance destroy_val_mono : VPROPER bi_entails.
  Proof. rewrite destroy_val.unlock. solve_proper. Qed.
  #[global] Instance destroy_val_flip_mono : VPROPER (flip bi_entails).
  Proof. repeat intro. by apply destroy_val_mono. Qed.
  #[global] Instance destroy_val_proper : VPROPER equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply destroy_val_mono; rewrite HQ. Qed.

  #[global] Instance: Params (@wp_destroy_array) 7 := {}.
  #[local] Notation APROPER R := (
    ∀ tu ety n p,
    Proper (R ==> R) (wp_destroy_array tu ety n p)
  ) (only parsing).
  #[global] Instance wp_destroy_array_mono : APROPER bi_entails.
  Proof.
    intros * Q1 Q2 HQ.
    iIntros "wp". iApply (wp_destroy_array_frame with "[] wp"); [done..|].
    by iApply HQ.
  Qed.
  #[global] Instance wp_destroy_array_flip_mono : APROPER (flip bi_entails).
  Proof. repeat intro. by apply wp_destroy_array_mono. Qed.
  #[global] Instance wp_destroy_array_proper : APROPER equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply wp_destroy_array_mono; rewrite HQ. Qed.

  Lemma fupd_wp_destroy_val tu cv ty this Q :
    (|={top}=> wp_destroy_val tu cv ty this Q) |--
    wp_destroy_val tu cv ty this Q.
  Proof. solve_fupd_shift wp_destroy_val_shift. Qed.
  Lemma fupd_destroy_val tu ty this Q :
    (|={top}=> destroy_val tu ty this Q) |--
    destroy_val tu ty this Q.
  Proof. solve_fupd_shift destroy_val_shift. Qed.

  Lemma wp_destroy_val_fupd tu cv ty this Q :
    wp_destroy_val tu cv ty this (|={top}=> Q) |--
    wp_destroy_val tu cv ty this Q.
  Proof. solve_shift_fupd wp_destroy_val_shift. Qed.
  Lemma destroy_val_fupd tu ty this Q :
    destroy_val tu ty this (|={top}=> Q) |--
    destroy_val tu ty this Q.
  Proof. solve_shift_fupd destroy_val_shift. Qed.

  Lemma fupd_wp_destroy_array tu ety n p Q :
    (|={top}=> wp_destroy_array tu ety n p Q) |--
    wp_destroy_array tu ety n p Q.
  Proof. solve_fupd_shift wp_destroy_array_shift. Qed.

  Lemma wp_destroy_array_fupd tu ety n p Q :
    wp_destroy_array tu ety n p (|={top}=> Q) |--
    wp_destroy_array tu ety n p Q.
  Proof. solve_shift_fupd wp_destroy_array_shift. Qed.

  (** Introduction rules *)
  Section intro.
    Let intro_body tu cv rty this Q : mpred :=
      match rty with
      | Tqualified q ty => wp_destroy_val tu (merge_tq cv q) ty this Q
      | Tnamed cls =>
        |>
        letI* := if q_const cv then wp_make_mutable tu this rty else id in
        letI* := wp_destroy_named tu cls this in
        Q
      | Tarray ety sz =>
        |>
        letI* := if q_const cv then wp_make_mutable tu this rty else id in
        letI* := wp_destroy_array tu ety sz this in
        Q
      | Tref r_ty
      | Trv_ref r_ty =>
        wp_destroy_prim tu cv (Tref r_ty) this Q
      | Tnum _ _
      | Tchar_ _
      | Tfloat_ _
      | Tenum _
      | Tbool
      | Tnullptr
      | Tptr _
      | Tmember_pointer _ _
      | Tvoid =>
        wp_destroy_prim tu cv rty this Q
      | Tfunction _ _
      | Tarch _ _ => False
      end.

    Lemma wp_destroy_val_intro rty tu cv this Q :
      Reduce (intro_body tu cv rty this Q)
      |-- wp_destroy_val tu cv rty this Q.
    Proof. wp_destroy_val_unfold. destruct rty; cbn; auto. Qed.
    Lemma destroy_val_intro ty tu this Q :
      Cbn (Reduce (intro_body tu QM ty this Q))
      |-- destroy_val tu ty this Q.
    Proof.
      by rewrite destroy_val_wp_destroy_val -wp_destroy_val_intro.
    Qed.

    Lemma wp_destroy_array_intro tu ety n p Q :
      foldl (fun Q i => destroy_val tu ety (p .[ erase_qualifiers ety ! Z.of_N i ]) Q) Q (seqN 0 n)
      |-- wp_destroy_array tu ety n p Q.
    Proof.
      wp_destroy_array_unfold. apply wp_gen_intro. intros.
      by apply destroy_val_frame.
    Qed.
  End intro.

  Lemma wp_destroy_val_elim tu cv rty this Q :
    wp_destroy_val tu cv rty this Q
    |-- Reduce (V tu cv rty this Q).
  Proof. by wp_destroy_val_unfold. Qed.
  Lemma destroy_val_elim tu ty this Q :
    destroy_val tu ty this Q
    |-- Cbn (Reduce (V tu QM ty this Q)).
  Proof. by destroy_val_unfold. Qed.

  Lemma wp_destroy_val_value_type_elim tu cv ty this Q :
    is_value_type ty ->
    wp_destroy_val tu cv ty this Q |--
      qual_norm' (fun cv ty =>
        wp_destroy_prim tu cv ty this Q
      ) cv ty.
  Proof.
    rewrite {1}wp_destroy_val_qual_norm'.
    elim: (qual_norm'_ok _ cv ty); [|done]. move=>? rty *.
    rewrite qual_norm'_unqual. wp_destroy_val_unfold.
    destruct rty; first [done | by case: unqualified_qual].
  Qed.
  Lemma destroy_val_value_type_elim tu ty this Q :
    is_value_type ty ->
    destroy_val tu ty this Q |--
      qual_norm (fun cv ty =>
        wp_destroy_prim tu cv ty this Q
      ) ty.
  Proof.
    intros.
    by rewrite destroy_val_wp_destroy_val  wp_destroy_val_value_type_elim.
  Qed.

  Lemma wp_destroy_array_elim tu ety n p Q :
    wp_destroy_array tu ety n p Q
    |-- Reduce (A tu ety n p Q).
  Proof. by wp_destroy_array_unfold. Qed.
End val_array.

(** ** Destroying temporaries *)
(**
[interp free Q] "runs" [free] and then acts like [Q].

NOTE why not just destroy each object with [Q := emp]?

Consider destroying 2 objects using destructors that return resources,
i.e. suppose specifications such as [\post Q].

[interp (par (delete ty a) (delete ty b)) Q] will reduce to

<<
  Exists Q1 Q2,
    (... ** (Q -* Q1)) **
    (... ** (Q -* Q2)) **
    (Q1 -* Q2 -* ..)
>>

With the trivial instantiation, this becomes unprovable because [Q -*
emp] is not provable unless [Q] is affine.
*)
(* BEGIN interp *)
#[local] Definition interp_body `{Σ : cpp_logic, σ : genv}
    (interp : translation_unit -> FreeTemps -> epred -> mpred)
    (tu : translation_unit) (free : FreeTemps) (Q : epred) : mpred :=
  match free with
  | FreeTemps.id => |={top}=> Q
  | FreeTemps.seq f g => interp tu f $ interp tu g Q
  | FreeTemps.par f g => |={top}=> Exists Qf Qg, interp tu f Qf ** interp tu g Qg ** (Qf -* Qg -* |={top}=> Q)
  | FreeTemps.delete ty addr => destroy_val tu ty addr Q
  | FreeTemps.delete_va va addr => |={top}=> addr |-> varargsR va ** Q
  end.

mlock Definition interp `{Σ : cpp_logic, σ : genv}
    : translation_unit -> FreeTemps -> epred -> mpred :=
  fix interp tu free :=
  interp_body interp tu free.
#[global] Arguments interp {_ _ _} _ free Q : assert.	(* set names *)
(* END interp *)
(* ^^ These BEGIN/END markers matter to our documentation *)

Section unfold.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types Q : epred.

  Lemma interp_unfold free tu : interp tu free = Reduce (interp_body interp tu free).
  Proof. rewrite interp.unlock. by destruct free. Qed.
End unfold.

(**
Unfold for one inhabitant of [FreeTemps], failing if there's nothing
to do.
*)
Ltac interp_unfold :=
  lazymatch goal with
  | |- context [interp _ ?f] => rewrite !(interp_unfold f)
  | _ => fail "[interp] not found"
  end.

Section temps.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types Q : epred.

  Lemma interp_intro free tu Q :
    match free with
    | FreeTemps.id => Q
    | FreeTemps.seq f g => interp tu f (interp tu g Q)
    | FreeTemps.par f g => Exists Qf Qg, interp tu f Qf ** interp tu g Qg ** (Qf -* Qg -* Q)
    | FreeTemps.delete ty addr => destroy_val tu ty addr Q
    | FreeTemps.delete_va va addr => addr |-> varargsR va ** Q
    end
    |-- interp tu free Q.
  Proof.
    interp_unfold. destruct free; auto using fupd_elim.
    { (* par *) iIntros "(%Qf & %Qg & Qf & Qg & HQ)".
      iExists Qf, Qg. iFrame "Qf Qg". iIntros "!> Qf Qg".
      iApply ("HQ" with "Qf Qg"). }
  Qed.

  Lemma interp_intro_id tu Q : Q |-- interp tu 1 Q.
  Proof. by rewrite -interp_intro. Qed.

  Lemma interp_intro_seq tu f g Q :
    interp tu f (interp tu g Q) |-- interp tu (f >*> g) Q.
  Proof. by rewrite -(interp_intro (f >*> g)). Qed.

  Lemma interp_intro_par tu f g Q :
    Exists Qf Qg, interp tu f Qf ** interp tu g Qg ** (Qf -* Qg -* Q)
    |-- interp tu (f |*| g) Q.
  Proof. by rewrite -interp_intro. Qed.

  Lemma interp_intro_delete tu ty addr Q :
    destroy_val tu ty addr Q
    |-- interp tu (FreeTemps.delete ty addr) Q.
  Proof. by rewrite -interp_intro. Qed.

  Lemma interp_intro_delete_va tu va (addr : ptr) Q :
    addr |-> varargsR va ** Q
    |-- interp tu (FreeTemps.delete_va va addr) Q.
  Proof. by rewrite -interp_intro. Qed.

  (** Elimination rules *)

  Lemma interp_elim free tu Q :
    interp tu free Q |--
    Reduce (interp_body interp tu free Q).
  Proof. by interp_unfold. Qed.

  Lemma interp_elim_id tu Q : interp tu 1 Q |-- |={top}=> Q.
  Proof. apply interp_elim. Qed.

  Lemma interp_elim_seq tu f g Q : interp tu (f >*> g) Q |-- interp tu f (interp tu g Q).
  Proof. apply interp_elim. Qed.

  Lemma interp_elim_par tu f g Q :
    interp tu (f |*| g) Q
    |-- |={top}=> Exists Qf Qg, interp tu f Qf ** interp tu g Qg ** (Qf -* Qg -* |={top}=> Q).
  Proof. apply interp_elim. Qed.

  Lemma interp_elim_delete tu ty addr Q :
    interp tu (FreeTemps.delete ty addr) Q
    |-- destroy_val tu ty addr Q.
  Proof. apply interp_elim. Qed.

  Lemma interp_elim_delete_va tu va addr Q :
    interp tu (FreeTemps.delete_va va addr) Q
    |-- |={top}=> addr |-> varargsR va ** Q.
  Proof. apply interp_elim. Qed.

  (** Structural rules *)

  Lemma interp_frame_strong tu tu' free Q Q' :
    TULE tu tu' ->
    Q -* Q' |-- interp tu free Q -* interp tu' free Q'.
  Proof.
    intros. move: Q Q'. induction free=>Q Q'; interp_unfold; iIntros "HQ".
    - iIntros ">Q". by iApply "HQ".
    - by iApply destroy_val_frame.
    - iIntros ">($ & Q)". by iApply "HQ".
    - iApply IHfree1. by iApply IHfree2.
    - iIntros ">(%Qf & %Qg & (Qf & Qg & Hfg))". iExists Qf, Qg.
      iDestruct (IHfree1 with "[] Qf") as "$"; auto.
      iDestruct (IHfree2 with "[] Qg") as "$"; auto.
      iIntros "!> Qf Qg". iApply "HQ". iApply ("Hfg" with "Qf Qg").
  Qed.

  (** The name is historic *)
  Lemma interp_frame tu free Q Q' :
    Q -* Q' |-- interp tu free Q -* interp tu free Q'.
  Proof. by apply interp_frame_strong. Qed.

  Lemma interp_wand tu free Q Q' :
    interp tu free Q |-- (Q -* Q') -* interp tu free Q'.
  Proof. iIntros "wp HQ". by iApply (interp_frame with "HQ wp"). Qed.

  Lemma interp_shift tu free Q :
    (|={top}=> interp tu free (|={top}=> Q))
    |-- interp tu free Q.
  Proof.
    move: Q. induction free=>Q; interp_unfold.
    - by iIntros ">>>Q".
    - iApply destroy_val_shift.
    - iIntros ">>($ & $)".
    - iIntros "HQ". iApply (IHfree1 with "[HQ]"). iApply (interp_wand with "HQ").
      iIntros "HQ". by iApply (IHfree2 with "[HQ]").
    - iIntros ">>(%Qf & %Qg & (Qf & Qg & Hfg))". iExists Qf, Qg.
      iFrame "Qf Qg". iIntros "!> Qf Qg". by iMod ("Hfg" with "Qf Qg").
  Qed.

  Lemma fupd_interp tu free Q :
    (|={top}=> interp tu free Q) |-- interp tu free Q.
  Proof.
    iIntros "wp". iApply interp_shift. iMod "wp".
    iApply (interp_wand with "wp"). by iIntros "!> $".
  Qed.

  Lemma interp_fupd tu free Q :
    interp tu free (|={top}=> Q) |-- interp tu free Q.
  Proof. solve_shift_fupd interp_shift. Qed.

  Lemma interp_free tu free free' Q :
    free ≡ free' -> interp tu free Q -|- interp tu free' Q.
  Proof.
    #[local] Notation WEAK_PROPER R :=
      (∀ tu free, Proper (R ==> R) (interp tu free)) (only parsing).
    have weak_mono : WEAK_PROPER bi_entails.
    { clear. intros * Q1 Q2 HQ. iIntros "wp".
      iApply (interp_wand with "wp"). by iApply HQ. }
    have {weak_mono} weak_proper : WEAK_PROPER equiv.
    { clear -weak_mono. intros * Q1 Q2 HQ.
      split'; apply weak_mono; by rewrite HQ. }
    have fupd_interp : ∀ tu free Q,
      (|={top}=> interp tu free Q) -|- interp tu free Q.
    { clear. split'; auto using fupd_interp, fupd_elim. }
    have interp_fupd : ∀ tu free Q,
      interp tu free (|={top}=> Q) -|- interp tu free Q.
    { clear. split'; first apply interp_fupd.
      iIntros "wp". iApply (interp_wand with "wp"). by iIntros "$". }
    intros i. move: Q. induction i=>Q.
    { done. }
    { by rewrite IHi. }
    { by rewrite IHi IHi0. }
    { by rewrite !interp_unfold destroy_val_ref. }
    { by rewrite !(interp_unfold (_ >*> _)). }
    { rewrite (interp_unfold (_ >*> _)) (interp_unfold 1).
      by rewrite fupd_interp. }
    { rewrite (interp_unfold (_ >*> _)) (interp_unfold 1).
      by rewrite interp_fupd. }
    { rewrite !(interp_unfold (_ >*> _)). by rewrite IHi IHi0. }
    { rewrite !(interp_unfold (_ |*| _)).
      f_equiv. rewrite bi.exist_exist. f_equiv=>Qf. f_equiv=>Qg.
      by split'; iIntros "($ & $ & F) A B"; iApply ("F" with "B A"). }
    { rewrite !(interp_unfold (_ |*| _)). split'.
      - iIntros ">(%Qx & %Qyz & wpx & Hyz & HQ)".
        iMod "Hyz" as "(%Qy & %Qz & wpy & wpz & Hyz)".
        iExists (Qx ** Qy), Qz. rewrite -(bi.exist_intro Qx) -(bi.exist_intro Qy).
        iFrame "wpz wpx wpy". iIntros "!>". iSplitR.
        { by iIntros "!> $ $". }
        iIntros "[Qx Qy] Qz". iMod ("Hyz" with "Qy Qz") as "Qyz".
        iApply ("HQ" with "Qx Qyz").
      - iIntros ">(%Qxy & %Qz & Hxy & wpz & HQ)".
        iMod "Hxy" as "(%Qx & %Qy & wpx & wpy & Hxy)".
        iExists Qx, (Qy ** Qz). rewrite -(bi.exist_intro Qy) -(bi.exist_intro Qz).
        iFrame "wpz wpx wpy". iIntros "!>". iSplitR.
        { by iIntros "!> $ $". }
        iIntros "Qx [Qy Qz]". iMod ("Hxy" with "Qx Qy") as "Qxy".
        iApply ("HQ" with "Qxy Qz"). }
    { rewrite (interp_unfold (_ |*| _)) (interp_unfold 1). split'.
      - iIntros "X". iApply interp_shift.
        iMod "X" as "(%Qf & %Qg & >Qf & wp & HQ)".
        iApply (interp_wand with "wp"). iIntros "!> Qg".
        iApply ("HQ" with "Qf Qg").
      - iIntros "wp". iExists emp, Q. iFrame "wp".
        iIntros "!>". iSplitL; by auto. }
    { rewrite !(interp_unfold (_ |*| _)).
      setoid_rewrite IHi. by setoid_rewrite IHi0. }
  Qed.

  #[global] Instance: Params (@interp) 4 := {}.
  #[local] Notation PROPER R := (
    ∀ tu,
    Proper (equiv ==> R ==> R) (interp tu)
  ) (only parsing).
  #[global] Instance interp_mono : PROPER bi_entails.
  Proof.
    intros * f1 f2 Hf Q1 Q2 HQ. iIntros "wp".
    iApply interp_free; first done.
    iApply (interp_wand with "wp").
    by iApply HQ.
  Qed.
  #[global] Instance interp_flip_mono : PROPER (flip bi_entails).
  Proof. repeat intro. by apply interp_mono. Qed.
  #[global] Instance interp_proper : PROPER equiv.
  Proof.
    intros * f1 f2 HF Q1 Q2 HQ.
    split'; (apply interp_mono; [by rewrite HF|by rewrite HQ]).
  Qed.

  Section proofmode.
    Context (tu : translation_unit) (free : FreeTemps).
    Implicit Types (P : mpred).
    #[local] Notation WP := (interp tu free).

    #[global] Instance elim_modal_fupd_interp p P Q :
      ElimModal True p false (|={top}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_interp.
    Qed.
    #[global] Instance elim_modal_bupd_interp p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_interp.
    Qed.
    #[global] Instance add_modal_fupd_interp P Q : AddModal (|={top}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_interp.
    Qed.
  End proofmode.
End temps.
#[global] Hint Resolve interp_intro_id : core.
