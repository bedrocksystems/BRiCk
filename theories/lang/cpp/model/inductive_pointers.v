(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Another (incomplete) consistency proof for [PTRS], based on Krebbers' PhD thesis, and
other formal models of C++ using structured pointers.
This is more complex than [SIMPLE_PTRS_IMPL], but will be necessary to justify [VALID_PTR_AXIOMS].

In this model, all valid pointers have an address pinned, but this is not meant
to be guaranteed.
*)

From stdpp Require Import gmap.
From bedrock.lang.prelude Require Import base addr avl bytestring option numbers.

From bedrock.lang.cpp Require Import ast.
From bedrock.lang.cpp.semantics Require Import sub_module values.
From bedrock.lang.cpp.model Require Import simple_pointers_utils inductive_pointers_utils.

Implicit Types (σ : genv).
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

Module Type PTRS_INTF_MINIMAL := PTRS <+ PTRS_DERIVED.

Module PTRS_IMPL : PTRS_INTF_MINIMAL.
  Import canonical_tu address_sums merge_elems.

  Inductive raw_offset_seg : Set :=
  | o_field_ (* type-name: *) (f : field)
  | o_sub_ (ty : type) (z : Z)
  | o_base_ (derived base : globname)
  | o_derived_ (base derived : globname)
  | o_invalid_.
  #[local] Instance raw_offset_seg_eq_dec : EqDecision raw_offset_seg.
  Proof. solve_decision. Qed.
  Declare Instance raw_offset_seg_countable : Countable raw_offset_seg.

  Definition offset_seg : Set := raw_offset_seg * Z.
  #[local] Instance offset_seg_eq_dec : EqDecision offset_seg := _.
  #[local] Instance offset_seg_countable : Countable offset_seg := _.

  Definition eval_raw_offset_seg σ (ro : raw_offset_seg) : option Z :=
    match ro with
    | o_field_ f => o_field_off σ f
    | o_sub_ ty z => o_sub_off σ ty z
    | o_base_ derived base => o_base_off σ derived base
    | o_derived_ base derived => o_derived_off σ base derived
    | o_invalid_ => None
    end.
  Definition mk_offset_seg σ (ro : raw_offset_seg) : offset_seg :=
    match eval_raw_offset_seg σ ro with
    | None => (o_invalid_, 0%Z)
    | Some off => (ro, off)
    end.

  (* This list is reversed.
  The list of offsets in [[p; o_1; ...; o_n]] is represented as [[o_n; ... o_1]].
  This way, we can cons new offsets to the head, and consume them at the tail. *)
  Definition raw_offset := list offset_seg.
  #[local] Instance raw_offset_eq_dec : EqDecision offset := _.
  #[local] Instance raw_offset_countable : Countable raw_offset := _.

  Notation isnt o pattern :=
    (match o with | pattern => False | _ => True end).

  Implicit Types (z : Z).
  (* Close Scope nat_scope. *)
  #[local] Open Scope Z_scope.
  Section roff_canon.
    (* Context {σ : genv}. *)

    (* We currently ensure the offsets in the destination are correct wrt the source, not that the ones in the source are consistent with each other. *)
    Inductive roff_canon : raw_offset -> raw_offset -> Prop :=
    | o_nil :
      roff_canon [] []
    | o_field_canon s d f o :
      (* is_Some (o_field_off σ f) -> *) (* not canonicalization's problem? *)
      roff_canon s d ->
      roff_canon ((o_field_ f, o) :: s) ((o_field_ f, o) :: d)
    | o_base_canon s d base derived o :
      (* no, because (valid?) normal forms don't use [o_derived]? *)
      (* isnt d ((o_derived_ _ _ , _) :: _) -> *)
      roff_canon s d ->
      roff_canon ((o_base_ derived base, o) :: s) ((o_base_ derived base, o) :: d)
    (* should paths start from the complete object? If
    yes, as done by Ramananandro [POPL 2012],
    o_derived should just cancel out o_base, and this should be omitted. *)
    (* | o_derived_wf s d derived base :
      isnt d (o_base_ _ _ :: d) ->
      roff_canon s d ->
      roff_canon (o_derived_ base derived :: s) (o_derived_ base derived :: d) *)
    | o_derived_cancel_canon s d derived base o1 o2 :
      roff_canon s d ->
      (* This premise is a hack, but without it, normalization might not be deterministic. Thankfully, paths can't contain o_derived step, so we're good! *)
      (* roff_canon (o_base_ derived base :: s) (o_base_ derived base :: d) -> *)
      roff_canon ((o_derived_ base derived, o1) :: (o_base_ derived base, o2) :: s) d
    | o_sub_0_canon s d ty :
      roff_canon s d ->
      roff_canon ((o_sub_ ty 0, 0) :: s) d
    | o_sub_canon s d ty1 z o :
      match d with
      | ((o_sub_ ty2 _, _) :: _) => ty1 <> ty2
      | _ => True
      end ->
      (* In fact, we want [0 < z], but that's a matter of validity, not canonicalization. *)
      z <> 0 ->
      (* isnt o (o_sub_ _ _) *)
      roff_canon s d ->
      roff_canon ((o_sub_ ty1 z, o) :: s) ((o_sub_ ty1 z, o) :: d)
    | o_sub_merge_canon s d ty z1 z2 o1 o2 :
      (* Again, validity would require [> 0]. *)
      z1 + z2 <> 0 ->
      roff_canon s ((o_sub_ ty z1, o1) :: d) ->
      roff_canon ((o_sub_ ty z2, o2) :: s) ((o_sub_ ty (z1 + z2), o1 + o2) :: d)
    .
  End roff_canon.

  Lemma roff_canon_o_base_inv s d derived base o1 o2 :
    roff_canon ((o_base_ derived base, o1) :: s) ((o_base_ derived base, o2) :: d) ->
    roff_canon s d.
  Proof. inversion 1; auto. Qed.

  Lemma roff_canon_o_sub_wf s d ty z o :
    roff_canon s ((o_sub_ ty z, o) :: d) ->
    z <> 0.
  Proof.
    move E: (_ :: _) => d' Hcn.
    elim: Hcn E; naive_solver eauto with lia.
  Qed.

  Lemma roff_canon_o_sub_no_dup s d o ty1 z ro :
    roff_canon s ((o_sub_ ty1 z, ro) :: o :: d) ->
    match o with
    | (o_sub_ ty2 _, _) => ty1 <> ty2
    | _ => True
    end.
  Proof.
    move E: ((o_sub_ _ _, _) :: _) => d' Hcn.
    elim: Hcn z ro E; naive_solver.
  Qed.

  Definition offset_seg_cons (os : offset_seg) (oss : list offset_seg) : list offset_seg :=
    match os, oss with
    | (o_sub_ ty1 n1, off1), _ =>
      if decide (n1 = 0 /\ off1 = 0)%Z then oss else
      match oss with
        | (o_sub_ ty2 n2, off2) :: oss' =>
        if decide (ty1 <> ty2)
          then os :: oss
          else if decide (n2 + n1 = 0 /\ off1 + off2 = 0)%Z
          then oss'
          else (o_sub_ ty1 (n2 + n1), (off2 + off1)%Z) :: oss'
        | _ => os :: oss
      end
    | (o_derived_ base1 der1, off1), (o_base_ der2 base2, off2) :: oss' =>
      if decide (der1 = der2 /\ base1 = base2)
      then oss'
      else os :: oss
    (* | (o_invalid_, _), _ => [(o_invalid_, 0%Z)] *)
    | _, _ => os :: oss
    end.
  Definition raw_offset_collapse : raw_offset -> raw_offset :=
    foldr offset_seg_cons [].
  Arguments raw_offset_collapse !_ /.

  Definition raw_offset_wf (ro : raw_offset) : Prop :=
    raw_offset_collapse ro = ro.
  Arguments raw_offset_wf !_ /.
  Instance raw_offset_wf_pi ro : ProofIrrel (raw_offset_wf ro) := _.
  Lemma singleton_raw_offset_wf {os}
    (Hn0 : isnt os (o_sub_ _ 0, _)) :
    raw_offset_wf [os].
  Proof. destruct os as [[] ?] => //=; case_decide; naive_solver. Qed.

  #[local] Hint Constructors roff_canon : core.
  Theorem canon_wf_0 src dst :
    roff_canon src dst ->
    roff_canon dst dst.
  Proof.
    intros Hrc; induction Hrc; eauto.
    inversion IHHrc; eauto 2; last have ?: z0 = 0 by [lia]; subst.
    (* Show that [o_sub_merge_canon] isn't applicable. *)
    all: by efeed pose proof roff_canon_o_sub_wf.
  Qed.

  Theorem canon_wf' src dst : roff_canon src dst -> raw_offset_collapse src = dst.
  Proof.
    rewrite /raw_offset_wf /raw_offset_collapse => Hc;
    induction Hc => //=; rewrite ?IHHc /offset_seg_cons //=.
    { by [ rewrite decide_True //=; repeat (lia || f_equal)]. }
    all: repeat ((case_decide || case_match); destruct_and?; subst => //).
    by rewrite !right_id_L.
  Qed.

  Theorem canon_wf src dst : roff_canon src dst -> raw_offset_wf dst.
  Proof. intros ?%canon_wf_0. exact: canon_wf'. Qed.

  Definition raw_offset_merge (o1 o2 : raw_offset) : raw_offset :=
    raw_offset_collapse (o1 ++ o2).
  Arguments raw_offset_merge !_ _ /.

  Definition offset := {ro : raw_offset | raw_offset_wf ro}.
  Instance offset_eq_dec : EqDecision offset := _.

  #[local] Definition raw_offset_to_offset (ro : raw_offset) : option offset :=
    match decide (raw_offset_wf ro) with
    | left Hwf => Some (exist _ ro Hwf)
    | right _ => None
    end.
  Instance offset_countable : Countable offset.
  Proof.
    apply (inj_countable proj1_sig raw_offset_to_offset) => -[ro Hwf] /=.
    rewrite /raw_offset_to_offset; case_match => //.
    by rewrite (proof_irrel Hwf).
  Qed.

  Program Definition o_id : offset := [] ↾ _.
  Next Obligation. done. Qed.
  Program Definition mkOffset σ (ro : raw_offset_seg)
    (Hn0 : isnt ro (o_sub_ _ 0)) : offset :=
    [mk_offset_seg σ ro] ↾ singleton_raw_offset_wf _.
  Next Obligation.
    rewrite /mk_offset_seg; intros ? [] H => //=; repeat case_match => //.
  Qed.
  Definition o_field σ f : offset :=
    mkOffset σ (o_field_ f) I.
  Definition o_base σ derived base : offset :=
    mkOffset σ (o_base_ derived base) I.
  Definition o_derived σ base derived : offset :=
    mkOffset σ (o_derived_ base derived) I.
  Program Definition o_sub σ ty z : offset :=
    if decide (z = 0)%Z
    then o_id
    else mkOffset σ (o_sub_ ty z) _.
  Next Obligation. intros; case_match; simplify_eq/=; case_match; naive_solver. Qed.

  Lemma last_last_equiv {X} d {xs : list X} : default d (stdpp.list.last xs) = List.last xs d.
  Proof. elim: xs => // x1 xs /= <-. by case_match. Qed.
(*
  Section merge_elem.
    Context {X} (f : X -> X -> list X).
    Context (Hinv : ∀ x1 x2, merge_elems f (f x1 x2) = f x1 x2).

    #[global] Instance invol_merge_elems: Involutive (merge_elems f).
    Proof.
    Admitted.

    #[global] Instance invol_app_merge_elems: InvolApp (merge_elems f).
    Proof.
    Admitted.
  End merge_elem.
  #[local] Arguments merge_elems {X} f !_ /. *)

  Definition offset_seg_append : offset_seg -> raw_offset -> raw_offset :=
    offset_seg_cons.
(*
  Lemma offset_seg_cons_inv x1 x2 :
    raw_offset_collapse (offset_seg_cons x1 x2) = offset_seg_cons x1 x2.
  Proof.
    move=> /= [o1 off1] [o2 off2].
    destruct o1, o2 => //=; by repeat (case_decide; simpl).
  Qed. *)

  #[local] Definition test xs :=
    raw_offset_collapse (raw_offset_collapse xs) = raw_offset_collapse xs.

  Section tests.
    Ltac start := intros; red; simpl.
    Ltac step_true := rewrite ?decide_True //=.
    Ltac step_false := rewrite ?decide_False //=.
    Ltac res_true := start; repeat step_true.
    Ltac res_false := start; repeat step_false.

    Goal test []. Proof. res_true. Qed.
    Goal `{n1 <> 0 -> test [(o_sub_ ty n1, o1)] }.
    Proof. res_false; naive_solver. Qed.
    Goal `{n1 <> 0 -> n2 <> 0 -> n2 + n1 <> 0 -> test [(o_sub_ ty n1, o1); (o_sub_ ty n2, o2)] }.
    Proof. res_false; naive_solver. Qed.

    (* Goal `{test [(o_sub_ ty n1, o1); (o_sub_ ty n2, o2); (o_field_ f, o3)] }.
    Proof. res_true. Qed.

    Goal `{test [(o_field_ f, o1); (o_sub_ ty n1, o2); (o_sub_ ty n2, o3)] }.
    Proof. res_true. Qed.

    Goal `{ty1 ≠ ty2 → test [(o_sub_ ty1 n1, o1); (o_sub_ ty2 n2, o2); (o_field_ f, o3)] }.
    Proof. res_false. Qed.

    Goal `{ty1 ≠ ty2 → test [(o_sub_ ty1 n1, o1); (o_sub_ ty1 n2, o2); (o_sub_ ty2 n3, o3); (o_field_ f, o4)] }.
    Proof. start. step_false. step_true. step_false. Qed. *)
  End tests.

  (* This is probably sound, since it allows temporary underflows. *)
  (* Section eval_offset.
    (* From PTR_INTERNAL *)
    Definition eval_raw_offset (σ : genv) (o : raw_offset) : option Z :=
      foldr (liftM2 Z.add) (Some 0%Z) (eval_offset_seg σ <$> o).
    Definition eval_offset (σ : genv) (o : offset) : option Z := eval_raw_offset σ (`o).
  End eval_offset. *)

  Class InvolApp {X} (f : list X → list X) :=
    invol_app : ∀ xs1 xs2,
    f (xs1 ++ xs2) = f (f xs1 ++ f xs2).
  Class Involutive {X} (f : X → X) :=
    invol : ∀ x, f (f x) = f x.
  Instance raw_offset_collapse_involutive : Involutive raw_offset_collapse.
  Admitted.
  Instance raw_offset_collapse_invol_app : InvolApp raw_offset_collapse.
  Admitted.

  Program Definition o_dot : offset → offset → offset :=
    λ o1 o2, (raw_offset_merge (proj1_sig o1) (proj1_sig o2)) ↾ _.
  Next Obligation.
    move=> o1 o2 /=.
    exact: raw_offset_collapse_involutive.
  Qed.
  Inductive root_ptr : Set :=
  | nullptr_
  | global_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | alloc_ptr_ (a : alloc_id) (va : vaddr).

  #[local] Instance root_ptr_eq_dec : EqDecision root_ptr.
  Proof. solve_decision. Qed.
  Declare Instance root_ptr_countable : Countable root_ptr.

  #[local] Definition global_ptr_encode_canon
    (tu : translation_unit_canon) (o : obj_name) : option (alloc_id * vaddr) :=
    global_ptr_encode_ov o (tu !! o).

  Definition root_ptr_alloc_id (rp : root_ptr) : option alloc_id :=
    match rp with
    | nullptr_ => Some null_alloc_id
    | global_ptr_ tu o => fst <$> global_ptr_encode_canon tu o
    | alloc_ptr_ aid _ => Some aid
    end.

  Definition root_ptr_vaddr (rp : root_ptr) : option vaddr :=
    match rp with
    | nullptr_ => Some 0%N
    | global_ptr_ tu o => snd <$> global_ptr_encode_canon tu o
    | alloc_ptr_ aid va => Some va
    end.

  Inductive ptr_ : Set :=
  | invalid_ptr_
  | fun_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | offset_ptr (p : root_ptr) (o : offset).
  Definition ptr := ptr_.
  #[local] Instance ptr_eq_dec : EqDecision ptr.
  Proof. solve_decision. Qed.
  Declare Instance ptr_countable : Countable ptr.

  Definition ptr_alloc_id (p : ptr) : option alloc_id :=
    match p with
    | invalid_ptr_ => None
    | fun_ptr_ tu o => fst <$> global_ptr_encode_canon tu o
    | offset_ptr p o => root_ptr_alloc_id p
    end.

  Definition ptr_vaddr (p : ptr) : option vaddr :=
    match p with
    | invalid_ptr_ => None
    | fun_ptr_ tu o => snd <$> global_ptr_encode_canon tu o
    | offset_ptr p o =>
      foldr
        (λ off ova, ova ≫= offset_vaddr off)
        (root_ptr_vaddr p)
        (snd <$> `o)
    end.

  Definition lift_root_ptr (rp : root_ptr) : ptr := offset_ptr rp o_id.
  Definition invalid_ptr := invalid_ptr_.
  Definition fun_ptr tu o := fun_ptr_ (canonical_tu.tu_to_canon tu) o.

  Definition nullptr := lift_root_ptr nullptr_.
  Definition global_ptr (tu : translation_unit) o :=
    lift_root_ptr (global_ptr_ (canonical_tu.tu_to_canon tu) o).
  Definition alloc_ptr a oid := lift_root_ptr (alloc_ptr_ a oid).

  Lemma ptr_vaddr_nullptr : ptr_vaddr nullptr = Some 0%N.
  Proof. done. Qed.

  Instance id_dot : LeftId (=) o_id o_dot.
  Proof. intros o. apply /sig_eq_pi. by case: o. Qed.
  Instance dot_id : RightId (=) o_id o_dot.
  Proof.
    intros o. apply /sig_eq_pi.
    rewrite /= /raw_offset_merge (right_id []).
    by case: o.
  Qed.
  #[local] Instance dot_assoc : Assoc (=) o_dot.
  Proof.
    intros o1 o2 o3. apply /sig_eq_pi.
    move: o1 o2 o3 => [ro1 /= wf1]
      [ro2 /= wf2] [ro3 /= wf3].
      rewrite /raw_offset_merge.
      rewrite -{1}wf1 -{2}wf3.
      rewrite -!invol_app; f_equiv.
      apply: assoc.
  Qed.

  #[local] Instance ptr_eq_dec' : EqDecision ptr := ptr_eq_dec.

  (* Instance ptr_equiv : Equiv ptr := (=).
  Instance offset_equiv : Equiv offset := (=).
  Instance ptr_equivalence : Equivalence (≡@{ptr}) := _.
  Instance offset_equivalence : Equivalence (==@{offset}) := _.
  Instance ptr_equiv_dec : RelDecision (≡@{ptr}) := _.
  Instance offset_equiv_dec : RelDecision (==@{offset}) := _. *)

  (* Instance dot_assoc : Assoc (≡) o_dot := _. *)
  (* Instance dot_proper : Proper ((≡) ==> (≡) ==> (≡)) o_dot := _. *)


  Declare Scope ptr_scope.
  Bind Scope ptr_scope with ptr.
  Delimit Scope ptr_scope with ptr.

  Declare Scope offset_scope.
  Bind Scope offset_scope with offset.
  Delimit Scope offset_scope with offset.
  Notation "o1 .., o2" := (o_dot o1 o2) : offset_scope.

  Definition _offset_ptr (p : ptr) (o : offset) : ptr :=
    match p with
    | offset_ptr p' o' => offset_ptr p' (o' .., o)
    | invalid_ptr_ => invalid_ptr_ (* too eager! *)
    | fun_ptr_ _ _ =>
      match `o with
      | [] => p
      | _ => invalid_ptr_
      end
    end.
  Notation "p .., o" := (_offset_ptr p o) : ptr_scope.

  Lemma offset_ptr_id p : (p .., o_id = p)%ptr.
  Proof. case: p => // p o. by rewrite /_offset_ptr (right_id o_id o_dot). Qed.

  Lemma offset_ptr_dot p o1 o2 :
    (p .., (o1 .., o2) = p .., o1 .., o2)%ptr.
  Proof.
    destruct p; rewrite //= ?assoc //=.
    move: o1 o2 => [o1 /= +] [o2 /= +]; rewrite /raw_offset_wf => WF1 WF2.
    repeat (case_match; simplify_eq/= => //).
    by rewrite Heqr in WF2.
  Admitted.

  Lemma o_sub_0' σ ty :
    o_sub σ ty 0 = o_id.
  Proof. done. Qed.
  Lemma o_sub_0 σ ty :
    is_Some (size_of σ ty) ->
    o_sub σ ty 0 = o_id.
  Proof. done. Qed.

  Lemma ptr_alloc_id_offset {p o} :
    let p' := (p .., o)%ptr in
    is_Some (ptr_alloc_id p') -> ptr_alloc_id p' = ptr_alloc_id p.
  Proof. by destruct p, o as [[] ?] => //= /is_Some_None []. Qed.

  Axiom ptr_vaddr_o_sub_eq : forall p σ ty n1 n2 sz,
    size_of σ ty = Some sz -> (sz > 0)%N ->
    (same_property ptr_vaddr (p .., o_sub _ ty n1) (p .., o_sub _ ty n2) ->
    n1 = n2)%ptr.

  Lemma o_dot_sub σ (z1 z2 : Z) ty :
    (o_sub σ ty z1 .., o_sub σ ty z2 = o_sub σ ty (z1 + z2))%offset.
  Proof.
    intros. apply /sig_eq_pi => /=.
    rewrite /o_sub /= /mkOffset. repeat case_decide => //=.
    all: subst; try lia.
    all: rewrite ?Z.add_0_r ?Z.add_0_l.
    all: rewrite /mk_offset_seg /= /o_sub_off; case: size_of => [sz|] //=.
    all: try by rewrite decide_False //=; lia.
    - repeat (case_decide; try (lia || by auto)).
    - admit.
    - repeat (case_decide; try (lia || by auto)).
      repeat (lia || f_equiv).
    - admit.
  Admitted.

  Include PTRS_DERIVED_MIXIN.
End PTRS_IMPL.
