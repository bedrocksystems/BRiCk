(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From stdpp Require Import gmap.
From bedrock.lang.prelude Require Import base addr avl bytestring option numbers.

From bedrock.lang.cpp Require Import ast.
From bedrock.lang.cpp.semantics Require Import sub_module values.

Close Scope nat_scope.
Implicit Types (σ : genv).
Module canonical_tu.
  Definition im_to_gmap {V} (m : IM.t V) : gmap BS.t V :=
    list_to_map (map_to_list m).
  Definition symbol_table_canon : Set := gmap BS.t ObjValue.
  Definition type_table_canon : Set := gmap BS.t GlobDecl.

  Instance symbol_table_canon_eq_dec : EqDecision symbol_table_canon.
  Proof. solve_decision. Qed.
  Instance type_table_canon_eq_dec : EqDecision type_table_canon.
  Proof. solve_decision. Qed.

  Record translation_unit_canon : Set := Build_translation_unit_canon
  { symbols    : symbol_table_canon
  ; globals    : type_table_canon
  ; byte_order : endian
  }.
  Instance translation_unit_canon_eq_dec : EqDecision translation_unit_canon.
  Proof. solve_decision. Qed.

  Instance symbol_canon_lookup : Lookup obj_name ObjValue translation_unit_canon :=
    fun k m => m.(symbols) !! k.

  Record genv_canon : Set := Build_genv_canon
  { genv_tu : translation_unit_canon
    (* ^ the [translation_unit] *)
  ; pointer_size_bitsize : bitsize
    (* ^ the size of a pointer *)
  }.
  Instance genv_canon_eq_dec : EqDecision genv_canon.
  Proof. solve_decision. Qed.

  Definition tu_to_canon (tu : translation_unit) : translation_unit_canon :=
    let (s, g, bo) := tu in Build_translation_unit_canon (im_to_gmap s) (im_to_gmap g) bo.
  Local Definition genv_to_canon (σ : genv) : genv_canon :=
    let (tu, sz) := σ in Build_genv_canon (tu_to_canon tu) sz.
End canonical_tu.

Definition null_alloc_id : alloc_id := MkAllocId 0.
Definition invalid_alloc_id : alloc_id := MkAllocId 1.

(** Compute the actual raw offsets in Z. *)
Section eval_offset_seg.
  Context (σ : genv).
  Definition o_field_off (f : field) : option Z := offset_of σ f.(f_type) f.(f_name).
  Definition o_sub_off ty z : option Z := Z.mul z <$> (Z.of_N <$> size_of σ ty).
  Definition o_base_off derived base : option Z := parent_offset σ derived base.
  Definition o_derived_off base derived : option Z := Z.opp <$> parent_offset σ derived base.
End eval_offset_seg.

(*
Utility function, used to emulate [global_ptr] without a linker.
This is a really bad model and it'd fail a bunch of sanity checks.

Caveat: a model this to model [global_ptr] isn't correct, beyond proving
[global_ptr]'s isn't contradictory.
This model would fail proving that [global_ptr] is injective, that objects
are disjoint, or that
[global_ptr tu1 "staticR" |-> anyR T 1%Qp  ... ∗
  global_ptr tu2 "staticR" |-> anyR T 1%Qp  ...] actually holds at startup.
*)
Local Definition global_ptr_encode_ov (o : obj_name) (obj : option ObjValue) :
    option (alloc_id * vaddr) :=
  match obj with
  | Some _ => let p := Npos (encode o) in Some (MkAllocId p, p)
  | None => None
  end.

Module Import address_sums.
  Definition offset_vaddr : Z -> vaddr -> option vaddr := λ z pa,
    let sum : Z := (Z.of_N pa + z)%Z in
    guard (0 ≤ sum)%Z; Some (Z.to_N sum).

  Lemma offset_vaddr_eq z pa :
    let sum := (Z.of_N pa + z)%Z in
    (0 ≤ sum)%Z ->
    offset_vaddr z pa = Some (Z.to_N sum).
  Proof. rewrite /offset_vaddr/= => /= Hle. rewrite option_guard_True //. Qed.

  Lemma offset_vaddr_eq' {z pa} :
    offset_vaddr z pa <> None ->
    offset_vaddr z pa = Some (Z.to_N (Z.of_N pa + z)).
  Proof. rewrite /offset_vaddr/= => /=. case_option_guard; naive_solver. Qed.

  Lemma offset_vaddr_0 pa :
    offset_vaddr 0 pa = Some pa.
  Proof. rewrite offset_vaddr_eq Z.add_0_r ?N2Z.id //. lia. Qed.

  Lemma offset_vaddr_combine {pa o o'} :
    offset_vaddr o pa <> None ->
    offset_vaddr o pa ≫= offset_vaddr o' = offset_vaddr (o + o') pa.
  Proof.
    rewrite /offset_vaddr => Hval.
    by case_option_guard; rewrite /= Z.add_assoc ?Z2N.id.
  Qed.
End address_sums.

(*
A slightly better model might be something like the following, but we don't
bother defining this [Countable] instance. And this is not a great model
anyway. *)

(*
Declare Instance ObjValue_countable: Countable ObjValue.
Definition global_ptr (tu : translation_unit) (o : obj_name) : ptr :=
  let obj : option ObjValue := tu !! o in
  let p := Npos (encode obj) in (mkptr p p).
*)

Module Type PTRS_DERIVED_MIXIN (Import P : PTRS).
  Definition same_alloc : ptr -> ptr -> Prop := same_property ptr_alloc_id.
  Lemma same_alloc_eq : same_alloc = same_property ptr_alloc_id.
  Proof. done. Qed.

  Definition same_address : ptr -> ptr -> Prop := same_property ptr_vaddr.
  Lemma same_address_eq : same_address = same_property ptr_vaddr.
  Proof. done. Qed.

  Definition pinned_ptr_pure (va : vaddr) (p : ptr) := ptr_vaddr p = Some va.
  Lemma pinned_ptr_pure_eq :
    pinned_ptr_pure = fun (va : vaddr) (p : ptr) => ptr_vaddr p = Some va.
  Proof. done. Qed.
End PTRS_DERIVED_MIXIN.

Module Type PTRS_INTF := PTRS <+ PTRS_DERIVED.
(**
A simple consistency proof for [PTRS]; this one is inspired by Cerberus's
model of pointer provenance, and resembles CompCert's model.

Unlike [PTRS_IMPL], this model cannot be extended to support
[VALID_PTR_AXIOMS] because it collapses the structure of pointers.
*)
Module SIMPLE_PTRS_IMPL : PTRS_INTF.
  Import address_sums.
  Local Open Scope Z_scope.

  (**
  In this model, a pointer is either [invalid_ptr] (aka [None]) or a pair of
  a provenance and an address.

  We use [Z] for addresses to allow temporary underflows, but understand
  negative addresses as _invalid_. In this model (but not in general), all valid pointers have an address.
  *)
  Definition ptr' : Set := alloc_id * Z.
  Definition ptr : Set := option ptr'.

  Definition invalid_ptr : ptr := None.
  Definition mkptr a n : ptr := Some (a, n).
  Definition nullptr : ptr := mkptr null_alloc_id 0.

  Definition ptr_alloc_id : ptr -> option alloc_id := fmap fst.
  Definition ptr_vaddr : ptr -> option vaddr := λ p,
    '(_, va) ← p;
    guard 0 ≤ va;
    Some (Z.to_N va).

  Definition offset := option Z.
  Instance offset_eq_dec : EqDecision offset := _.
  Instance offset_countable : Countable offset := _.

  Declare Scope ptr_scope.
  Bind Scope ptr_scope with ptr.
  Delimit Scope ptr_scope with ptr.

  Declare Scope offset_scope.
  Bind Scope offset_scope with offset.
  Delimit Scope offset_scope with offset.

  Instance ptr_eq_dec : EqDecision ptr := _.
  Instance ptr_countable : Countable ptr := _.
  Definition ptr_eq_dec' := ptr_eq_dec.

  Lemma ptr_vaddr_nullptr : ptr_vaddr nullptr = Some 0%N.
  Proof. done. Qed.

  Definition o_id : offset := Some 0.
  Definition o_dot : offset → offset → offset := liftM2 Z.add.
  Notation "o1 .., o2" := (o_dot o1 o2) : offset_scope.

  Instance dot_id : RightId (=) o_id o_dot.
  Proof. case => [o|//] /=. by rewrite right_id_L. Qed.
  Instance id_dot : LeftId (=) o_id o_dot.
  Proof. case => [o|//] /=. by rewrite left_id_L. Qed.
  Instance dot_assoc : Assoc (=) o_dot.
  Proof. case => [x|//] [y|//] [z|//] /=. by rewrite assoc. Qed.

  (**
  [_offset_ptr] is basically [Z.add] lifted over a couple of functors.
  However, we perform the lifting in 2 stages. *)
  (*
   *** The first layer takes offsets in [Z] instead of [offset := option Z].
   This layer, with its associated lemmas, is useful after case analysis on [offset].
   *)
  Definition offset_ptr_raw : Z -> ptr -> ptr :=
    λ z p, p ≫= (λ '(aid, pa), Some (aid, z + pa)).

  (* Raw versions of [offset_ptr_id], [offset_ptr_dot]. *)
  Lemma offset_ptr_raw_id p : offset_ptr_raw 0 p = p.
  Proof. by case: p => [[a p]|]. Qed.

  Lemma offset_ptr_raw_dot {p o o'} :
    offset_ptr_raw o' (offset_ptr_raw o p) = offset_ptr_raw (o + o') p.
  Proof. case: p => [[a v]|//] /=. by rewrite assoc_L (comm_L _ o o'). Qed.

  (** Conveniences over [offset_ptr_raw_dot]. *)
  Lemma offset_ptr_raw_cancel {p} {o1 o2 : Z} o3
    (Hsum : o1 + o2 = o3) :
    offset_ptr_raw o2 (offset_ptr_raw o1 p) = (offset_ptr_raw o3 p).
  Proof. by rewrite offset_ptr_raw_dot Hsum. Qed.

  Lemma offset_ptr_raw_cancel0 (o1 o2 : Z) p
    (Hsum : o1 + o2 = 0) :
    offset_ptr_raw o2 (offset_ptr_raw o1 p) = p.
  Proof. by rewrite (offset_ptr_raw_cancel 0 Hsum) offset_ptr_raw_id. Qed.

  (* *** The second layer encapsulates case analysis on [ptr]. *)
  Definition _offset_ptr : ptr -> offset -> ptr :=
    λ p oz, z ← oz; offset_ptr_raw z p.
  Notation "p .., o" := (_offset_ptr p o) : ptr_scope.
  Local Open Scope ptr_scope.

  Lemma offset_ptr_id p : p .., o_id = p.
  Proof. apply offset_ptr_raw_id. Qed.

  Lemma offset_ptr_dot p o1 o2 :
    p .., (o1 .., o2) = p .., o1 .., o2.
  Proof. destruct o1, o2 => //=. apply symmetry, offset_ptr_raw_dot. Qed.

  Lemma ptr_alloc_id_offset {p o} :
    let p' := p .., o in
    is_Some (ptr_alloc_id p') ->
    ptr_alloc_id p' = ptr_alloc_id p.
  Proof. move=> /= -[aid]. by case: o p => [?|] [[??]|] /=. Qed.

  Definition o_field σ f : offset := o_field_off σ f.
  Definition o_sub σ ty z : offset := o_sub_off σ ty z.
  Definition o_base σ derived base := o_base_off σ derived base.
  Definition o_derived σ base derived := o_derived_off σ base derived.

  Lemma o_base_derived_raw σ p derived base :
    (p .., o_base σ derived base)%ptr <> invalid_ptr ->
    (p .., o_base σ derived base .., o_derived σ base derived = p)%ptr.
  Proof.
    rewrite /o_base /o_base_off /o_derived /o_derived_off.
    case: parent_offset => [o|//] /= Hval. apply offset_ptr_raw_cancel0. lia.
  Qed.

  Lemma o_derived_base_raw σ p derived base :
    (p .., o_derived σ base derived)%ptr <> invalid_ptr ->
    (p .., o_derived σ base derived .., o_base σ derived base = p)%ptr.
  Proof.
    rewrite /o_base /o_base_off /o_derived /o_derived_off.
    case: parent_offset => [o|//] /= Hval. apply: offset_ptr_raw_cancel0. lia.
  Qed.

  Lemma o_sub_sub_raw σ p ty n1 n2 :
    (p .., o_sub σ ty n1 .., o_sub σ ty n2 = p .., o_sub σ ty (n1 + n2))%ptr.
  Proof.
    rewrite /o_sub /o_sub_off. case: size_of => [o|//] /=.
    apply: offset_ptr_raw_cancel. lia.
  Qed.

  Lemma o_sub_0 σ ty :
    is_Some (size_of σ ty) ->
    o_sub σ ty 0 = o_id.
  Proof. rewrite /o_sub /o_sub_off => -[? ->] //=. Qed.

  Lemma o_dot_sub {σ : genv} i j ty :
    o_dot (o_sub _ ty i) (o_sub _ ty j) = o_sub _ ty (i + j).
  Proof.
    rewrite /o_sub /o_sub_off; case: size_of => //= sz. f_equiv. lia.
  Qed.

  (* Caveat: This model of [global_ptr] isn't correct, beyond proving
  [global_ptr]'s isn't contradictory.
  This model would fail proving that [global_ptr] is injective, that objects
  are disjoint, or that
  [global_ptr tu1 "staticR" |-> anyR T 1%Qp  ... ∗
   global_ptr tu2 "staticR" |-> anyR T 1%Qp  ...] actually holds at startup.
  *)
  Definition global_ptr (tu : translation_unit) (o : obj_name) : ptr :=
    '(aid, va) ← global_ptr_encode_ov o (tu !! o);
    Some (aid, Z.of_N va).

  Definition fun_ptr := global_ptr.

  Lemma ptr_vaddr_o_sub_eq p σ ty n1 n2 sz
    (Hsz : size_of σ ty = Some sz) (Hsz0 : (sz > 0)%N) :
    (same_property ptr_vaddr (p .., o_sub σ ty n1) (p .., o_sub σ ty n2) ->
    n1 = n2)%ptr.
  Proof.
    rewrite same_property_iff /ptr_vaddr /o_sub /o_sub_off Hsz => -[addr []] /=.
    case: p => [[aid va]|] Haddr ?; simplify_option_eq. nia.
  Qed.

  Include PTRS_DERIVED_MIXIN.

  (* Not exposed directly, but proof sketch for
  [valid_o_sub_size]; recall that in this model, all valid pointers have an
  address. *)
  Lemma raw_valid_o_sub_size σ p ty i :
    is_Some (ptr_vaddr (p .., o_sub σ ty i)) ->
    is_Some (size_of σ ty).
  Proof. rewrite /o_sub /o_sub_off. case: size_of=> //. by eexists. Qed.
End SIMPLE_PTRS_IMPL.

Module Import merge_elems.
Section merge_elem.
  Context {X} (f : X -> X -> list X).
  Definition merge_elem (x0 : X) (xs : list X) : list X :=
    match xs with
    | x1 :: xs' => f x0 x1 ++ xs'
    | [] => [x0]
    end.
  Lemma merge_elem_nil x0 : merge_elem x0 [] = [x0].
  Proof. done. Qed.
  Lemma merge_elem_cons x0 x1 xs : merge_elem x0 (x1 :: xs) = f x0 x1 ++ xs.
  Proof. done. Qed.

  Definition merge_elems_aux : list X -> list X -> list X := foldr merge_elem.
  Local Arguments merge_elems_aux _ !_ /.
  Definition merge_elems : list X -> list X := merge_elems_aux [].
  Local Arguments merge_elems !_ /.
  Lemma merge_elems_cons x xs :
    merge_elems (x :: xs) = merge_elem x (merge_elems xs).
  Proof. done. Qed.
  Lemma merge_elems_aux_app ys xs1 xs2 :
    merge_elems_aux ys (xs1 ++ xs2) = merge_elems_aux (merge_elems_aux ys xs2) xs1.
  Proof. apply foldr_app. Qed.
  Lemma merge_elems_app xs1 xs2 :
    merge_elems (xs1 ++ xs2) = merge_elems_aux (merge_elems xs2) xs1.
  Proof. apply merge_elems_aux_app. Qed.
End merge_elem.
End merge_elems.

(**
Another (incomplete) consistency proof for [PTRS], based on Krebbers' PhD thesis, and
other formal models of C++ using structured pointers.
This is more complex than [SIMPLE_PTRS_IMPL], but will be necessary to justify [VALID_PTR_AXIOMS].

In this model, all valid pointers are pinned, but this is not meant
to be guaranteed, and is indeed not guaranteed by the other model.
*)
Module PTRS_IMPL : PTRS_INTF.
  Import canonical_tu.

  Inductive raw_offset_seg : Set :=
  | o_field_ (* type-name: *) (f : field)
  | o_sub_ (ty : type) (z : Z)
  | o_base_ (derived base : globname)
  | o_derived_ (base derived : globname)
  | o_invalid_.
  Local Instance raw_offset_seg_eq_dec : EqDecision raw_offset_seg.
  Proof. solve_decision. Qed.
  Declare Instance raw_offset_seg_countable : Countable raw_offset_seg.

  Definition offset_seg : Set := raw_offset_seg * Z.
  Local Instance offset_seg_eq_dec : EqDecision offset_seg := _.
  Local Instance offset_seg_countable : Countable offset_seg := _.

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
  Local Instance raw_offset_eq_dec : EqDecision offset := _.
  Local Instance raw_offset_countable : Countable raw_offset := _.

  Notation isnt o pattern :=
    (match o with | pattern => False | _ => True end).

  Implicit Types (z : Z).
  (* Close Scope nat_scope. *)
  Local Open Scope Z_scope.
  Section roff_canon.
    (* Context {σ : genv}. *)

    (* Ugh, big-step or small-step normalization. *)
    Inductive roff_canon : list raw_offset_seg -> list raw_offset_seg -> Prop :=
    | o_nil :
      roff_canon [] []
    | o_field_canon s d f :
      (* is_Some (o_field_off σ f) -> *) (* not canonicalization's problem? *)
      roff_canon s d ->
      roff_canon (o_field_ f :: s) (o_field_ f :: d)
    | o_base_canon s d base derived :
      isnt d (o_derived_ _ _ :: _) ->
      roff_canon s d ->
      roff_canon (o_base_ derived base :: s) (o_base_ derived base :: d)
    (* should paths start from the complete object? If
    yes, as done by Ramananandro [POPL 2012],
    o_derived should just cancel out o_base, and this should be omitted. *)
    (* | o_derived_wf s d derived base :
      isnt d (o_base_ _ _ :: d) ->
      roff_canon s d ->
      roff_canon (o_derived_ base derived :: s) (o_derived_ base derived :: d) *)
    | o_derived_cancel_canon s d derived base :
      roff_canon s d ->
      (* This premise is a hack, but without it, normalization might not be deterministic. Thankfully, paths can't contain o_derived step, so we're good! *)
      (* roff_canon (o_base_ derived base :: s) (o_base_ derived base :: d) -> *)
      roff_canon (o_derived_ base derived :: o_base_ derived base :: s) d
    | o_sub_canon s d ty1 z :
      match d with
      | (o_sub_ ty2 _ :: _) => ty1 <> ty2
      | _ => True
      end ->
      0 < z ->
      (* isnt o (o_sub_ _ _) *)
      roff_canon s d ->
      roff_canon (o_sub_ ty1 z :: s) (o_sub_ ty1 z :: d)
    | o_sub_merge_canon s d ty z1 z2 :
      0 < z1 + z2 ->
      roff_canon s (o_sub_ ty z1 :: d) ->
      roff_canon (o_sub_ ty z2 :: s) (o_sub_ ty (z1 + z2) :: d)
    .
  End roff_canon.

  Lemma roff_canon_o_base_inv s d derived base :
    roff_canon (o_base_ derived base :: s) (o_base_ derived base :: d) ->
    roff_canon s d.
  Proof. inversion 1; auto. Qed.

  Lemma roff_canon_o_sub_wf s d ty z :
    roff_canon s (o_sub_ ty z :: d) ->
    0 < z.
  Proof.
    move E: (o_sub_ _ _ :: _) => d' Hcn.
    elim: Hcn E; naive_solver.
  Qed.
  Lemma roff_canon_o_sub_no_dup s d o ty1 z :
    roff_canon s (o_sub_ ty1 z :: o :: d) ->
    match o with
    | o_sub_ ty2 _ => ty1 <> ty2
    | _ => True
    end.
  Proof.
    (* inversion 1 => //; case_match; simplify_eq/=; try naive_solver. *)
    move E: (o_sub_ _ _ :: _) => d' Hcn.
    elim: Hcn z E; naive_solver.
  Qed.

  Lemma foo_o_base_cancel_wf s d derived base :
    roff_canon (o_derived_ base derived :: s) (o_derived_ base derived :: d) ->
    roff_canon s d.
  Proof. intros H.
  (* dependent induction H; eauto. *)
    inversion H; subst; eauto using roff_canon_o_base_inv.
    Fail Qed.
    Abort.

  (* Lemma foo_o_derived_cancel_wf' o s d :
    roff_canon (o :: s) (o :: d) ->
    roff_canon s d.
  Proof. inversion 1; subst; eauto using foo_o_derived_cancel_wf. apply foo_o_derived_cancel_wf in H3. Qed. *)


  Definition offset_seg_merge (os1 os2 : offset_seg) : list offset_seg :=
    match os1, os2 with
    | (o_sub_ ty1 n1, off1), (o_sub_ ty2 n2, off2) =>
      if decide (ty1 = ty2)
      then [(o_sub_ ty1 (n2 + n1), (off1 + off2)%Z)]
      else [os2; os1]
    | (o_base_ der1 base1, off1), (o_derived_ base2 der2, off2) =>
      if decide (der1 = der2 ∧ base1 = base2)
      then []
      else [os2; os1]
    | (o_invalid_, _), _ => [(o_invalid_, 0%Z)]
    | _, _ => [os2; os1]
    end.

  Definition raw_offset_collapse : raw_offset -> raw_offset :=
    merge_elems (flip offset_seg_merge).
  Arguments raw_offset_collapse !_ /.
  Definition raw_offset_wf (ro : raw_offset) : Prop :=
    raw_offset_collapse ro = ro.
  Instance raw_offset_wf_pi ro : ProofIrrel (raw_offset_wf ro) := _.
  Lemma singleton_raw_offset_wf {os} : raw_offset_wf [os].
  Proof. done. Qed.

  Hint Constructors roff_canon : core.
  Theorem canon_wf_0 src dst :
    roff_canon src dst ->
    roff_canon dst dst.
  Proof.
    intros Hrc; induction Hrc; eauto.
    inversion IHHrc; subst; first naive_solver.
    (* Show that [o_sub_merge_canon] isn't applicable. *)
    have ?: z0 = 0 by [lia]; subst.
    by efeed pose proof roff_canon_o_sub_wf.
  Qed.

  (* Theorem canon_wf_keep o src dst :
    roff_canon (o :: src) (o :: dst) ->
    roff_canon src dst.
  Proof.
    move E1: (_ :: src) => s1.
    move E2: (_ :: dst) => s2 Hrc.
    move: Hrc o src dst E1 E2.
    induction 1; intros; simplify_eq/=; eauto.
    - *)
    (* destruct dst => //.
    admit.
    econstructor. *)
    (* rewrite Z.add_0_l.
    clear H4. have {H2} Hz1 : 0 < z1 by lia.
    constructor => //.
    destruct d. admit.
    destruct d.
    econstructor.
    rewrite left_id_L.
    eauto.
    inversion H6; simplify_eq/=; try naive_solver.
    inversion Hrc; simplify_eq/=; try naive_solver.
    destruct d. admit.
    inversion Hfoo; simplify_eq/=; try naive_solver.
    econstructor => //. *)

  (* Lemma foo ty z1 dst r rs (Hgt : 0 < z1) :
    raw_offset_wf (zip (o_sub_ ty z1 :: dst) (r :: rs)) ->
    raw_offset_wf (zip dst rs).
  Proof.
    rewrite /raw_offset_wf /raw_offset_collapse.
      rewrite /merge_elem /=.
      case: merge_elems => [|o os] IH; simplify_eq/=. by destruct zip.

      destruct o as [[] ?]; simplify_eq/=; try by rewrite -IH.
      case_decide; simplify_eq/=; repeat (lia || f_equal || done).
  Admitted. *)

  Theorem canon_wf src dst rs : roff_canon src dst -> raw_offset_wf (zip dst rs).
  Proof.
    rewrite /raw_offset_wf /raw_offset_collapse => /canon_wf_0 Hc.
    move: Hc rs; induction 1 => // {Hc} -[//|r rs] /=; rewrite ?IHHc /=;
      try by rewrite /merge_elem /offset_seg_merge /=; repeat case_match.
    - case_match => //. destruct rs => //.
      case_match => //=. by rewrite decide_False.
    - (* Idea: invert the result of normalizing [o_sub ty z1 :: d], and show
      that [o_sub ty (z1 + z2) :: d] normalizes the same way. *)
      move: IHHc => /(_ (r :: rs)).

      rewrite /merge_elem /=.
      case: merge_elems => [|o os] IH; simplify_eq/=. by destruct zip.

      destruct o as [[] ?]; simplify_eq/=; try by rewrite -IH.
      case_decide; simplify_eq/=; repeat (lia || f_equal). done.
  Qed.
(*
    move: IHHc => /(_ (r :: rs)) /foo.
    rewrite /raw_offset_wf /raw_offset_collapse.

      rewrite /merge_elem /= => IH. rewrite -IH. move: IH.
      case: merge_elems => //=.
      => [|o os] IH; simplify_eq/=. by destruct zip.

      destruct o as [[] ?]; simplify_eq/=; try by rewrite -IH.
      case_decide; simplify_eq/=; repeat (lia || f_equal). done.


        rewrite H0.
        f_equiv.
        lia.
        repeat f_equiv => //.
        repeat case_match; simplify_eq/=.
        destruct o.
        congruence.
        destruct zs, d => //=.
      repeat case_match.
      inversion Hc; subst.
      +  case_match => //. destruct zs => //=.
        case_match => //=. by rewrite decide_False.
      destruct d, zs; simplify_eq/=.
        case_match.
      admit.
      {
        rewrite /merge_elem. IHHc.
        destruct d as [|[] ds] => //=; eauto.
        case: zs d IHhc Hc H => //= [|z1 zs] [|? d].
      by rewrite /merge_elem /offset_seg_merge /=; repeat case_match. }
      rewrite /merge_elem /=.
      case E: merge_elems => [|os oss]; simplify_eq.
      -
      (* destruct d as [|? [|? d]], zs as [|? [|? zs]]; simplify_eq/= =>//. *)
      admit.
      -
      simpl in IHHc.
      rewrite /offset_seg_merge; simplify_eq/=.
      specialize
      destruct d as [|d0 d], zs as [|z zs] => //=.
      repeat case_match => //; subst; simplify_eq/=.
      rewrite /= -E. *)

    (* elim: dst src Hc zs => [//|d dst IHdst] src Hc [//|z zs] /=.
    inversion Hc; subst => //; rewrite (IHdst s) //.
      all: try by rewrite /merge_elem /offset_seg_merge /=; repeat case_match. *)

    (* - rewrite (IHdst s);
      by rewrite /merge_elem /offset_seg_merge /=; repeat case_match.
    -
      rewrite (IHdst s) //.
        by rewrite /merge_elem /offset_seg_merge /=; repeat case_match.
    -
    inversion H3; subst => //.
      + rewrite (IHdst s0) //.
        by rewrite /merge_elem /offset_seg_merge /=; repeat case_match.
      +
        rewrite (IHdst s0) //.
      econstructor.
      by .

    induction 1 => -[//|z zs] /=. {
      rewrite IHHc /=.
      rewrite /merge_elem /= /offset_seg_merge.
      repeat case_match => //.
    }
    rewrite IHHc /=. *)


  Definition raw_offset_merge (o1 o2 : raw_offset) : raw_offset :=
    raw_offset_collapse (o1 ++ o2).
  Arguments raw_offset_merge !_ _ /.

  Definition offset := {ro : raw_offset | raw_offset_wf ro}.
  Instance offset_eq_dec : EqDecision offset := _.

  Local Definition raw_offset_to_offset (ro : raw_offset) : option offset :=
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
  Program Definition mkOffset σ (ro : raw_offset_seg) : offset :=
    [mk_offset_seg σ ro] ↾ singleton_raw_offset_wf.
  Definition o_field σ f : offset :=
    mkOffset σ (o_field_ f).
  Definition o_sub σ ty z : offset :=
    mkOffset σ (o_sub_ ty z).
  Definition o_base σ derived base : offset :=
    mkOffset σ (o_base_ derived base).
  Definition o_derived σ base derived : offset :=
    mkOffset σ (o_derived_ base derived).

  Lemma last_last_equiv {X} d {xs : list X} : default d (stdpp.list.last xs) = List.last xs d.
  Proof. elim: xs => // x1 xs /= <-. by case_match. Qed.

  Class InvolApp {X} (f : list X → list X) :=
    invol_app : ∀ xs1 xs2,
    f (xs1 ++ xs2) = f (f xs1 ++ f xs2).
  Class Involutive {X} (f : X → X) :=
    invol : ∀ x, f (f x) = f x.

  Section merge_elem.
    Context {X} (f : X -> X -> list X).
    Context (Hinv : ∀ x1 x2, merge_elems f (f x1 x2) = f x1 x2).

    Global Instance invol_merge_elems: Involutive (merge_elems f).
    Proof.
    Admitted.

    Global Instance invol_app_merge_elems: InvolApp (merge_elems f).
    Proof.
    Admitted.
  End merge_elem.
  Local Arguments merge_elems {X} f !_ /.
  Instance raw_offset_collapse_involutive : Involutive raw_offset_collapse := _.

  Definition offset_seg_append : offset_seg -> raw_offset -> raw_offset :=
    merge_elem (flip offset_seg_merge).

  Lemma offset_seg_merge_inv :
    let f := (flip offset_seg_merge) in
    ∀ x1 x2, raw_offset_collapse (f x1 x2) = f x1 x2.
  Proof.
    move=> /= [o1 off1] [o2 off2].
    destruct o1, o2 => //=; by repeat (case_decide; simpl).
  Qed.

  Local Definition test xs :=
    raw_offset_collapse (raw_offset_collapse xs) = raw_offset_collapse xs.

  Section tests.
    Ltac start := intros; red; simpl.
    Ltac step_true := rewrite ?decide_True //=.
    Ltac step_false := rewrite ?decide_False //=.
    Ltac res_true := start; repeat step_true.
    Ltac res_false := start; repeat step_false.

    Goal test []. Proof. res_true. Qed.
    Goal `{test [(o_sub_ ty n1, o1)] }. Proof. done. Qed.
    Goal `{test [(o_sub_ ty n1, o1); (o_sub_ ty n2, o2)] }.
    Proof. res_true. Qed.

    Goal `{test [(o_sub_ ty n1, o1); (o_sub_ ty n2, o2); (o_field_ f, o3)] }.
    Proof. res_true. Qed.

    Goal `{test [(o_field_ f, o1); (o_sub_ ty n1, o2); (o_sub_ ty n2, o3)] }.
    Proof. res_true. Qed.

    Goal `{ty1 ≠ ty2 → test [(o_sub_ ty1 n1, o1); (o_sub_ ty2 n2, o2); (o_field_ f, o3)] }.
    Proof. res_false. Qed.

    Goal `{ty1 ≠ ty2 → test [(o_sub_ ty1 n1, o1); (o_sub_ ty1 n2, o2); (o_sub_ ty2 n3, o3); (o_field_ f, o4)] }.
    Proof. start. step_false. step_true. step_false. Qed.
  End tests.

  (* This is probably sound, since it allows temporary underflows. *)
  (* Section eval_offset.
    (* From PTR_INTERNAL *)
    Definition eval_raw_offset (σ : genv) (o : raw_offset) : option Z :=
      foldr (liftM2 Z.add) (Some 0%Z) (eval_offset_seg σ <$> o).
    Definition eval_offset (σ : genv) (o : offset) : option Z := eval_raw_offset σ (`o).
  End eval_offset. *)

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

  Local Instance root_ptr_eq_dec : EqDecision root_ptr.
  Proof. solve_decision. Qed.
  Declare Instance root_ptr_countable : Countable root_ptr.

  Local Definition global_ptr_encode_canon
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
  Local Instance ptr_eq_dec : EqDecision ptr.
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
  Local Instance dot_assoc : Assoc (=) o_dot.
  Proof.
    intros o1 o2 o3. apply /sig_eq_pi.
    move: o1 o2 o3 => [ro1 /= wf1]
      [ro2 /= wf2] [ro3 /= wf3].
      rewrite /raw_offset_merge.
      rewrite -{1}wf1 -{2}wf3.
      rewrite -!invol_app; f_equiv.
      apply: assoc.
  Qed.

  Local Instance ptr_eq_dec' : EqDecision ptr := ptr_eq_dec.

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
    | invalid_ptr_ => invalid_ptr_
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

  (* XXX False. *)
  Lemma o_sub_0 σ ty :
    is_Some (size_of σ ty) ->
    o_sub σ ty 0 = o_id.
  Proof. rewrite /o_sub/o_id/=. Admitted.

  Lemma ptr_alloc_id_offset {p o} :
    let p' := (p .., o)%ptr in
    is_Some (ptr_alloc_id p') -> ptr_alloc_id p' = ptr_alloc_id p.
  Admitted.

  Axiom ptr_vaddr_o_sub_eq : forall p σ ty n1 n2 sz,
    size_of σ ty = Some sz -> (sz > 0)%N ->
    (same_property ptr_vaddr (p .., o_sub _ ty n1) (p .., o_sub _ ty n2) ->
    n1 = n2)%ptr.

  Lemma o_dot_sub σ (z1 z2 : Z) ty :
    (o_sub σ ty z1 .., o_sub σ ty z2 = o_sub σ ty (z1 + z2))%offset.
  Proof.
    intros. apply /sig_eq_pi => /=.
    rewrite /mk_offset_seg /= /o_sub_off /=;
      case: size_of => [sz|] //=; rewrite decide_True //=.
    by rewrite -Z.mul_add_distr_r (comm_L _ z2).
  Qed.

  Include PTRS_DERIVED_MIXIN.
End PTRS_IMPL.
