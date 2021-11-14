(**
 * Copyright (c) 2021 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From stdpp Require Export finite.
From bedrock.prelude Require Import base bool numbers list_numbers gmap list.

#[local] Open Scope N_scope.

(**
Extensions of [stdpp.finite], especially for variants:

From the [Finite] typeclass, like from Haskell's [Enum], one can generate
conversion to and from [N], both for individual elements and bitsets of them.
*)

Lemma subset_of_enum `{Finite A} xs :
  xs ⊆ enum A.
Proof. intros x _. apply elem_of_enum. Qed.

Definition encode_N `{Countable A} (x : A) : N :=
  Pos.pred_N (encode x).
Definition decode_N `{Countable A} (i : N) : option A :=
  decode (N.succ_pos i).
Section countable.
  Context `{Countable A}.
  Implicit Type (x : A).

  #[global] Instance encode_N_inj : Inj (=) (=) (encode_N (A:=A)).
  Proof. unfold encode_N; intros x y Hxy; apply (inj encode); lia. Qed.
  Lemma decode_encode_N x : decode_N (encode_N x) = Some x.
  Proof. rewrite /decode_N /encode_N N_succ_pos_pred. apply decode_encode. Qed.

  Lemma encode_nat_N x : encode_nat x = N.to_nat (encode_N x).
  Proof. rewrite /encode_nat /encode_N. lia. Qed.

  Lemma encode_N_nat x : encode_N x = N.of_nat (encode_nat x).
  Proof. by rewrite encode_nat_N N2Nat.id. Qed.
  Lemma decode_nat_N i : decode_nat i =@{option A} decode_N (N.of_nat i).
  Proof. by rewrite /decode_nat Pos_of_S. Qed.
  Lemma decode_N_nat i : decode_N i =@{option A} decode_nat (N.to_nat i).
  Proof. by rewrite decode_nat_N N2Nat.id. Qed.
End countable.

Definition card_N A `{Finite A} : N := N.of_nat $ card A.

Section finite.
  Context `{Finite A}.
  Implicit Type (x : A).

  (* Unfolding lemma: pretty annoying to prove inline by unfolding. *)
  Lemma finite_decode_nat_unfold n :
    decode_nat n = enum A !! n.
  Proof. apply (f_equal (flip lookup (enum _))). lia. Qed.

  (* To upstream! Missing companion to [encode_lt_card]. *)
  Lemma finite_decode_nat_lt n x :
    decode_nat n = Some x → (n < card A)%nat.
  Proof. rewrite finite_decode_nat_unfold /card. apply lookup_lt_Some. Qed.

  (** Lift the above lemmas *)
  Lemma finite_decode_N_unfold n :
    decode_N n = enum A !! N.to_nat n.
  Proof. by rewrite decode_N_nat finite_decode_nat_unfold. Qed.

  Lemma finite_decode_N_lt n x :
    decode_N n = Some x → n < card_N A.
  Proof. rewrite /card_N decode_N_nat => /finite_decode_nat_lt. lia. Qed.

  Lemma encode_N_lt_card x : encode_N x < card_N A.
  Proof. rewrite encode_N_nat. apply N_of_nat_lt_mono, encode_lt_card. Qed.

  Lemma encode_decode_N (i : N) :
    i < card_N A →
    ∃ x : A, decode_N i = Some x ∧ encode_N x = i.
  Proof.
    rewrite /card_N -{1}(N2Nat.id i). intros Hle%N_of_nat_lt_mono.
    have [x [Hdec Henc]] := encode_decode A (N.to_nat i) Hle.
    exists x. rewrite decode_nat_N encode_nat_N N2Nat.id in Hdec Henc.
    by apply (inj N.to_nat) in Henc.
  Qed.

  (** A partial inverse to [decode_encode_N]: if [decode_N] succeeds, we can
  [encode_N] the result back. *)
  Lemma decode_N_Some_encode_N (n : N) (x : A)
    (Hdec : decode_N n = Some x) : encode_N x = n.
  Proof.
    pose proof (finite_decode_N_lt _ _ Hdec) as Hcmp.
    destruct (encode_decode_N _ Hcmp) as (x' & ?Hdec & Henc).
    naive_solver.
  Qed.
End finite.

(* From (pieces of) [Countable] (and more) to [Finite]. *)
Section enc_finite.
  #[local] Close Scope N_scope.
  Context `{EqDecision A}.
  Context (to_nat : A → nat) (of_nat : nat → A) (c : nat).
  Context (of_to_nat : ∀ x, of_nat (to_nat x) = x).
  Context (to_nat_c : ∀ x, to_nat x < c).
  Context (to_of_nat : ∀ i, i < c → to_nat (of_nat i) = i).

  (* Unfolding lemma for enc_finite. *)
  Lemma enc_finite_enum :
    @enum _ _ (enc_finite to_nat of_nat c of_to_nat to_nat_c to_of_nat) = of_nat <$> seq 0 c.
  Proof. done. Qed.
End enc_finite.

(** Lift enc_finite to [N] *)
Section enc_finite_N.
  Context `{Inhabited A}.
  Context `{EqDecision A}.
  Context (to_N : A → N) (of_N : N → option A) (c : N).
  Context (of_to_N : ∀ x, of_N (to_N x) = Some x).

  Context (to_N_c : ∀ x, to_N x < c).
  Context (to_of_N : ∀ i, i < c → to_N (default inhabitant $ of_N i) = i).

  #[program] Definition enc_finite_N : Finite A :=
    enc_finite (N.to_nat ∘ to_N) ((λ x, default inhabitant (of_N x)) ∘ N.of_nat) (N.to_nat c) _ _ _.
  Next Obligation. move=> /= x. by rewrite N2Nat.id of_to_N. Qed.
  Next Obligation. move=> /= x. have := to_N_c x. lia. Qed.
  Next Obligation. move=> /= x Hle. rewrite to_of_N; lia. Qed.
End enc_finite_N.

(** Useful to prove NoDup when lifting [Finite] over constructor [f]. *)
Lemma NoDup_app_fmap_l {A B} `{Finite A} (f : A -> B) xs :
  Inj eq eq f →
  NoDup xs →
  (∀ x : B, x ∈ f <$> enum A → x ∉ xs) →
  NoDup ((f <$> enum A) ++ xs).
Proof.
  intros. rewrite NoDup_app. by split_and!; first apply /NoDup_fmap_2 /NoDup_enum.
Qed.

(**
Module-based infrastructure to generate Finite-based utilities.

Example use for a variant.

Module right.
  Variant _t := FOO | BAR.
  Definition t := _t. (* Workaround Coq bug. *)
  #[global] Instance t_inh : Inhabited t.
  Proof. exact (populate ...). Qed.
  #[global] Instance t_eqdec : EqDecision t.
  Proof. solve_decision. Defined.

  #[global,program] Instance t_finite : Finite t :=
  { enum := [FOO; BAR] }.
  Next Obligation. solve_finite_nodup. Qed.
  Next Obligation. solve_finite_total. Qed.

  (* Option 1: specify [to_N] by hand:  *)
  Definition to_N : t -> N := ..

  (* get a specialized copy of [of_N] and [of_to_N]. *)
  Include finite_encoded_type_mixin.

  (* Option 2 (alternative to 1):
  INSTEAD OF defining [to_N], obtain it from [Finite], together with various
  other parts of an encoding into bitmasks.
  *)
  Include simple_finite_bitmask_type_mixin.

  (* [simple_finite_bitmask_type_mixin] can almost be replaced by (some subset of), but
  enjoys extra lemmas. *)
  Include finite_type_mixin.
  Include bitmask_type_simple_mixin.
  Include finite_bitmask_type_mixin.
End right.

(* For bitmasks over [simple_finite_bitmask_type_intf]. *)
Module rights := simple_finite_bits rights.
(* Else, for bitmasks over [finite_bitmask_type_intf]. *)
Module rights := finite_bits rights.
*)
Module Type eqdec_type.
  Parameter t : Type.
  #[global] Declare Instance t_inh : Inhabited t.
  #[global] Declare Instance t_eqdec : EqDecision t.
End eqdec_type.

Module Type finite_type <: eqdec_type.
  Include eqdec_type.
  #[global] Declare Instance t_finite : Finite t.
End finite_type.

(**
To define [finite_type] for enums, the following will work:

<<
#[global,program] Instance t_finite : Finite t :=
{ enum := [GET; SET] }.
Next Obligation. solve_finite_nodup. Qed.
Next Obligation. solve_finite_total. Qed.
>>
*)
Ltac solve_finite_nodup := repeat (constructor; first set_solver); constructor.
Ltac solve_finite_total := intros []; set_solver.

(*
TODO: unclear how to best present this abstraction, without adding an
operational typeclass for [of_N].

For now, we nest these functions in a module, to avoid polluting the global
namespace.
*)
Module invert_of_N.
  Section of_N.
    Context `{!EqDecision A} `{!Finite A} (to_N : A -> N).
    (* TODO: Use [list_find] instead? *)
    Definition of_N (r : N) : option A :=
      head $ filter (fun x => bool_decide (to_N x = r)) $ enum A.

    Lemma of_to_N `[Hinj : !Inj eq eq to_N] x : of_N (to_N x) = Some x.
    Proof.
      rewrite /of_N.
      generalize (NoDup_enum A); generalize (elem_of_enum x).
      elim: (enum A) => [|x' xs IHxs]; cbn.
      - by move /elem_of_nil.
      - move=> /elem_of_cons [{IHxs} ->|Hin] /NoDup_cons [Hx'NiXs NDxs].
        + by rewrite bool_decide_eq_true_2.
        + rewrite bool_decide_eq_false_2. apply /IHxs /NDxs /Hin.
          intros ->%(inj to_N). apply /Hx'NiXs /Hin.
    Qed.

    Lemma to_of_N (n : N) (x : A)
      (Hof : of_N n = Some x) : to_N x = n.
    Proof.
      suff: Refine (x ∈ filter (fun x => bool_decide (to_N x = n)) $ enum A). {
        intros [? _]%elem_of_list_filter. by case_bool_decide.
      }
      move: Hof. rewrite /of_N. case: (filter _ _) => [//|y ys /=]. set_solver.
    Qed.
  End of_N.
End invert_of_N.

(* Mixin hierarchy 1: given a Finite instance and a [to_N] function, we can
create an [of_N] function. This contains [finite_encoded_type] *)
Module Type finite_encoded_type <: finite_type.
  Include finite_type.
  Parameter to_N : t -> N.
End finite_encoded_type.

Module Type finite_encoded_type_mixin (Import F : finite_encoded_type).
  Definition of_N := Unfold (@invert_of_N.of_N) (invert_of_N.of_N to_N).

  Definition of_to_N `[Hinj : !Inj eq eq to_N] (x : t) :
      of_N (to_N x) = Some x :=
    invert_of_N.of_to_N to_N (Hinj := Hinj) x.

  Definition to_of_N (n : N) (x : t) :
      of_N n = Some x → to_N x = n :=
    invert_of_N.to_of_N to_N n x.
End finite_encoded_type_mixin.

(* Mixin hierarchy 2: *)
Module Type finite_type_mixin (Import F : finite_type).
  (*
  Not marked as an instance because it is derivable.
  It is here just in case some mixin wants it. *)
  Definition t_countable : Countable t := _.

  (* Obtain encoding from [t_finite] *)
  Definition to_N : t -> N := encode_N.
  Definition of_N : N -> option t := decode_N.

  Lemma of_to_N x : of_N (to_N x) = Some x.
  Proof. apply decode_encode_N. Qed.

  Lemma of_N_Some_to_N (n : N) (x : t) :
    of_N n = Some x → to_N x = n.
  Proof. apply decode_N_Some_encode_N. Qed.
End finite_type_mixin.

Module Type finite_type_intf := finite_type <+ finite_type_mixin.

(* Interface for the bitmask functions. *)
Module Type bitmask_type (Import F : eqdec_type).
  (**
  Convert [t] to the corresponding bit number.
  [bitmask_type_simple_mixin] sets this to [finite_type.to_N], which is
  not always appropriate when interfacing with outside protocols.
  *)
  Parameter to_bit : t -> N.
End bitmask_type.

Module Type bitmask_type_simple_mixin (Import F : finite_type) (Import FM : finite_type_mixin F).
  (* Here, [to_N] is a valid bit encoding *)
  Definition to_bit := to_N.
  Definition of_bit := of_N.

  Lemma of_to_bit x : of_bit (to_bit x) = Some x.
  Proof. apply of_to_N. Qed.

  Lemma of_bit_Some_to_bit (n : N) (x : t) :
    of_bit n = Some x → to_bit x = n.
  Proof. apply of_N_Some_to_N. Qed.
End bitmask_type_simple_mixin.

Module Type finite_bitmask_type_mixin (Import F : finite_type) (Import B : bitmask_type F).
  Definition to_bitmask (r : t) : N := 2 ^ to_bit r.

  Lemma to_bitmask_setbit x : to_bitmask x = N.setbit 0 (to_bit x).
  Proof. by rewrite N.setbit_spec'. Qed.

  Definition testbit (mask : N) (x : t) : bool :=
    N.testbit mask (to_bit x).
  Definition filter (mask : N) (x : t) : list t :=
    if testbit mask x then [x] else [].

  (* Parse a bitmask into a list of flags. *)
  Definition to_list_aux (mask : N) (xs : list t) : list t :=
    xs ≫= filter mask.

  Definition to_list (mask : N) : list t := to_list_aux mask $ enum t.

  Lemma to_list_0 : to_list 0 = [].
  Proof. rewrite /to_list. by elim: enum. Qed.
End finite_bitmask_type_mixin.

Module Type finite_bitmask_type_intf := finite_type <+ bitmask_type <+ finite_bitmask_type_mixin.

(* All the above mixins in the right order, for when [bitmask_type_simple_mixin]
is appropriate. *)
Module Type simple_finite_bitmask_type_mixin (Import F : finite_type).
  Include finite_type_mixin F.
  Include bitmask_type_simple_mixin F.
  Include finite_bitmask_type_mixin F.

  Definition all_bits : N := N.ones (N.of_nat (card F.t)).

  (* Cannot be proven in [finite_bitmask_type_mixin] because we need [to_bit]'s
  definition. *)
  Lemma to_list_max : to_list all_bits = enum F.t.
  Proof.
    rewrite /to_list /to_list_aux /filter.
    elim: enum => [//|x xs IH]; cbn; rewrite {}IH.
    set c := testbit _ _; suff -> : c = true by []; rewrite {}/c.
    apply N.ones_spec_iff, encode_N_lt_card.
  Qed.
End simple_finite_bitmask_type_mixin.

Module Type simple_finite_bitmask_type_intf := finite_type <+ simple_finite_bitmask_type_mixin.

(* A type for _sets_ of flags, as opposed to the type of flags described above. *)
Module finite_bits (BT : finite_bitmask_type_intf).
  Definition t := gset BT.t.
  #[global] Instance top_t : Top t := fin_to_set BT.t (C := t).

  (*
  [to_bits] and [of_bits] implement a bitset encoding of [t] into N, given
  the encoding [to_bit : BT.t -> N].

  Conjecture: [to_bits] and [from_bits] should be partial inverses if [to_bit]
  and [from_bit] are.
  *)
  Definition of_bits (mask : N) : t := list_to_set $ BT.to_list mask.

  Lemma of_bits_0 : of_bits 0 = ∅.
  Proof. by rewrite /of_bits BT.to_list_0. Qed.

  Definition setbit (b : BT.t) (n : N) : N := N.setbit n (BT.to_bit b).
  Notation setbit_alt b n := (N.lor (BT.to_bitmask b) n).

  Lemma setbit_0 x : setbit x 0 = BT.to_bitmask x.
  Proof. by rewrite BT.to_bitmask_setbit. Qed.
  Lemma setbit_is_alt b n : setbit b n = setbit_alt b n.
  Proof. by rewrite /setbit N.setbit_spec' comm_L. Qed.

  Definition to_bits (rs : t) : N := set_fold setbit 0 rs.

  Lemma to_bits_empty : to_bits ∅ = 0.
  Proof. apply set_fold_empty. Qed.
  Lemma to_bits_singleton x : to_bits {[x]} = BT.to_bitmask x.
  Proof. by rewrite /to_bits set_fold_singleton setbit_0. Qed.

  Lemma testbit_singleton (x : BT.t) : BT.testbit (to_bits {[ x ]}) x = true.
  Proof. rewrite to_bits_singleton. apply N.pow2_bits_true. Qed.

  Module Import internal.
    Definition to_bits_alt (rs : t) : N := set_fold (λ b n, setbit_alt b n) 0 rs.
    Lemma to_bits_is_alt rs : to_bits rs = to_bits_alt rs.
    Proof. apply: foldr_ext => // b a. apply setbit_is_alt. Qed.

    (**
    Writing [to_bits] as a commutative, associative fold
    allows reasoning with lemmas about [foldr] and [Permutation].
    See for instance [to_bits_union_singleton]. *)
    Definition to_bits_comm (rs : t) : N :=
      foldr N.lor 0 (BT.to_bitmask <$> elements rs).
    Lemma to_bits_is_comm rs : to_bits rs = to_bits_comm rs.
    Proof. rewrite to_bits_is_alt. apply symmetry, foldr_fmap. Qed.

    (*
    We could also use

    Definition to_bits_comm' (rs : t) : N :=
      set_fold N.lor 0 (set_map (D := gset N) BT.to_bitmask rs).

    But it seems that more lemmas are available on the [foldr] form.
    *)
  End internal.

  (** Use [to_bits_union_singleton]. *)
  #[local] Lemma to_bits_union_singleton' x xs (Hni : x ∉ xs) :
    to_bits ({[x]} ∪ xs) = N.lor (to_bits {[ x ]}) (to_bits xs).
  Proof.
    rewrite to_bits_singleton !to_bits_is_comm /to_bits_comm -foldr_cons -fmap_cons.
    apply foldr_permutation_proper'; [apply _ ..|].
    f_equiv. exact: elements_union_singleton.
  Qed.

  Lemma setbit_in_idemp x xs
    (Hin : x ∈ xs) :
    setbit x (to_bits xs) = to_bits xs.
  Proof.
    apply N.bits_inj_iff => i.
    rewrite N_setbit_bool_decide.
    case_bool_decide as Hdec => //=. symmetry.
    induction xs as [|y ys Hni IHys] using set_ind_L; first by set_solver.
    set_unfold in Hin.
    rewrite to_bits_union_singleton' // N.lor_spec.
    destruct Hin as [->|Hin]; first last.
    { rewrite IHys //. apply: right_absorb_L. }
    clear IHys Hni.
    suff ->: Refine (N.testbit (to_bits {[y]}) i = true) by [].
    subst i. apply testbit_singleton.
  Qed.

  Lemma to_bits_union_singleton x xs :
    to_bits ({[x]} ∪ xs) = N.lor (to_bits {[ x ]}) (to_bits xs).
  Proof.
    destruct (decide (x ∈ xs)). 2: exact: to_bits_union_singleton'.
    rewrite subseteq_union_1_L; [|set_solver].
    rewrite to_bits_singleton -setbit_is_alt.
    by rewrite setbit_in_idemp.
  Qed.

  (* TODO move [setbit], and these lemmas, with [BT.testbit]. *)
  Section BT_to_bit_inj.
    Context`{Hinj : !Inj eq eq BT.to_bit}.
    #[local] Set Default Proof Using "Hinj".

    Lemma testbit_setbit (x y : BT.t) (mask : N) :
      BT.testbit (setbit x mask) y =
      bool_decide (x = y) || BT.testbit mask y.
    Proof.
      rewrite /BT.testbit /setbit N_setbit_bool_decide.
      by rewrite (bool_decide_iff _ _ (inj_iff BT.to_bit _ _)).
    Qed.

    Lemma filter_setbit (x y z : BT.t) mask :
      y ∈ BT.filter (setbit x mask) z ↔ x = y ∧ y = z ∨ y ∈ BT.filter mask z.
    Proof.
      rewrite /BT.filter (testbit_setbit x).
      case_bool_decide; simpl; case_match; set_solver.
    Qed.

    Lemma to_list_setbit (x z : BT.t) (mask : N) :
      z ∈ BT.to_list (setbit x mask) ↔ z = x ∨ z ∈ BT.to_list mask.
    Proof.
      rewrite /BT.to_list /BT.to_list_aux !elem_of_list_bind.
      setoid_rewrite filter_setbit.
      naive_solver eauto using elem_of_enum.
    Qed.

    Lemma of_bits_setbit x xs :
      of_bits (setbit x xs) = {[x]} ∪ of_bits xs.
    Proof.
      apply gset_eq => y; rewrite elem_of_union elem_of_singleton.
      by rewrite /of_bits !elem_of_list_to_set to_list_setbit.
    Qed.

    Lemma of_to_bits rs :
      of_bits (to_bits rs) = rs.
    Proof.
      induction rs as [|x xs Hni IHxs] using set_ind_L.
      { by rewrite to_bits_empty of_bits_0. }
      rewrite to_bits_union_singleton // to_bits_singleton -setbit_is_alt.
      by rewrite of_bits_setbit IHxs.
    Qed.

    #[global] Instance of_to_bits_cancel : Cancel eq of_bits to_bits :=
      of_to_bits.
    #[global] Instance to_bits_inj : Inj eq eq to_bits := cancel_inj.
    #[global] Instance of_bits_surj : Surj eq of_bits := cancel_surj.
  End BT_to_bit_inj.

  Definition masked (mask : N) (x : t) : t :=
    x ∩ of_bits mask.
  Definition masked_opt (mask : N) (x : t) : option t :=
    let res := masked mask x in
    guard (res <> ∅); Some res.

  Lemma masked_0 rights : masked 0 rights = ∅.
  Proof. by rewrite /masked of_bits_0 right_absorb_L. Qed.

  Lemma masked_opt_0 rights : masked_opt 0 rights = None.
  Proof. by rewrite /masked_opt masked_0. Qed.

  Lemma masked_empty n : masked n ∅ = ∅.
  Proof. rewrite /masked. set_solver. Qed.

  Lemma masked_opt_empty n : masked_opt n ∅ = None.
  Proof. by rewrite /masked_opt masked_empty. Qed.

  (* Warning: prefer [BT.all_bits] if available, that's simpler to reason about. *)
  Definition mask_top : N := to_bits ⊤.

  Lemma masked_top `{Hinj : !Inj eq eq BT.to_bit} rights :
    masked mask_top rights = rights.
  Proof. rewrite /masked /mask_top of_to_bits. set_solver. Qed.

  Lemma masked_opt_top `{Hinj : !Inj eq eq BT.to_bit}
    rights (Hrights : rights ≠ ∅) :
    masked_opt mask_top rights = Some rights.
  Proof. by rewrite /masked_opt masked_top option_guard_True. Qed.
End finite_bits.

Module simple_finite_bits (BT : simple_finite_bitmask_type_intf).
  Include finite_bits BT.

  Lemma of_bits_max : of_bits BT.all_bits = ⊤.
  Proof. by rewrite /of_bits BT.to_list_max. Qed.

  Lemma masked_max rights :
    masked BT.all_bits rights = rights.
  Proof. rewrite /masked of_bits_max. set_solver. Qed.

  Lemma masked_opt_max rights (Hrights : rights ≠ ∅) :
    masked_opt BT.all_bits rights = Some rights.
  Proof. by rewrite /masked_opt masked_max option_guard_True. Qed.
End simple_finite_bits.
