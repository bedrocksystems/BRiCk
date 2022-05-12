(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Functionality to elaborate specifications that are written to take
    operands (i.e. [val]) and convert them to take materialized values.
 *)
Require Import iris.proofmode.proofmode.
From bedrock.lang.cpp Require Import ast logic semantics.
From bedrock.lang.cpp.specs Require Import cpp_specs wp_spec_compat.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** determine if an argument is already materialized in the operand style.

      NOTE arrays are treated as primitives because they are passed as pointers
   *)
  Definition mtype (t : type) : globname + type :=
    match erase_qualifiers t with
    | Tnamed cls => inl cls
    | Trv_ref ty => inr (Tref ty)
    | ty => inr ty
    end.

  (** [elaborate ret ts wpp args] builds a function specification around [wpp]
      assuming that [wpp] takes the arguments in [args] (in reverse order) and the
      remaining arguments in [ts].
   *)
  Fixpoint elaborate (ret : type) (ts : list type) (wpp : WpSpec_cpp_val) (args : list val) : WpSpec mpredI ptr ptr :=
    match ts with
    | nil =>
        match mtype ret with
        | inl cls =>
            wp_spec_bind wpp args (fun rv => WITH (fun pr : ptr => DONE pr [| Vptr pr = rv |]))
        | inr t =>
            wp_spec_bind wpp args (fun rv => WITH (fun pr : ptr => DONE pr (_at pr (primR t 1 rv))))
        end
    | t :: ts =>
        match mtype t with
        | inl cls =>
            add_with (fun pv : ptr => add_arg pv (elaborate ret ts wpp (args ++ [Vptr pv])))
        | inr t =>
            add_with (fun pv : ptr => add_with (fun v : val => add_arg pv (
                                           add_pre (_at pv (primR t 1 v)) (add_post (Exists v, _at pv (primR t 1 v))
                                                                                    (elaborate ret ts wpp (args ++ [v]))))))
        end
    end.

  (** [cpp_spec ret ts spec] is the elaborated version of the [spec]
      (operand-based) spec that is based on materialized values.
   *)
  Definition cpp_spec (ret : type) (ts : list type) (wpp : WpSpec_cpp_val) : WpSpec_cpp_ptr :=
    elaborate ret ts wpp nil.

  (** Specification implications

      NOTE: these can be strengthened to include extra information about well-typed values.
            (this includes [valid_ptr] on `this` if it exists                                                                  )
      NOTE: this should do the extra plumbing to avoid [K], though it isn't clear how to do this
      NOTE: this can be strengthened with extra fancy updates.
   *)
  Definition spec_impl {A R} (Q P : WpSpec mpredI A R) : mpredI :=
    ∀ (vs : list A) (K : R → mpred), P vs K -∗ Q vs K.

  (* TODO: some upstream proper instances use [wpspec_entails], unify the uses.
  TODO: we should flip [wpspec_relation] like we flipped [fs_entails] for the
  same reason. *)
  Definition spec_entails {A R} :=
    flip (wpspec_relation (PROP := mpredI) bi_entails (ARGS := A) (RESULT := R)).

  Lemma spec_entails_impl {A R} Q P :
    (|-- @spec_impl A R P Q) ↔
    spec_entails P Q.
  Proof.
    rewrite /spec_impl/wpspec_relation; split; intros H **; first iApply H.
    iIntros (??). iApply H.
  Qed.

  Lemma elab_impl (Q P : WpSpec mpredI val val) ret ts :
    spec_impl Q P |-- spec_impl (cpp_spec ret ts Q) (cpp_spec ret ts P).
  Proof.
    rewrite /spec_impl/wp_specD/cpp_spec.
    assert (forall ps xs Ps Qs,
               (∀ (vs : list val) (K : val → mpred), spec_internal P [] [] [] vs K -∗ spec_internal Q [] [] [] vs K) -∗
               ∀ (vs : list ptr) (K : ptr → mpred),
                 spec_internal (elaborate ret ts P ps) xs Ps Qs vs K -∗ spec_internal (elaborate ret ts Q ps) xs Ps Qs vs K).
    { induction ts; simpl; intros.
      { case_match; rewrite /wp_spec_bind/=.
        { iIntros "H" (??) "[$ P]".
          iRevert "P"; iApply list_sep_into_frame.
          iApply "H". }
        { iIntros "H" (??) "[$ P]".
          iRevert "P"; iApply list_sep_into_frame.
          iApply "H"; eauto. } }
      { case_match; rewrite /wp_spec_bind/=.
        { iIntros "H" (??) "P".
          iDestruct "P" as (x) "P".
          iExists x.
          iDestruct (IHts with "H") as "H".
          by iApply "H". }
        { iIntros "H" (??) "P".
          iDestruct "P" as (x y) "P".
          iExists x, y.
          iDestruct (IHts with "H") as "H".
          by iApply "H". } } }
    { eauto. }
  Qed.

  Lemma elab_entails (Q P : WpSpec mpredI val val) ret ts :
    spec_entails Q P ->
    spec_entails (cpp_spec ret ts Q) (cpp_spec ret ts P).
  Proof. intros H%spec_entails_impl. iApply elab_impl. iApply H. Qed.

  #[global] Instance cpp_spec_mono ret ts :
    Proper (spec_entails ==> spec_entails) (cpp_spec ret ts).
  Proof. intros ???. exact: elab_entails. Qed.
End with_cpp.
