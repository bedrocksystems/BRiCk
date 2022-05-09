(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Lists.List.
Require Import iris.proofmode.proofmode.
Require Import bedrock.prelude.numbers.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.bi.errors.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp destroy.
Require Import bedrock.lang.cpp.heap_notations.

Module Type Init.

  Section with_resolve.
    Context `{Σ : cpp_logic thread_info} {σ:genv}.
    Variables (ρ : region).

    #[local] Notation wp := (wp ρ).
    #[local] Notation wp_lval := (wp_lval ρ).
    #[local] Notation wp_prval := (wp_prval ρ).
    #[local] Notation wp_operand := (wp_operand ρ).
    #[local] Notation wp_xval := (wp_xval ρ).
    #[local] Notation wp_init := (wp_init ρ).
    #[local] Notation fspec := (@fspec _ Σ σ.(genv_tu).(globals)).
    #[local] Notation mspec := (@mspec _ Σ σ.(genv_tu).(globals)).

    Definition default_initialize_array (default_initialize : type -> ptr -> (FreeTemps -> epred) -> mpred)
               (ty : type) (len : N) (p : ptr) (Q : FreeTemps -> epred) : mpred :=
      fold_right (fun i PP => default_initialize ty (p ,, o_sub _ ty (Z.of_N i)) (fun free' => interp free' PP))
                 (p .[ ty ! Z.of_N len ] |-> validR -* Q FreeTemps.id) (seqN 0 len).
    #[global] Arguments default_initialize_array : simpl never.

    Lemma default_initialize_array_frame : ∀ di ty sz Q Q' (p : ptr),
        (Forall f, Q f -* Q' f)
    |-- <pers> (Forall p Q Q', (Forall f, Q f -* Q' f) -* di ty p Q -* di ty p Q')
          -* default_initialize_array di ty sz p Q -* default_initialize_array di ty sz p Q'.
    Proof.
      intros ? ? sz Q Q' p; rewrite /default_initialize_array.
      generalize dependent (p .[ ty ! Z.of_N sz ] |-> validR).
      induction (seqN 0 sz) =>/=; intros.
      - iIntros "X #Y a b"; iApply "X"; iApply "a"; eauto.
      - iIntros "F #Hty". iApply "Hty".
        iIntros (?). iApply interp_frame. iApply (IHl with "F"); eauto.
    Qed.

    (** [default_initialize ty p Q] default initializes the memory at [p] according to
        the type [ty].

        NOTE this assumes that the underlying memory has already been given to the
             C++ abstract machine.

        NOTE: <https://eel.is/c++draft/dcl.init#general-7>:
        | (7) To default-initialize an object of type T means:
        | (7.1) If T is a (possibly cv-qualified) class type ([class]), constructors are considered.
        |       The applicable constructors are enumerated ([over.match.ctor]), and the best one for
        |       the initializer () is chosen through overload resolution ([over.match]).
        |       The constructor thus selected is called, with an empty argument list, to initialize
        |       the object.
        | (7.2) If T is an array type, each element is default-initialized.
        | (7.3) Otherwise, no initialization is performed.
        and [default_initialize] corresponds to [default-initialization] as described above.
     *)
    Fixpoint default_initialize
               (ty : type) (p : ptr) (Q : FreeTemps → epred) {struct ty} : mpred :=
      match ty with
      | Tnum _ _ as rty
      | Tptr _ as rty
      | Tbool as rty
      | Tfloat _ as rty
      | Tnullptr as rty =>
        let rty := erase_qualifiers rty in
        p |-> uninitR rty 1 -* Q FreeTemps.id
      | Tarray ety sz =>
        default_initialize_array default_initialize ety sz p (fun _ => Q FreeTemps.id)

      | Tref _
      | Trv_ref _ => ERROR "default initialization of reference"
      | Tvoid => ERROR "default initialization of void"
      | Tfunction _ _ => ERROR "default initialization of functions"
      | Tmember_pointer _ _ => ERROR "default initialization of member pointers"
      | Tnamed _ => False (* default initialization of aggregates is done at elaboration time. *)

      | Tarch _ _ => UNSUPPORTED "default initialization of architecture type"
      | Tqualified _ ty => default_initialize ty p Q
      end%bs%I.
    #[global] Arguments default_initialize !_ _ _ /.

    (** TODO this should be generalized to different [σ] but, in that case it relies
        on the fact that [ty] is defined in both environments.
     *)
    Lemma default_initialize_frame ty : forall this Q Q',
        (Forall f, Q f -* Q' f)
        |-- default_initialize ty this Q -* default_initialize ty this Q'.
    Proof.
      induction ty; simpl;
        try solve [ intros; iIntros "a b c"; iApply "a"; iApply "b"; eauto | eauto ].
      { intros. iIntros "a"; iApply (default_initialize_array_frame with "a").
        iModIntro. iIntros (???) "a". by iApply IHty. }
    Qed.

    (** [wp_initialize] provides "constructor" semantics for types.
        For aggregates, simply delegates to [wp_init], but for primitives,
        the semantics is to evaluate the primitive and initialize the location
        with the value.

        NOTE this assumes that the memory is coming from the C++ abstract machine.

        NOTE [wp_initialize] is very similar to [wp_init] except that [wp_initialize]
        can be used to initialize all values (including references) whereas [wp_init]
        is only safe to initialize C-style values (primitives or aggregates).
     *)
    Definition wp_initialize (ty : type) (addr : ptr) (init : Expr) (k : FreeTemps -> mpred) : mpred :=
      match drop_qualifiers ty with
      | Tvoid => False
      | Tpointer _ as ty
      | Tmember_pointer _ _ as ty
      | Tbool as ty
      | Tnum _ _ as ty
      | Tnullptr as ty =>
        wp_operand init (fun v free =>
                          addr |-> primR (erase_qualifiers ty) 1 v -* k free)

        (* non-primitives are handled via prvalue-initialization semantics *)
      | Tarray _ _
      | Tnamed _ => wp_init addr init (fun _ frees => k frees)
        (* NOTE that just like this function [wp_init] will consume the object. *)

      | Tref ty =>
        let rty := Tref $ erase_qualifiers ty in
        wp_lval init (fun p free =>
                        addr |-> primR rty 1 (Vref p) -* k free)
      | Trv_ref ty =>
        let rty := Tref $ erase_qualifiers ty in
        wp_xval init (fun p free =>
                        addr |-> primR rty 1 (Vref p) -* k free)
      | Tfunction _ _ => False (* functions not supported *)

      | Tqualified _ ty => False (* unreachable *)
      | Tarch _ _ => False (* vendor-specific types are not supported *)
      | Tfloat _ => False (* floating point numbers are not supported *)
      end.
    #[global] Arguments wp_initialize !_ _ _ _ /.

    (* TEMPORARY we use a slightly different semantics for calls
       because we need to revise the way that we define function
       specifications.
     *)
    Definition wp_call_initialize (ty : type) (init : Expr)
               (k : ptr -> FreeTemp -> FreeTemps -> epred) : mpred :=
      Forall p, wp_initialize ty p init (fun frees => k p (FreeTemps.delete ty p) frees).

    (** [wpi cls this init Q] evaluates the initializer [init] from the
        object [thisp] (of type [Tnamed cls]) and then proceeds as [Q].

        NOTE that temporaries introduced by the evaluation of [init] are cleaned
        up before [Q] is run ([Q] does not have a [FreeTemps] argument). This is
        because initialization is considered a full expression.
        See [https://eel.is/c++draft/class.init#class.base.init-note-2].
     *)
    Definition wpi (cls : globname) (thisp : ptr) (init : Initializer) (Q : epred) : mpred :=
        let p' := thisp ,, offset_for cls init.(init_path) in
        wp_initialize (erase_qualifiers init.(init_type)) p' init.(init_init) (fun free => interp free Q).
    #[global] Arguments wpi _ _ _ _ /.

  End with_resolve.

  #[global] Hint Opaque default_initialize_array : typeclass_instances.

  Section frames.
    Context `{Σ : cpp_logic thread_info} {σ1 σ2 :genv}.
    Variables (ρ : region).
    Hypothesis MOD : genv_leq σ1 σ2.

    Lemma wp_initialize_frame obj ty e Q Q' :
      (Forall free, Q free -* Q' free)
      |-- wp_initialize (σ:=σ2) ρ ty obj e Q -* wp_initialize (σ:=σ2) ρ ty obj e Q'.
    Proof using.
      rewrite /wp_initialize.
      case_eq (drop_qualifiers ty) =>/=; intros; eauto;
        try solve [
              iIntros "a"; first [ iApply wp_operand_frame
                                 | iApply wp_lval_frame
                                 | iApply wp_xval_frame ]; try reflexivity;
              iIntros (v f) "X Y"; iApply "a"; iApply "X"; eauto ].
      { iIntros "a". iApply wp_init_frame => //; iIntros (?) => //. }
      { iIntros "a". iApply wp_init_frame => //; iIntros (?) => //. }
    Qed.

    Lemma wp_initialize_wand obj ty e Q Q' :
      wp_initialize (σ:=σ2) ρ ty obj e Q
      |-- (Forall free, Q free -* Q' free) -* wp_initialize (σ:=σ2) ρ ty obj e Q'.
    Proof. by iIntros "H Y"; iRevert "H"; iApply wp_initialize_frame. Qed.

    Theorem wpi_frame (cls : globname) (this : ptr) (e : Initializer) k1 k2 :
      k1 -* k2 |-- wpi (σ:=σ1) ρ cls this e k1 -* wpi (σ:=σ2) ρ cls this e k2.
    Proof. Abort. (* This is not quite provable *)

  End frames.

  Section mono_frames.
    (* All framing lemmas *should* work with [genv] weakening, but that
       requires some additional side-conditions on paths that we can't prove
       right now. So, for the time being, we prove [_frame] lemmas without
       [genv] weakening.
     *)

    Context `{Σ : cpp_logic thread_info} {σ : genv}.
    Variables (ρ : region).

    Theorem wpi_frame (cls : globname) (this : ptr) (e : Initializer) k1 k2 :
      k1 -* k2 |-- wpi ρ cls this e k1 -* wpi ρ cls this e k2.
    Proof.
      clear.
      iIntros "X". rewrite /wpi. iApply wp_initialize_frame.
      iIntros (?); by iApply interp_frame.
    Qed.

  End mono_frames.

End Init.

Declare Module IN : Init.

Export IN.
