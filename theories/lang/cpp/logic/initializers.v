(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
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
     pred path_pred heap_pred wp destroy const.

(**
The C++ language provides several types of initialization:
- default initialization <https://eel.is/c++draft/dcl.init#def:default-initialization>
- value initialization <https://eel.is/c++draft/dcl.init#def:value-initialization>
- zero initialization <https://eel.is/c++draft/dcl.init#def:zero-initialization>
- direct initialization <https://eel.is/c++draft/dcl.init#def:direct-initialization>

The BRiCk frontend resolves (via clang) the rules for which one of
these is used in each context. Therefore, in the semantics, we are
left with only two cases:

- default initialization (implemented by [default_initialize]), which
occurs when there is no expression used to initialize the value

- expression initialization (implemented by [wp_initialize]), which
occurs when there is an expression used to initialize the value.

Note that the frontend inserts constructor calls to default initialize
objects, so [Tnamed] types can *not* be default initialized.
*)

(** ** Default initilalization *)
(**
[default_initialize_array default_initialize tu ty len p Q]
initializes an array of type [ty[len]] at pointer [p] using
[default_initialize].

NOTE that default initialization of an array of constants is a
compile-time error, so we don't need to worry about that case.
Also, note that arrays of length 0 are not legal so we are
guaranteed to have to initialize a value which will result in an
[ERROR].
*)
Definition default_initialize_array `{Σ : cpp_logic, σ : genv}
    (default_initialize : translation_unit -> type -> ptr -> (FreeTemps -> epred) -> mpred)
    (tu : translation_unit) (ty : type) (len : N) (p : ptr) (Q : FreeTemps -> epred) : mpred :=
  let folder i PP :=
    default_initialize tu ty (p ,, o_sub _ ty (Z.of_N i)) (fun free' => interp tu free' PP)
  in
  foldr folder (p .[ ty ! Z.of_N len ] |-> validR -* Q FreeTemps.id) (seqN 0 len).
#[global] Hint Opaque default_initialize_array : typeclass_instances.
#[global] Arguments default_initialize_array : simpl never.

(**
[default_initialize tu ty p Q] default initializes the memory at [p]
according to the type [ty].

NOTE this assumes that the underlying memory has already been given to
the C++ abstract machine.

NOTE: <https://eel.is/c++draft/dcl.init#general-7>:
| (7) To default-initialize an object of type T means:
| (7.1) If T is a (possibly cv-qualified) class type ([class]), constructors are considered.
|       The applicable constructors are enumerated ([over.match.ctor]), and the best one for
|       the initializer () is chosen through overload resolution ([over.match]).
|       The constructor thus selected is called, with an empty argument list, to initialize
|       the object.
| (7.2) If T is an array type, each element is default-initialized.
| (7.3) Otherwise, no initialization is performed.

and [default_initialize] corresponds to [default-initialization] as
described above.
*)
Fixpoint default_initialize `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ty : type) (p : ptr) (Q : FreeTemps → epred) {struct ty} : mpred :=
  match ty with
  | Tnum _ _
  | Tchar_ _
  | Tptr _
  | Tbool
  | Tfloat_ _
  | Tnullptr
  | Tenum _ =>
    let rty := erase_qualifiers ty in
    p |-> uninitR rty (cQp.m 1) -* Q FreeTemps.id

  | Tarray ety sz =>
    default_initialize_array default_initialize tu ety sz p (fun _ => Q FreeTemps.id)

  | Tref _
  | Trv_ref _ => ERROR "default initialization of reference"
  | Tvoid => ERROR "default initialization of void"
  | Tfunction _ _ => ERROR "default initialization of functions"
  | Tmember_pointer _ _ => ERROR "default initialization of member pointers"
  | Tnamed _ => False (* default initialization of aggregates is done at elaboration time. *)

  | Tarch _ _ => UNSUPPORTED "default initialization of architecture type"
  | Tqualified q ty =>
    if q_const q then ERROR "default initialize const"
    else default_initialize tu ty p Q
  end%bs%I.
#[global] Hint Opaque default_initialize : typeclass_instances.
#[global] Arguments default_initialize _ _ _ _ !_ _ _ / : assert.

Section frame.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : FreeTemps -> epred).
  Implicit Types (di : translation_unit -> type -> ptr -> (FreeTemps -> epred) -> mpred).

  Lemma default_initialize_array_frame di tu tu' ty sz Q Q' (p : ptr) :
    sub_module tu tu' ->
    (∀ p Q Q', (Forall f, Q f -* Q' f) |-- di tu ty p Q -* di tu' ty p Q') ->
    (Forall f, Q f -* Q' f)
    |-- default_initialize_array di tu ty sz p Q -* default_initialize_array di tu' ty sz p Q'.
  Proof.
    intros Hsub IHty.
    rewrite /default_initialize_array.
    generalize dependent (p .[ ty ! Z.of_N sz ] |-> validR).
    induction (seqN 0 sz) =>/=; intros.
    - iIntros "X a b". iApply "X". by iApply "a".
    - iIntros "F". iApply IHty.
      iIntros (?). iApply interp_frame_strong; [done|]. iApply (IHl with "F").
  Qed.

  (**
  TODO this should be generalized to different [σ] but, in that case
  it relies on the fact that [ty] is defined in both environments.
  *)
  Lemma default_initialize_frame tu tu' ty this Q Q' :
    sub_module tu tu' ->
    (Forall f, Q f -* Q' f)
    |-- default_initialize tu ty this Q -* default_initialize tu' ty this Q'.
  Proof.
    intros.
    move: this Q Q'. induction ty=>this Q Q'; simpl; intros; try case_match;
      try solve [ intros; iIntros "a b c"; iApply "a"; iApply "b"; eauto | eauto ].
    { intros. iIntros "a". by iApply (default_initialize_array_frame with "a"). }
  Qed.

  #[global] Instance: Params (@default_initialize) 6 := {}.
  #[local] Notation INIT R := (
    ∀ tu ty this,
    Proper (pointwise_relation _ R ==> R) (default_initialize tu ty this)
  ) (only parsing).
  #[global] Instance default_initialize_mono : INIT bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (default_initialize_frame with "[] wp"); [done|]. iIntros (free) "Q".
    by iApply HQ.
  Qed.
  #[global] Instance default_initialize_flip_mono : INIT (flip bi_entails).
  Proof. repeat intro. by apply default_initialize_mono. Qed.
  #[global] Instance default_initialize_proper : INIT equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply default_initialize_mono=>free; rewrite HQ. Qed.

  #[global] Instance: Params (@default_initialize_array) 8 := {}.
  #[local] Notation ARRAY R := (
    ∀ tu ty sz p,
    Proper (pointwise_relation _ R ==> R)
      (default_initialize_array default_initialize tu ty sz p)
  ) (only parsing).
  #[global] Instance default_initialize_array_mono : ARRAY bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (default_initialize_array_frame with "[] wp"); [done| |].
    { clear=>p Q Q'. exact: default_initialize_frame. }
    { iIntros (free) "Q". by iApply HQ. }
  Qed.
  #[global] Instance default_initialize_array_flip_mono : ARRAY (flip bi_entails).
  Proof. repeat intro. by apply default_initialize_array_mono. Qed.
  #[global] Instance default_initialize_array_proper : ARRAY equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply default_initialize_array_mono=>free; rewrite HQ. Qed.
End frame.

(** ** Expression initialization *)

Section wp_initialize.
  Context `{Σ : cpp_logic thread_info} {σ:genv} (tu : translation_unit).
  Implicit Types (Q : FreeTemps -> epred).
  Variables (ρ : region).

  #[local] Notation wp := (wp tu ρ).
  #[local] Notation wp_lval := (wp_lval tu ρ).
  #[local] Notation wp_operand := (wp_operand tu ρ).
  #[local] Notation wp_xval := (wp_xval tu ρ).
  #[local] Notation wp_init := (wp_init tu ρ).
  #[local] Notation interp := (interp tu).
  #[local] Notation wp_fptr := (@wp_fptr _ Σ tu.(types)).
  #[local] Notation mspec := (@mspec _ Σ tu.(types)).

  (* error used when using [e] to initialize a value of type [ty]. *)
  Variant initializing_type (ty : type) (e : Expr) : Prop := ANY.

  (**
  [wp_initialize] provides "constructor" semantics for types. For
  aggregates, simply delegates to [wp_init], but for primitives, the
  semantics is to evaluate the primitive and initialize the location
  with the value.

  NOTE this assumes that the memory is coming from the C++ abstract
  machine.

  NOTE [wp_initialize] is very similar to [wp_init] except that
  [wp_initialize] can be used to initialize all values (including
  references) whereas [wp_init] is only safe to initialize
  non-primitives (arrays and aggregates).
  *)
  Definition wp_initialize_unqualified (cv : type_qualifiers) (ty : type)
      (addr : ptr) (init : Expr) (Q : FreeTemps -> epred) : mpred :=
    match ty with

    (**
    Note: For primitive types, we effectively bake in [if q_const cv
    then wp_make_const tu addr ty else id].
    *)

    | Tvoid =>
      (*
      [wp_initialize] is used to `return` from a function. The
      following is legal in C++:
      <<
         void f();
         void g() { return f(); }
      >>
      *)
      letI* v, frees := wp_operand init in
      let qf := cQp.mk (q_const cv) 1 in
      [| v = Vvoid |] **
      (addr |-> primR Tvoid qf Vvoid -* Q frees)

    | Tpointer _
    | Tmember_pointer _ _
    | Tbool
    | Tnum _ _
    | Tchar_ _
    | Tenum _
    | Tfloat_ _
    | Tnullptr =>
      letI* v, free := wp_operand init in
      let qf := cQp.mk (q_const cv) 1 in
      addr |-> primR (erase_qualifiers ty) qf v -* Q free

      (* non-primitives are handled via prvalue-initialization semantics *)
    | Tarray _ _
    | Tnamed _ =>
      letI* frees := wp_init ty addr init in
      letI* := if q_const cv then wp_make_const tu addr ty else id in
      Q frees

    | Tref ty =>
      let rty := Tref $ erase_qualifiers ty in
      letI* p, free := wp_lval init in
      let qf := cQp.mk (q_const cv) 1 in
      (*
      TODO: [ref]s are never mutable, but we use [qf] here
      for compatibility with [implicit_destruct_struct]
      *)
      addr |-> primR rty qf (Vref p) -* Q free

    | Trv_ref ty =>
      let rty := Tref $ erase_qualifiers ty in
      letI* p, free := wp_xval init in
      let qf := cQp.mk (q_const cv) 1 in
      (*
      TODO: [ref]s are never mutable, but we use [qf] here
      for compatibility with [implicit_destruct_struct]
      *)
      addr |-> primR rty qf (Vref p) -* Q free

    | Tfunction _ _ => UNSUPPORTED (initializing_type ty init)

    | Tqualified _ ty => False (* unreachable *)
    | Tarch _ _ => UNSUPPORTED (initializing_type ty init)
    end.
  #[global] Hint Opaque wp_initialize_unqualified : typeclass_instances.
  #[global] Arguments wp_initialize_unqualified _ !_ _ _ _ / : assert.

  Definition wp_initialize (qty : type) (addr : ptr) (init : Expr) (Q : FreeTemps -> epred) : mpred :=
    qual_norm wp_initialize_unqualified qty addr init Q.
  #[global] Hint Opaque wp_initialize : typeclass_instances.
  #[global] Arguments wp_initialize !_ _ _ _ / : assert.

  Lemma wp_initialize_ok qty :
    qual_norm_spec wp_initialize_unqualified QM qty (wp_initialize qty).
  Proof. apply qual_norm_ok. Qed.

  Lemma wp_initialize_qual_norm qty :
    wp_initialize qty = qual_norm wp_initialize_unqualified qty.
  Proof. done. Qed.

  Lemma wp_initialize_decompose_type qty :
    wp_initialize qty =
      let p := decompose_type qty in
      wp_initialize_unqualified p.1 p.2.
  Proof.
    by rewrite wp_initialize_qual_norm qual_norm_decompose_type.
  Qed.

  (**
  [wpi cls this init Q] evaluates the initializer [init] from the
  object [thisp] (of type [Tnamed cls]) and then proceeds as [Q].

  NOTE that temporaries introduced by the evaluation of [init] are
  cleaned up before [Q] is run ([Q] does not have a [FreeTemps]
  argument). This is because initialization is considered a full
  expression.

  See [https://eel.is/c++draft/class.init#class.base.init-note-2].
  *)
  Definition wpi (cls : globname) (thisp : ptr) (init : Initializer) (Q : epred) : mpred :=
    let p' := thisp ,, offset_for cls init.(init_path) in
    letI* free := wp_initialize init.(init_type) p' init.(init_init) in
    letI* := interp free in
    Q.
  #[global] Hint Opaque wpi : typeclass_instances.
  #[global] Arguments wpi _ _ _ _ / : assert.

End wp_initialize.

(*
All framing lemmas *should* work with [genv] weakening, but that
requires some additional side-conditions on paths that we can't prove
right now. So, for the time being, we prove [_frame] lemmas without
[genv] weakening.
*)

Section frames.
  Context `{Σ : cpp_logic thread_info, σ : genv}.
  Implicit Types (Q : FreeTemps -> epred).

  Lemma wp_initialize_unqualified_frame tu tu' ρ obj cv ty e Q Q' :
    sub_module tu tu' ->
    (Forall free, Q free -* Q' free)
    |-- wp_initialize_unqualified tu ρ cv ty obj e Q -* wp_initialize_unqualified tu' ρ cv ty obj e Q'.
  Proof.
    intros. iIntros "HQ'". destruct ty; cbn; auto.
    all:
      lazymatch goal with
      | |- context [wp_operand] => iApply wp_operand_frame; [done|]
      | |- context [wp_lval] => iApply wp_lval_frame; [done|]
      | |- context [wp_xval] => iApply wp_xval_frame; [done|]
      | |- context [wp_init] => iApply wp_init_frame; [done|]
      | _ => idtac
      end;
      try by iIntros (??) "HQ ?"; iApply "HQ'"; iApply "HQ".
    all:
      lazymatch goal with
      | |- context [wp_const] =>
        iIntros (?);
        destruct (q_const cv);
          [ iApply wp_const_frame; [exact: types_compat|]
          | cbn ];
        iIntros "?"; by iApply "HQ'"
      | _ => idtac
      end.
    (* void *)
    iIntros (??) "($ & HQ) ?". iApply "HQ'". by iApply "HQ".
  Qed.

  #[global] Instance: Params (@wp_initialize_unqualified) 9 := {}.
  #[local] Notation BODY R := (
    ∀ tu ρ cv ty obj init,
    Proper (pointwise_relation _ R ==> R) (wp_initialize_unqualified tu ρ cv ty obj init)
  ) (only parsing).
  #[global] Instance wp_initialize_unqualified_mono : BODY bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (wp_initialize_unqualified_frame with "[] wp"); [done|]. iIntros (free) "Q".
    by iApply HQ.
  Qed.
  #[global] Instance wp_initialize_unqualified_flip_mono : BODY (flip bi_entails).
  Proof. repeat intro. by apply wp_initialize_unqualified_mono. Qed.
  #[global] Instance wp_initialize_unqualified_proper : BODY equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply wp_initialize_unqualified_mono=>free; rewrite HQ. Qed.

  Lemma wp_initialize_frame tu tu' ρ obj ty e Q Q' :
    sub_module tu tu' ->
    (Forall free, Q free -* Q' free)
    |-- wp_initialize tu ρ ty obj e Q -* wp_initialize tu' ρ ty obj e Q'.
  Proof using.
    intros. rewrite /wp_initialize/qual_norm.
    induction (wp_initialize_ok tu ρ ty); last done.
    rewrite !qual_norm'_unqual. exact: wp_initialize_unqualified_frame.
  Qed.

  #[global] Instance: Params (@wp_initialize) 8 := {}.
  #[local] Notation INIT R := (
    ∀ tu ρ ty obj init,
    Proper (pointwise_relation _ R ==> R) (wp_initialize tu ρ ty obj init)
  ) (only parsing).
  #[global] Instance wp_initialize_mono : INIT bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (wp_initialize_frame with "[] wp"); [done|]. iIntros (free) "Q".
    by iApply HQ.
  Qed.
  #[global] Instance wp_initialize_flip_mono : INIT (flip bi_entails).
  Proof. repeat intro. by apply wp_initialize_mono. Qed.
  #[global] Instance wp_initialize_proper : INIT equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply wp_initialize_mono=>free; rewrite HQ. Qed.

  Lemma wp_initialize_wand tu ρ obj ty e Q Q' :
    wp_initialize tu ρ ty obj e Q
    |-- (Forall free, Q free -* Q' free) -* wp_initialize tu ρ ty obj e Q'.
  Proof. by iIntros "H Y"; iRevert "H"; iApply wp_initialize_frame. Qed.

  Lemma wpi_frame tu tu' ρ cls this e (Q Q' : epred) :
    sub_module tu tu' ->
    Q -* Q' |-- wpi tu ρ cls this e Q -* wpi tu' ρ cls this e Q'.
  Proof.
    intros. iIntros "HQ". rewrite /wpi.
    iApply wp_initialize_frame; [done|]. iIntros (free).
    by iApply interp_frame_strong.
  Qed.

  #[global] Instance: Params (@wpi) 8 := {}.
  #[local] Notation WPI R := (
    ∀ tu ρ cls this e,
    Proper (R ==> R) (wpi tu ρ cls this e)
  ) (only parsing).
  #[global] Instance wpi_mono : WPI bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (wpi_frame with "[] wp"); [done|]. iIntros "Q".
    by iApply HQ.
  Qed.
  #[global] Instance wpi_flip_mono : WPI (flip bi_entails).
  Proof. repeat intro. by apply wpi_mono. Qed.
  #[global] Instance wpi_proper : WPI equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply wpi_mono; rewrite HQ. Qed.
End frames.
