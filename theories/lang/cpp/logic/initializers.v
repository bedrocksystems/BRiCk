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
     pred path_pred heap_pred wp destroy const.

(** The C++ language provides several types of initialization:
    - default initialization <https://eel.is/c++draft/dcl.init#def:default-initialization>
    - value initialization <https://eel.is/c++draft/dcl.init#def:value-initialization>
    - zero initialization <https://eel.is/c++draft/dcl.init#def:zero-initialization>
    - direct initialization <https://eel.is/c++draft/dcl.init#def:direct-initialization>

    The BRiCk frontend resolves (via clang) the rules for which one of these is used in each
    context. Therefore, in the semantics, we are left with only two cases:
    - default initialization (implemented by [default_initialize]), which occurs when there
      is no expression used to initialize the value
    - expression initialization (implemented by [wp_initialize]), which occurs when there is
      an expression used to initialize the value.

    Note that the frontend inserts constructor calls to default initialize objects, so
    [Tnamed] types can *not* be default initialized.
 *)

Module Type Init.

  Section with_resolve.
    Context `{Σ : cpp_logic thread_info} {σ:genv} (tu : translation_unit).
    Variables (ρ : region).

    #[local] Notation wp := (wp tu ρ).
    #[local] Notation wp_lval := (wp_lval tu ρ).
    #[local] Notation wp_operand := (wp_operand tu ρ).
    #[local] Notation wp_xval := (wp_xval tu ρ).
    #[local] Notation wp_init := (wp_init tu ρ).
    #[local] Notation interp := (interp tu).
    #[local] Notation fspec := (@fspec _ Σ tu.(globals)).
    #[local] Notation mspec := (@mspec _ Σ tu.(globals)).

    (** [default_initialize_array default_init ty len p Q] initializes an array of type [ty[len]]
        at pointer [p].

        NOTE that default initialization of an array of constants is a compile-time error, so
             we don't need to worry about that case. Also, note that arrays of length 0 are
             not legal so we are guaranteed to have to initialize a value which will result in
             an [ERROR].
     *)
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
    Fixpoint default_initialize (ty : type) (p : ptr) (Q : FreeTemps → epred) {struct ty} : mpred :=
      match ty with
      | Tnum _ _
      | Tchar_ _
      | Tptr _
      | Tbool
      | Tfloat _
      | Tnullptr
      | Tenum _ =>
          let rty := erase_qualifiers ty in
          p |-> uninitR rty (cQp.m 1) -* Q FreeTemps.id

      | Tarray ety sz =>
          default_initialize_array default_initialize ety sz p (fun _ => Q FreeTemps.id)

      | Tref _
      | Trv_ref _ => ERROR "default initialization of reference"
      | Tvoid => ERROR "default initialization of void"
      | Tfunction _ _ => ERROR "default initialization of functions"
      | Tmember_pointer _ _ => ERROR "default initialization of member pointers"
      | Tnamed _ => False (* default initialization of aggregates is done at elaboration time. *)

      | Tarch _ _ => UNSUPPORTED "default initialization of architecture type"
      | Tqualified q ty =>
          if q_const q then ERROR "default initialize const"
          else default_initialize ty p Q
      end%bs%I.
    #[global] Arguments default_initialize !_ _ _ / : assert.

    (** TODO this should be generalized to different [σ] but, in that case it relies
        on the fact that [ty] is defined in both environments.
     *)
    Lemma default_initialize_frame ty : forall this Q Q',
        (Forall f, Q f -* Q' f)
        |-- default_initialize ty this Q -* default_initialize ty this Q'.
    Proof.
      induction ty; simpl; intros; try case_match;
        try solve [ intros; iIntros "a b c"; iApply "a"; iApply "b"; eauto | eauto ].
      { intros. iIntros "a"; iApply (default_initialize_array_frame with "a").
        iModIntro. iIntros (???) "a". by iApply IHty. }
    Qed.

    (* error used when using [e] to initialize a value of type [ty]. *)
    Variant initializing_type (ty : type) (e : Expr) : Prop := ANY.

    (** [wp_initialize] provides "constructor" semantics for types.
        For aggregates, simply delegates to [wp_init], but for primitives,
        the semantics is to evaluate the primitive and initialize the location
        with the value.

        NOTE this assumes that the memory is coming from the C++ abstract machine.

        NOTE [wp_initialize] is very similar to [wp_init] except that [wp_initialize]
        can be used to initialize all values (including references) whereas [wp_init]
        is only safe to initialize non-primitives (arrays and aggregates).
     *)
    Definition wp_initialize (qty : type) (addr : ptr) (init : Expr) (k : FreeTemps -> mpred) : mpred :=
      let '(cv, ty) := decompose_type qty in
      (**
      TODO (Gregory): In a few cases below, we're using [cQp.m 1]
      rather than [qf]. Please add a comment explaining.
      *)
      let qf := if q_const cv then cQp.const 1 else cQp.mut 1 in
      match ty with
      | Tvoid =>
        (* [wp_initialize] is used to `return` from a function.
           The following is legal in C++:
           ```
           void f();
           void g() { return f(); }
           ```
         *)
        wp_operand init (fun v frees => [| v = Vvoid |] ** (addr |-> primR Tvoid qf Vvoid -* k frees))
      | Tpointer _ as ty
      | Tmember_pointer _ _ as ty
      | Tbool as ty
      | Tnum _ _ as ty
      | Tchar_ _ as ty
      | Tenum _ as ty
      | Tfloat _ as ty
      | Tnullptr as ty =>
        wp_operand init (fun v free =>
                          addr |-> primR (erase_qualifiers ty) qf v -* k free)

        (* non-primitives are handled via prvalue-initialization semantics *)
      | Tarray _ _ as ty
      | Tnamed _ as ty => wp_init ty addr init (fun _ frees =>
           if q_const cv then wp_make_const tu addr ty (k frees)
           else k frees)

      | Tref ty =>
        let rty := Tref $ erase_qualifiers ty in
        wp_lval init (fun p free =>
                        addr |-> primR rty qf (Vref p) -* k free)
        (* ^ TODO: [ref]s are never mutable, but we use [qf] here
           for compatibility with [implicit_destruct_struct] *)

      | Trv_ref ty =>
        let rty := Tref $ erase_qualifiers ty in
        wp_xval init (fun p free =>
                        addr |-> primR rty qf (Vref p) -* k free)
        (* ^ TODO: [ref]s are never mutable, but we use [qf] here
           for compatibility with [implicit_destruct_struct] *)
      | Tfunction _ _ => UNSUPPORTED (initializing_type ty init)

      | Tqualified _ ty => False (* unreachable *)
      | Tarch _ _ => UNSUPPORTED (initializing_type ty init)
      end.
    #[global] Arguments wp_initialize !_ _ _ _ /.

    (** [wpi cls this init Q] evaluates the initializer [init] from the
        object [thisp] (of type [Tnamed cls]) and then proceeds as [Q].

        NOTE that temporaries introduced by the evaluation of [init] are cleaned
        up before [Q] is run ([Q] does not have a [FreeTemps] argument). This is
        because initialization is considered a full expression.
        See [https://eel.is/c++draft/class.init#class.base.init-note-2].
     *)
    Definition wpi (cls : globname) (thisp : ptr) (init : Initializer) (Q : epred) : mpred :=
        let p' := thisp ,, offset_for cls init.(init_path) in
        wp_initialize init.(init_type) p' init.(init_init) (fun free => interp free Q).
    #[global] Arguments wpi _ _ _ _ /.

  End with_resolve.

  #[global] Hint Opaque default_initialize_array : typeclass_instances.

  Section frames.
    Context `{Σ : cpp_logic thread_info} {σ1 σ2 :genv} (tu : translation_unit).
    Variables (ρ : region).
    Hypothesis MOD : genv_leq σ1 σ2.

    Lemma wp_initialize_frame obj ty e Q Q' :
      (Forall free, Q free -* Q' free)
      |-- wp_initialize (σ:=σ2) tu ρ ty obj e Q -* wp_initialize (σ:=σ2) tu ρ ty obj e Q'.
    Proof using.
      rewrite /wp_initialize.
      iIntros "a".
      case: (decompose_type _)=>a; case=>>; auto; try
          by [ iApply wp_operand_frame => //; iIntros (??) "X ?"; iApply "a"; iApply "X"
             | iIntros "H"; iExact "H"
             | iApply wp_init_frame => //-;
               case: (q_const _); iIntros (??); [ iApply wp_const_frame; try reflexivity | ]; iApply "a"
             ].
      { by iApply wp_lval_frame => //; iIntros (??) "X ?"; iApply "a"; iApply "X". }
      { by iApply wp_xval_frame => //; iIntros (??) "X ?"; iApply "a"; iApply "X". }
      { by iApply wp_operand_frame => //; iIntros (??) "[$ X] ?"; iApply "a"; iApply "X". }
    Qed.

    Lemma wp_initialize_wand obj ty e Q Q' :
      wp_initialize (σ:=σ2) tu ρ ty obj e Q
      |-- (Forall free, Q free -* Q' free) -* wp_initialize (σ:=σ2) tu ρ ty obj e Q'.
    Proof. by iIntros "H Y"; iRevert "H"; iApply wp_initialize_frame. Qed.

    Theorem wpi_frame (cls : globname) (this : ptr) (e : Initializer) k1 k2 :
      k1 -* k2 |-- wpi (σ:=σ1) tu ρ cls this e k1 -* wpi (σ:=σ2) tu ρ cls this e k2.
    Proof. Abort. (* This is not provable *)
  End frames.

  Section mono_frames.
    (* All framing lemmas *should* work with [genv] weakening, but that
       requires some additional side-conditions on paths that we can't prove
       right now. So, for the time being, we prove [_frame] lemmas without
       [genv] weakening.
     *)

    Context `{Σ : cpp_logic thread_info} {σ : genv} (tu : translation_unit).
    Variables (ρ : region).

    Theorem wpi_frame (cls : globname) (this : ptr) (e : Initializer) k1 k2 :
      k1 -* k2 |-- wpi tu ρ cls this e k1 -* wpi tu ρ cls this e k2.
    Proof.
      clear.
      iIntros "X". rewrite /wpi. iApply wp_initialize_frame.
      iIntros (?); by iApply interp_frame.
    Qed.

  End mono_frames.

End Init.

Declare Module IN : Init.

Export IN.
