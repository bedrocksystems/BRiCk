(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Lists.List.
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred call wp.
Require Import bedrock.lang.cpp.heap_notations.

Module Type Init.

  Section with_resolve.
    Context `{Σ : cpp_logic thread_info} {σ:genv}.
    Variables (M : coPset) (ti : thread_info) (ρ : region).

    Local Notation wp := (wp (resolve:=σ) M ti ρ).
    Local Notation wpi := (wpi (resolve:=σ) M ti ρ).
    (*Local Notation wpe := (wpe (resolve:=σ) M ti ρ).*)
    Local Notation wp_lval := (wp_lval (resolve:=σ) M ti ρ).
    Local Notation wp_prval := (wp_prval (resolve:=σ) M ti ρ).
    Local Notation wp_xval := (wp_xval (resolve:=σ) M ti ρ).
    Local Notation wp_init := (wp_init (resolve:=σ) M ti ρ).
    Local Notation wp_args := (wp_args (σ:=σ) M ti ρ).
    Local Notation fspec := (@fspec _ Σ σ.(genv_tu).(globals)).
    Local Notation mspec := (@mspec _ Σ σ.(genv_tu).(globals)).

    Local Notation primR := (primR (resolve:=σ)) (only parsing).
    Local Notation tblockR := (tblockR (σ:=σ)) (only parsing).
    Local Notation anyR := (anyR (resolve:=σ)) (only parsing).
    Local Notation offset_for := (offset_for σ) (only parsing).

    (* [wp_initialize] provides "constructor" semantics for types.
     * For aggregates, simply delegates to [wp_init], but for primitives,
     * the semantics is to evaluate the primitive and initialize the location
     * with the value.
     *
     * NOTE this is written as a recursive function rather than by using [decompose_type] because
     * we want simplification to reduce it.
     *)
    Fixpoint wp_initialize (ty : type) (addr : ptr) (init : Expr) (k : FreeTemps -> mpred) : mpred :=
      match ty with
      | Tvoid => False
      | Tpointer _ as ty
      | Tmember_pointer _ _ as ty
      | Tbool as ty
      | Tint _ _ as ty =>
        wp_prval init (fun v free =>
                         addr |-> anyR ty 1 (* TODO backwards compat [tblockR ty 1] *) **
                         (   addr |-> primR ty 1 v
                          -* k free))

        (* non-primitives are handled via prvalue-initialization semantics *)
      | Tarray _ _
      | Tnamed _ => wp_init ty addr (not_mine init) k

      | Treference t => False (* reference fields are not supported *)
      | Trv_reference t => False (* reference fields are not supported *)
      | Tfunction _ _ => False (* functions not supported *)

      | Tqualified _ ty => wp_initialize ty addr init k
      | Tnullptr => False (* nullptr fields are not supported *)
      | Tarch _ _ => False (* vendor-specific types are not supported *)
      | Tfloat _ => False (* floating point numbers are not supported *)
      end.

    Lemma wp_initialize_frame obj ty e Q Q' :
      (Forall free, Q free -* Q' free) |-- wp_initialize ty obj e Q -* wp_initialize ty obj e Q'.
    Proof using.
      induction ty =>/=; eauto.
      { iIntros "a". iApply wp_prval_frame; try reflexivity.
        iIntros (v f) "[$ X] Y"; iApply "a"; iApply "X"; eauto. }
      { iIntros "a". iApply wp_prval_frame; try reflexivity.
        iIntros (v f) "[$ X] Y"; iApply "a"; iApply "X"; eauto. }
      { iIntros "a". iApply wp_init_frame; try reflexivity; eauto. }
      { iIntros "a". iApply wp_init_frame; try reflexivity; eauto. }
      { iIntros "a". iApply wp_prval_frame; try reflexivity.
        iIntros (v f) "[$ X] Y"; iApply "a"; iApply "X"; eauto. }
      { iIntros "a". iApply wp_prval_frame; try reflexivity.
        iIntros (v f) "[$ X] Y"; iApply "a"; iApply "X"; eauto. }
    Qed.

    Lemma wp_initialize_wand obj ty e Q Q' :
      wp_initialize ty obj e Q |--(Forall free, Q free -* Q' free) -* wp_initialize ty obj e Q'.
    Proof using.
      iIntros "A B"; iRevert "A"; iApply wp_initialize_frame; eauto.
    Qed.

    Axiom wpi_initialize : forall (thisp : ptr) i cls Q,
        let p' := thisp ., offset_for cls i.(init_path) in
          wp_initialize (erase_qualifiers i.(init_type)) p' i.(init_init) Q
      |-- wpi cls thisp i Q.

    Fixpoint wpis (cls : globname) (this : ptr)
             (inits : list Initializer)
             (Q : FreeTemps -> mpred) : mpred :=
      match inits with
      | nil => Q emp
      | i :: is' => wpi cls this i (fun f => f ** wpis cls this is' Q)
      end%I.

    Axiom wp_init_constructor : forall cls addr cnd es Q,
      wp_args es (fun ls free =>
           match σ.(genv_tu) !! cnd with
           | Some cv =>
             |> mspec (Tnamed cls) (type_of_value cv) ti (Vptr $ _global cnd) (Vptr addr :: ls) (fun _ => Q free)
           | _ => False
           end)
      |-- wp_init (Tnamed cls) addr (Econstructor cnd es (Tnamed cls)) Q.

    Fixpoint wp_array_init (ety : type) (base : ptr) (es : list Expr) (idx : Z) (Q : FreeTemps -> mpred) : mpred :=
      match es with
      | nil => Q emp
      | e :: rest =>
          (* NOTE: We nest the recursive calls to `wp_array_init` within
               the continuation of the `wp_initialize` statement to
               reflect the fact that the C++ Standard introduces
               sequence-points between all of the elements of an
               initializer list (c.f. http://eel.is/c++draft/dcl.init.list#4)
           *)
          wp_initialize ety (base .[ ety ! idx ]) e (fun free => free ** wp_array_init ety base rest (Z.succ idx) Q)
      end%I.

    (* TODO: This could be useful elsewhere and should maybe be moved. *)
    Definition repeatN {A} (x : A) (count : N) : list A :=
      repeat x (N.to_nat count).

    #[global]
    Arguments repeatN : simpl never.

    Definition fill_initlist (desiredsz : N) (es : list Expr) (f : Expr) : list Expr :=
      let actualsz := N.of_nat (length es) in
      es ++ repeatN f (desiredsz - actualsz).

    Definition wp_array_init_fill (ety : type) (base : ptr) (es : list Expr) (f : option Expr) (sz : N) (Q : FreeTemps -> mpred) : mpred :=
      let len := N.of_nat (length es) in
      match (len ?= sz)%N with
      | Lt =>
          match f with
          | None => False
          | Some fill => wp_array_init ety base (fill_initlist sz es fill) 0 Q
          end
      | Eq => wp_array_init ety base es 0 Q
      (* <http://eel.is/c++draft/dcl.init.general#16.5>

         Programs which contain more initializer expressions than
         array-members are ill-formed.
       *)
      | Gt => False
      end.

    Axiom wp_init_initlist_array :forall ls fill ety (sz : N) base Q,
      wp_array_init_fill ety base ls fill sz Q
      |-- wp_init (Tarray ety sz) base (Einitlist ls fill (Tarray ety sz)) Q.

    (* https://eel.is/c++draft/dcl.init#general-7.2 says that "To
    default-initialize an object of type T means: If T is an array type, each
    element is default-initialized." Clang emits [Econstructor ... (Tarray
    (Tnamed ...))] initializing expressions for those cases, where the
    Econstructor node indicates the constructor for the *elements* in the
    array.

    We assume that the elements of the array are initialized from
    left to right, i.e. from the first element to the last element. The
    standard is not explicit about the initialization order for default
    initialization of arrays, but the standard does explicitly specify this
    ordering for arrays with an explicit element list
    (https://eel.is/c++draft/dcl.init#general-15.5). The standard also demands
    destructors to be run in opposite order (https://eel.is/c++draft/dcl.init.general#19),
    and it's expected that every object "is destroyed in the exact reverse order
    it was constructed." (https://doi.org/10.1145/2103656.2103718,
    https://eel.is/c++draft/expr.delete#6). Therefore, it seems
    reasonable to assume that the same ordering applies for default
    initialization. For this reason, the rule for default initalization
    simply defers to the rule for initialization with an empty initializer
    list. *)
    Axiom wp_init_default_array : forall ety sz base ctorname args Q,
      wp_init (Tarray ety sz) base (Einitlist [] (Some (Econstructor ctorname args ety)) (Tarray ety sz)) Q
      |-- wp_init (Tarray ety sz) base (Econstructor ctorname args (Tarray ety sz)) Q.

    Axiom wp_prval_initlist_default : forall t Q,
          match get_default t with
          | None => False
          | Some v => Q v emp
          end
      |-- wp_prval (Einitlist nil None t) Q.

    Axiom wp_prval_initlist_prim : forall t e Q,
          (if prim_initializable t
           then wp_prval e Q
           else False)
      |-- wp_prval (Einitlist (e :: nil) None t) Q.

    Axiom wp_init_cast_noop : forall e ty addr ty' Q,
        wp_init ty addr e Q
        |-- wp_init ty addr (Ecast Cnoop (Prvalue, e) ty') Q.

    Axiom wp_init_clean : forall e ty ty' addr Q,
        wp_init ty' addr e Q
        |-- wp_init ty' addr (Eandclean e ty) Q.
    Axiom wp_init_const : forall ty addr e Q,
        wp_init ty addr e Q
        |-- wp_init (Qconst ty) addr e Q.
    Axiom wp_init_mut : forall ty addr e Q,
        wp_init ty addr e Q
        |-- wp_init (Qmut ty) addr e Q.

  End with_resolve.

End Init.

Declare Module IN : Init.

Export IN.
