(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import stdpp.telescopes.

Local Open Scope string_scope.

From iris.proofmode Require Import tactics.
From Cpp.Sem Require Import
     Logic PLogic Semantics Wp Init Deinit Call Intensional.
From Cpp Require Import
     Ast.
From Cpp Require Import
     ChargeUtil.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

Local Set Universe Polymorphism.

Module Type Func.

  (* function specifications written in weakest pre-condition style.
   *
   * note(gmm): it might be better to make the `list val` into a
   * `vector val (length fs_arguments)`.
   *)
  Record function_spec' Σ : Type :=
  { fs'_return : type
  ; fs'_arguments : list type
  ; fs'_spec : thread_info -> list val -> (val -> mpred Σ) -> mpred Σ
  }.
  Arguments fs'_return {_} _.
  Arguments fs'_arguments {_} _.
  Arguments fs'_spec {_} _.

  (* this is the core definition that everything will be based on. *)
  Definition cptr'_def {Σ} {resolve} ti (fs : function_spec' Σ) : Rep Σ :=
    as_Rep (fun p =>
         Forall vs,
         [| List.length vs = List.length fs.(fs'_arguments) |] -*
         Forall Q, (fs.(fs'_spec) ti) vs Q -* fspec (resolve:=resolve) p vs ti Q).
  Definition cptr'_aux : seal (@cptr'_def). by eexists. Qed.
  Definition cptr' {Σ} {resolve} := cptr'_aux.(unseal) Σ resolve.
  Definition cptr'_eq : @cptr' = _ := cptr'_aux.(seal_eq).

  (* function specifications written in weakest pre-condition style.
   *
   * the motivation for `function_spec` is to avoid having to destruct things
   * repeatedly; however, they are more difficult to prove things about, so
   * it might be better to do this reasoning post-facto.
   *)
  Record function_spec Σ : Type :=
  { fs_return : type
  ; fs_arguments : list type
  ; fs_spec : thread_info -> arrowFrom val fs_arguments ((val -> mpred Σ) -> mpred Σ)
  }.
  Arguments fs_return {_} _.
  Arguments fs_arguments {_} _.
  Arguments fs_spec {_} _.

  (* this is the core definition that everything will be based on. *)
  Definition cptr_def {Σ} {resolve} ti (fs : function_spec Σ) : Rep Σ :=
   as_Rep (fun p =>
         ForallEach (fs.(fs_spec) ti) (fun PQ args =>
            Forall Q, PQ Q -* fspec (resolve:=resolve) p (List.map snd args) ti Q)).
  Definition cptr_aux : seal (@cptr_def). by eexists. Qed.
  Definition cptr {Σ} {resolve} := cptr_aux.(unseal) Σ resolve.
  Definition cptr_eq : @cptr = _ := cptr_aux.(seal_eq).

  Record WithPrePost Σ : Type :=
    { wpp_with : tele
    ; wpp_pre : tele_fun wpp_with (mpred Σ)
    ; wpp_post : tele_fun wpp_with (val -> mpred Σ) }.
  Arguments wpp_with {_} _.
  Arguments wpp_pre {_} _.
  Arguments wpp_post {_} _.

  Section with_Σ.
  Context {Σ : gFunctors}.

  Local Notation mpred := (mpred Σ) (only parsing).
  Local Notation Kpreds := (Kpreds Σ) (only parsing).
  Local Notation WithPrePost := (WithPrePost Σ) (only parsing).
  Local Notation function_spec := (function_spec Σ) (only parsing).

  Fixpoint WppD' {t : tele}
  : forall (P : t -t> mpred) (Q : t -t> val -> mpred), (val -> mpred) -> mpred :=
    match t as t
          return forall (P : t -t> mpred) (Q : t -t> val -> mpred),
                 (val -> mpred) -> mpred
    with
    | TeleO => fun P Q Q' => P ** (Forall result, Q result -* Q' result)
    | TeleS ts => fun P Q Q' => Exists x, @WppD' (ts x) (P x) (Q x) Q'
    end.

  Definition WppD (wpp : WithPrePost) : (val -> mpred) -> mpred :=
    WppD' wpp.(wpp_pre) wpp.(wpp_post).
  Global Arguments WppD !_ / .

  Section with_resolve.
    Context {resolve : genv}.

  (* Hoare triple for a function.
   * note(gmm): these should include linkage specifications.
   *)
  Definition TSFunction (ret : type) (targs : list type)
             (PQ : thread_info -> arrowFrom val targs WithPrePost)
  : function_spec :=
    {| fs_return := ret
     ; fs_arguments := targs
     ; fs_spec ti := arrowFrom_map WppD (PQ ti) |}.


  Definition SFunction (ret : type) (targs : list type)
             (PQ : arrowFrom val targs WithPrePost)
  : function_spec :=
    TSFunction ret targs (fun _ => PQ).

  (* Hoare triple for a constructor.
   *)
  Definition TSConstructor (class : globname)
             (targs : list type)
             (PQ : thread_info -> val -> arrowFrom val targs WithPrePost)
  : function_spec :=
    let this_type := Qmut (Tref class) in
    TSFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
              (fun ti this => arrowFrom_map (fun wpp =>
                 {| wpp_with := wpp.(wpp_with)
                  ; wpp_pre :=
                    tele_map (fun P => _at (_eq this) (uninit (Tref class) 1) ** P) wpp.(wpp_pre)
                  ; wpp_post := wpp.(wpp_post)
                  |}) (PQ ti this)).

  Definition SConstructor (class : globname) (targs : list type)
             (PQ : val -> arrowFrom val targs WithPrePost)
  : function_spec := TSConstructor class targs (fun _ => PQ).

  (* Hoare triple for a destructor.
   *)
  Definition TSDestructor (class : globname) (PQ : thread_info -> val -> WithPrePost)
  : function_spec :=
    let this_type := Qmut (Tref class) in
    TSFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
               (fun ti this =>
                  let PQ := PQ ti this in
                 {| wpp_with := PQ.(wpp_with)
                  ; wpp_pre := PQ.(wpp_pre)
                  ; wpp_post :=
                    tele_map (fun Q res => _at (_eq this) (tany (Tref class) 1) ** Q res) PQ.(wpp_post)
                  |}).

  Definition SDestructor (class : globname) (PQ : val -> WithPrePost)
  : function_spec := TSDestructor class (fun _ => PQ).

  (* Hoare triple for a method.
   *)
  Definition TSMethod (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : thread_info -> val -> arrowFrom val targs WithPrePost)
  : function_spec :=
    let class_type := Tref class in
    let this_type := Tqualified qual class_type in
    TSFunction ret (Qconst (Tpointer this_type) :: targs) PQ.
      (* ^ todo(gmm): this looks wrong. something isn't going
       * to fit together with respect to calling conventions and
       * specifications.
       *)

  Definition SMethod (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : val -> arrowFrom val targs WithPrePost)
  : function_spec := TSMethod class qual ret targs (fun _ => PQ).

  Lemma cptr_cptr' : forall ti fs fs',
      fs'.(fs'_arguments) = fs.(fs_arguments) ->
      fs'.(fs'_return) = fs.(fs_return) ->
      (forall Q vs,
          (fs'.(fs'_spec) ti) vs Q -|-
          applyEach fs.(fs_arguments) vs (fs.(fs_spec) ti) (fun k _ => k Q)) ->
      cptr (Σ:=Σ) (resolve:=resolve) ti fs -|- cptr' (Σ:=Σ) (resolve:=resolve) ti fs'.
  Proof.
    rewrite cptr'_eq. unfold cptr'_def.
    rewrite cptr_eq. unfold cptr_def.
    intros.
    destruct fs, fs'. simpl in *. subst.
    eapply Rep_equiv_ext_equiv. simpl; intros.
    setoid_rewrite H1; clear H1.
    rewrite <- (forallEach_primes (PROP:=L.mpredI Σ)) with (Z:=fun a b => fspec x a ti b).
    reflexivity.
  Qed.

  Definition cglob_def (gn : globname) ti (spec : function_spec)
  : mpred :=
    _at (_global gn) (cptr (resolve:=resolve) ti spec).
  Definition cglob_aux : seal (@cglob_def). by eexists. Qed.
  Definition cglob := cglob_aux.(unseal).
  Definition cglob_eq : @cglob = _ := cglob_aux.(seal_eq).

  Axiom cglob_dup : forall p ti fs,
      cglob p ti fs -|- cglob p ti fs ** cglob p ti fs.

  (* i was thinking that i could store static variables in invariants.
   * i'm not sure how this works with function pointer weakening.
   *)
  Axiom cglob_weaken : forall a b c, cglob a b c |-- empSP.

  End with_resolve.

  Fixpoint bind_type ρ (t : type) (x : ident) (v : val) : mpred :=
    match t with
    | Tqualified _ t => bind_type ρ t x v
    | Treference ref => _local ρ x &~ v
    | Trv_reference ref => _local ρ x &~ v
    | Tref _         => _local ρ x &~ v
    | _              => tlocal ρ x (tprim (erase_qualifiers t) 1 v)
    end.

  Fixpoint bind_type_free ρ (t : type) (x : ident) (v : val) : mpred :=
    match t with
    | Tqualified _ t => bind_type_free ρ t x v
    | Treference ref => _local ρ x &~ v
    | Trv_reference ref => _local ρ x &~ v
    | Tref cls       => _local ρ x &~ v
    | _              => tlocal ρ x (tany (erase_qualifiers t) 1)
    end.

    (* the proof obligation for a function
     *)
    Definition func_ok {resolve:genv} (ret : type) (params : list (ident * type))
               (body : Stmt)
               (ti : thread_info) (spec : function_spec)
    : mpred :=
      [| ret = spec.(fs_return) |] **
      [| spec.(fs_arguments) = List.map snd params |] **
      ForallEach (spec.(fs_spec) ti) (fun PQ args =>
        Forall ρ : region,
        let vals := List.map snd args in

        (* this is what is created from the parameters *)
        let binds :=
            sepSPs (zip (fun '(x, t) 'v => bind_type ρ t x v) params vals) in
        (* this is what is freed on return *)
        let frees :=
            sepSPs (zip (fun '(x, t) 'v =>
                           bind_type_free ρ t x v)
                   (rev params) (rev vals)) in
        if is_void ret
        then
          Forall Q : mpred,
          (binds ** PQ (fun _ => Q)) -*
          wp (resolve:=resolve) ti ρ body (Kfree frees (void_return (|>Q)))
        else if is_aggregate ret then
          Forall Q : val -> mpred,
          (binds ** _at (_result ρ) (uninit (erase_qualifiers ret) 1) ** PQ Q) -*
          wp (resolve:=resolve) ti ρ body (Kfree (frees ** Exists a, _result ρ &~ a) (val_return (fun x => |> Q x)))
        else
          Forall Q : val -> mpred,
          (binds ** PQ Q) -*
          wp (resolve:=resolve) ti ρ body (Kfree frees (val_return (fun x => |> Q x)))).
    (* ^ todo(gmm): the new semantics of function gets an address for a return value
     * so the semantics for `return` should be that *)



    Definition method_ok {resolve} (meth : Method) (ti : thread_info) (spec : function_spec)
      : mpred :=
      match meth.(m_body) with
      | None => lfalse
      | Some body =>
        let this_type :=
            Qconst (Tpointer (Tqualified meth.(m_this_qual) (Tref meth.(m_class))))
        in
        [| spec.(fs_return) = meth.(m_return) |] **
        [| spec.(fs_arguments) = this_type :: List.map snd meth.(m_params) |] **
        ForallEach (spec.(fs_spec) ti) (fun PQ args =>
          Forall ρ : region,
          let vals := List.map snd args in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds :=
                _this ρ &~ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type ρ t x v) meth.(m_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                _this ρ &~ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type_free ρ t x v) (rev meth.(m_params))
                       (rev rest_vals))
            in
            let ret_ty := meth.(m_return) in
            if is_void ret_ty
            then
              Forall Q : mpred,
              (binds ** PQ (fun _ => Q)) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (void_return (|>Q))))
            else if is_aggregate ret_ty then
              Forall Q : val -> mpred,
              (binds ** _at (_result ρ) (uninit (erase_qualifiers ret_ty) 1) ** PQ Q) -* (wp (resolve:=resolve) ti ρ body (Kfree (frees ** Exists a, _result ρ &~ a) (val_return (fun x => |>Q x))))
            else
              Forall Q : val -> mpred,
              (binds ** PQ Q) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (val_return (fun x => |>Q x))))
          end)
      end.

    Definition wp_ctor {resolve : genv} (cls : globname) (ti : thread_info) (ρ : region)
               (this_val : val)
               (inits : list Initializer) (body : Stmt)
               (Q : Kpreds)
    : mpred :=
      wpis (resolve:=resolve) ti ρ cls this_val inits
           (fun free => free ** wp (resolve:=resolve) ti ρ body Q).


    Definition ctor_ok {resolve} (ctor : Ctor) ti (spec : function_spec)
    : mpred :=
      match ctor.(c_body) with
      | None => lfalse
      | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
      | Some (UserDefined (init, body)) =>
        let this_type :=
            Qconst (Tpointer (Qmut (Tref ctor.(c_class))))
        in
        [| spec.(fs_return) = Qmut Tvoid |] **
        [| spec.(fs_arguments) = this_type :: List.map snd ctor.(c_params) |] **
        ForallEach (spec.(fs_spec) ti) (fun PQ args =>
          Forall ρ,
          let vals := List.map snd args in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds :=
                _this ρ &~ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type ρ t x v) ctor.(c_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                _this ρ &~ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type_free ρ t x v) (rev ctor.(c_params)) (rev rest_vals))
            in
            Forall Q : mpred,
            (binds ** PQ (fun _ => Q)) -*
            (wp_ctor (resolve:=resolve) ctor.(c_class) ti ρ this_val init body
                     (Kfree frees (void_return (|>Q))))
          end)
      end.

    Definition wp_dtor {resolve : genv} (cls : globname) (ti : thread_info) (ρ : region)
               (this_val : val)
               (body : Stmt) (dtors : list (FieldOrBase * globname))
               (frees : mpred) (Q : mpred)
    : mpred :=
      wp (resolve:=resolve) ti ρ body
         (Kfree frees (void_return (wpds (resolve:=resolve) ti ρ cls this_val dtors Q))).

    Definition dtor_ok {resolve: genv}(dtor : Dtor) ti (spec : function_spec)
    : mpred :=
      match dtor.(d_body) with
      | None => lfalse
      | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
      | Some (UserDefined (body, deinit)) =>
        let this_type :=
            Qconst (Tpointer (Qmut (Tref dtor.(d_class))))
        in
        [| spec.(fs_return) = Qmut Tvoid |] **
        [| spec.(fs_arguments) = this_type :: nil |] **
        ForallEach (spec.(fs_spec) ti) (fun PQ args =>
          Forall ρ,
          let vals := List.map snd args in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds := _this ρ &~ this_val in
            (* this is what is freed on return *)
            let frees := _this ρ &~ this_val in
            Forall Q : mpred,
              (binds ** PQ (fun _ => Q)) -*
              (wp_dtor (resolve:=resolve) dtor.(d_class) ti ρ this_val body deinit frees (|>Q))
          end)
      end.
  End with_Σ.

End Func.

Declare Module F : Func.

Export F.
