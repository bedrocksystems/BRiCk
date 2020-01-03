(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

Require Import stdpp.telescopes.

From iris.proofmode Require Import tactics.
From bedrock Require Import ChargeUtil ChargeCompat.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp Require Import
     pred heap_pred wp initializers destructors call intensional.

Local Open Scope string_scope.


Local Set Universe Polymorphism.

Module Type Func.

  (* function specifications written in weakest pre-condition style.
   *
   * note(gmm): it might be better to make the `list val` into a
   * `vector val (length fs_arguments)`.
   *)
  Record function_spec Σ : Type :=
  { fs_return : type
  ; fs_arguments : list type
  ; fs_spec : thread_info -> list val -> (val -> mpred Σ) -> mpred Σ
  }.
  Arguments fs_return {_} _.
  Arguments fs_arguments {_} _.
  Arguments fs_spec {_} _.

  (* this is the core definition that everything will be based on. *)
  Definition cptr_def {Σ} ti (fs : function_spec Σ) : Rep Σ :=
    as_Rep (fun p =>
         Forall vs,
         [| List.length vs = List.length fs.(fs_arguments) |] -*
         Forall Q, (fs.(fs_spec) ti) vs Q -* fspec p vs ti Q).
  Definition cptr_aux : seal (@cptr_def). by eexists. Qed.
  Definition cptr := cptr_aux.(unseal).
  Definition cptr_eq : @cptr = _ := cptr_aux.(seal_eq).
  Arguments cptr {_}.

  (* (* function specifications written in weakest pre-condition style. *)
  (*  * *)
  (*  * the motivation for `function_spec` is to avoid having to destruct things *)
  (*  * repeatedly; however, they are more difficult to prove things about, so *)
  (*  * it might be better to do this reasoning post-facto. *)
  (*  *) *)
  (* Record function_spec Σ : Type := *)
  (* { fs_return : type *)
  (* ; fs_arguments : list type *)
  (* ; fs_spec : thread_info -> arrowFrom val fs_arguments ((val -> mpred Σ) -> mpred Σ) *)
  (* }. *)
  (* Arguments fs_return {_} _. *)
  (* Arguments fs_arguments {_} _. *)
  (* Arguments fs_spec {_} _. *)

  (* (* this is the core definition that everything will be based on. *) *)
  (* Definition cptr_def {Σ} ti (fs : function_spec Σ) : Rep Σ := *)
  (*  as_Rep (fun p => *)
  (*        ForallEach _ (fs.(fs_spec) ti) (fun PQ args => *)
  (*           Forall Q, PQ Q -* fspec p (List.map snd args) ti Q)). *)
  (* Definition cptr_aux : seal (@cptr_def). by eexists. Qed. *)
  (* Definition cptr := cptr_aux.(unseal). *)
  (* Definition cptr_eq : @cptr = _ := cptr_aux.(seal_eq). *)
  (* Arguments cptr {_}. *)

  Record WithEx Σ : Type :=
    { we_ex   : tele
    ; we_post : we_ex -t> val * mpred Σ }.
  Arguments we_ex {_} _.
  Arguments we_post {_} _.

  Definition WithEx_map {Σ} (f : val -> mpred Σ -> val * mpred Σ) (we : WithEx Σ) : WithEx Σ :=
    {| we_ex := we.(we_ex)
     ; we_post := tele_map (fun '(r,Q) => f r Q) we.(we_post) |}.

  Record WithPrePost Σ : Type :=
    { wpp_with : tele
    ; wpp_pre : wpp_with -t> (list val * mpred Σ)
    ; wpp_post : wpp_with -t> WithEx Σ }.
  Arguments wpp_with {_} _.
  Arguments wpp_pre {_} _.
  Arguments wpp_post {_} _.

  Section with_Σ.
  Context {Σ : gFunctors}.

  Local Notation mpred := (mpred Σ) (only parsing).
  Local Notation Kpreds := (Kpreds Σ) (only parsing).
  Local Notation WithPrePost := (WithPrePost Σ) (only parsing).
  Local Notation function_spec := (function_spec Σ) (only parsing).

  Fixpoint tbi_exist {t : tele} : forall (P : t -t> mpred), mpred :=
    match t as t0 return ((t0 -t> L.mpred Σ) → L.mpred Σ) with
    | [tele] => fun x : L.mpred Σ => x
    | @TeleS X binder =>
      fun P : (∀ x : X, binder x -t> L.mpred Σ) => Exists x : X, tbi_exist (P x)
    end.

  Fixpoint tbi_forall {t : tele} : forall (P : t -t> mpred), mpred :=
    match t as t0 return ((t0 -t> L.mpred Σ) → L.mpred Σ) with
    | [tele] => fun x : L.mpred Σ => x
    | @TeleS X binder =>
      fun P : (∀ x : X, binder x -t> L.mpred Σ) => Forall x : X, tbi_forall (P x)
    end.

  Definition WppD (wpp : WithPrePost) (params : list val) (Q : val -> mpred) : mpred.
  refine (
    tbi_exist (tele_bind (fun args =>
      let P := tele_app wpp.(wpp_pre) args in
      let Q' := tele_app wpp.(wpp_post) args in
      [| params = fst P |] ** snd P ** (tbi_forall (tele_map (fun '(result,Q') => Q' -* Q result) Q'.(we_post)))))).
  Defined.
  Global Arguments WppD !_ / .

  (* Hoare triple for a function.
   * note(gmm): these should include linkage specifications.
   *)
  Definition TSFunction (ret : type) (targs : list type)
             (PQ : thread_info -> WithPrePost)
  : function_spec :=
    {| fs_return    := ret
     ; fs_arguments := targs
     ; fs_spec ti   := WppD (PQ ti) |}.


  Definition SFunction (ret : type) (targs : list type)
             (PQ : WithPrePost)
  : function_spec :=
    TSFunction ret targs (fun _ => PQ).

  (* Hoare triple for a constructor.
   *)
  Definition TSConstructor (class : globname)
             (targs : list type)
             (PQ : thread_info -> val -> WithPrePost)
  : function_spec :=
    let map_pre this '(args, P) :=
        (this :: args,
         _at (_eq this) (uninit (Tref class) 1) ** P) in
    let this_type := Qmut (Tref class) in
    TSFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
               (fun ti =>
                  {| wpp_with := TeleS (fun this : val => (PQ ti this).(wpp_with))
                   ; wpp_pre this :=
                       tele_map (map_pre this) (PQ ti this).(wpp_pre)
                   ; wpp_post this := (PQ ti this).(wpp_post)
                   |}).

  Definition SConstructor (class : globname) (targs : list type)
             (PQ : val -> WithPrePost)
  : function_spec := TSConstructor class targs (fun _ => PQ).

  (* Hoare triple for a destructor.
   *)
  Definition TSDestructor (class : globname) (PQ : thread_info -> val -> WithPrePost)
  : function_spec :=
    let map_pre this '(args, P) := (this :: args, P) in
    let map_post this '({| we_ex := pwiths ; we_post := Q|}) :=
        {| we_ex := pwiths
         ; we_post := tele_map (fun '(result, Q) =>
                                  (result, _at (_eq this) (tany (Tref class) 1) ** Q)) Q |}
    in
    let this_type := Qmut (Tref class) in
    TSFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
               (fun ti =>
                 {| wpp_with := TeleS (fun this : val => (PQ ti this).(wpp_with))
                  ; wpp_pre this :=
                       tele_map (map_pre this) (PQ ti this).(wpp_pre)
                  ; wpp_post this :=
                       tele_map (map_post this) (PQ ti this).(wpp_post)
                  |}).

  Definition SDestructor (class : globname) (PQ : val -> WithPrePost)
  : function_spec := TSDestructor class (fun _ => PQ).

  (* Hoare triple for a method.
   *)
  Definition TSMethod (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : thread_info -> val -> WithPrePost)
  : function_spec :=
    let map_pre this '(args, P) := (this :: args, P) in
    let class_type := Tref class in
    let this_type := Tqualified qual class_type in
    TSFunction ret (Qconst (Tpointer this_type) :: targs)
               (fun ti =>
                  {| wpp_with := TeleS (fun this : val => (PQ ti this).(wpp_with))
                   ; wpp_pre this :=
                       tele_map (map_pre this) (PQ ti this).(wpp_pre)
                   ; wpp_post this := (PQ ti this).(wpp_post)
                   |}).
      (* ^ todo(gmm): this looks wrong. something isn't going
       * to fit together with respect to calling conventions and
       * specifications.
       *)

  Definition SMethod (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : val -> WithPrePost)
  : function_spec := TSMethod class qual ret targs (fun _ => PQ).

Lemma forallEach_primes :
  forall (ts : list type)
    (fs' : arrowFrom val ts ((val -> mpred) -> mpred)) Z,
    Forall vs : list val,
  [| Datatypes.length vs = Datatypes.length ts |] -*
  (Forall Q : val -> mpred,
     applyEach ts vs fs'
               (fun (k : (val -> mpred) -> mpred) (_ : list (type * val)) => k Q) -*
               Z vs Q) -|-
  ForallEach ts fs'
  (fun (PQ : (val -> mpred) -> mpred) (args : list (type * val)) =>
     Forall Q : val -> mpred, PQ Q -* Z (map snd args) Q).
Proof.
  induction ts.
  { simpl. intros.
    split'.
    { eapply lforallR; intro Q.
      eapply (lforallL nil).
      eapply wandSP_only_provableL; [ reflexivity | ].
      eapply lforallL. reflexivity. }
    { eapply lforallR. intros.
      destruct x.
      { eapply wandSP_only_provableR. reflexivity. }
      { eapply wandSP_only_provableR. intros.
        inversion H. } } }
  { simpl. intros.
    split'.
    { eapply lforallR.
      intros.
      specialize (IHts (fs' x) (fun a b => Z (x :: a) b)).
      rewrite <- IHts.
      eapply lforallR. intros.
      eapply (lforallL (x :: x0)).
      eapply wandSP_only_provableR; intros.
      eapply wandSP_only_provableL; [ simpl; f_equal; eassumption | ].
      reflexivity. }
    { eapply lforallR; intros.
      eapply wandSP_only_provableR; intros.
      destruct x.
      { eapply lforallR; intro.
        eapply wandSPAdj'.
        rewrite -> sepSP_falseL.
        eapply lfalseL. }
      { eapply (lforallL v).
        rewrite <- (IHts (fs' v) (fun xs => Z (v :: xs))).
        eapply (lforallL x).
        eapply wandSP_only_provableL.
        simpl in H.
        inversion H. reflexivity. reflexivity. } } }
Qed.

Arguments ForallEach {_ _ _ _} [_] _ _.


  (* Lemma cptr_cptr' : forall ti fs fs', *)
  (*     fs'.(fs'_arguments) = fs.(fs_arguments) -> *)
  (*     fs'.(fs'_return) = fs.(fs_return) -> *)
  (*     (forall Q vs, *)
  (*         (fs'.(fs'_spec) ti) vs Q -|- *)
  (*         applyEach fs.(fs_arguments) vs (fs.(fs_spec) ti) (fun k _ => k Q)) -> *)
  (*     cptr (Σ:=Σ) ti fs -|- cptr' (Σ:=Σ) ti fs'. *)
  (* Proof. *)
  (*   rewrite cptr'_eq. unfold cptr'_def. *)
  (*   rewrite cptr_eq. unfold cptr_def. *)
  (*   intros. *)
  (*   destruct fs, fs'. simpl in *. subst. *)
  (*   eapply Rep_equiv_ext_equiv. simpl; intros. *)
  (*   setoid_rewrite H1; clear H1. *)
  (*   rewrite <- (forallEach_primes) with (Z:=fun a b => fspec x a ti b). *)
  (*   reflexivity. *)
  (* Qed. *)

  Definition cglob_def (gn : globname) ti (spec : function_spec)
  : mpred :=
    _at (_global gn) (cptr ti spec).
  Definition cglob_aux : seal (@cglob_def). by eexists. Qed.
  Definition cglob := cglob_aux.(unseal).
  Definition cglob_eq : @cglob = _ := cglob_aux.(seal_eq).

  Axiom Persistent_cglob : forall p ti fs, Persistent (cglob p ti fs).

  (* i was thinking that i could store static variables in invariants.
   * i'm not sure how this works with function pointer weakening.
   *)
  Axiom Affine_cglob : forall a b c, Affine (cglob a b c).

  (* todo(gmm): this is problematic because if `thread_info` was empty, then
   * the left hand side would be ltrue, not empSP
   *)
  Lemma cglob_weaken_any_ti : forall a c, Affine (Forall ti, cglob a ti c).
  Proof.
    intros.
    eapply bi.forall_affine.
    intros. eapply Affine_cglob.
    Unshelve.
  Admitted.

  Lemma cglob_weaken_any_ti_later :
    forall (a : globname) (c : function_spec),
      (Forall ti, |> cglob a ti c) |-- empSP.
  Proof.
  Admitted.

  Fixpoint bind_type ρ (t : type) (x : ident) (v : val) : mpred :=
    match t with
    | Tqualified _ t => bind_type ρ t x v
    | Treference ref => local_addr_v ρ x v
    | Trv_reference ref => local_addr_v ρ x v
    | Tref _         => local_addr_v ρ x v
    | _              => tlocal ρ x (tprim (erase_qualifiers t) 1 v)
    end.

  Fixpoint bind_type_free ρ (t : type) (x : ident) (v : val) : mpred :=
    match t with
    | Tqualified _ t => bind_type_free ρ t x v
    | Treference ref => local_addr_v ρ x v
    | Trv_reference ref => local_addr_v ρ x v
    | Tref cls       => local_addr_v ρ x v
    | _              => tlocal ρ x (tany (erase_qualifiers t) 1)
    end.

  Fixpoint ForallEaches (ts : list type) : (list (type * val) -> mpred) -> mpred :=
    match ts with
    | nil => fun k => k nil
    | t :: ts => fun k => Forall v : val, ForallEaches ts (fun args => k ((t,v) :: args))
    end.

    (* the proof obligation for a function
     *)
    Definition func_ok (ret : type) (params : list (ident * type))
               (body : Stmt)
               (ti : thread_info) (spec : function_spec)
    : mpred :=
      [| ret = spec.(fs_return) |] **
      [| spec.(fs_arguments) = List.map snd params |] **
      (* forall each argument, apply to [fs_spec ti] *)
      ForallEaches (spec.(fs_arguments)) (fun args =>
        Forall ρ : region,
        let vals := List.map snd args in
        let PQ := spec.(fs_spec) ti vals in

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
          (binds ** PQ (fun x => Q)) -*
          wp ti ρ body (Kfree frees (void_return (|>Q)))
        else if is_aggregate ret then
          Forall Q : val -> mpred,
          Forall ra,
          (binds ** result_addr ρ ra ** _at (_eq ra) (uninit (erase_qualifiers ret) 1) ** PQ Q) -*
          wp ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |> Q x)))
        else
          Forall Q : val -> mpred,
          (binds ** PQ Q) -*
          wp ti ρ body (Kfree frees (val_return (fun x => |> Q x)))).
    (* ^ todo(gmm): the new semantics of function gets an address for a return value
     * so the semantics for `return` should be that *)



    Definition method_ok (meth : Method) (ti : thread_info) (spec : function_spec)
      : mpred :=
      match meth.(m_body) with
      | None => lfalse
      | Some body =>
        let this_type :=
            Qconst (Tpointer (Tqualified meth.(m_this_qual) (Tref meth.(m_class))))
        in
        [| spec.(fs_return) = meth.(m_return) |] **
        [| spec.(fs_arguments) = this_type :: List.map snd meth.(m_params) |] **
        ForallEaches spec.(fs_arguments) (fun args =>
          Forall ρ : region,
          let vals := List.map snd args in
          let PQ := spec.(fs_spec) ti vals in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds :=
                this_addr ρ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type ρ t x v) meth.(m_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                this_addr ρ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type_free ρ t x v) (rev meth.(m_params))
                       (rev rest_vals))
            in
            let ret_ty := meth.(m_return) in
            if is_void ret_ty
            then
              Forall Q : mpred,
              (binds ** PQ (fun x => Q)) -* (wp ti ρ body (Kfree frees (void_return (|>Q))))
            else if is_aggregate ret_ty then
              Forall Q : val -> mpred,
              Forall ra,
              (binds ** result_addr ρ ra ** _at (_eq ra) (uninit (erase_qualifiers ret_ty) 1) ** PQ Q) -* (wp ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |>Q x))))
            else
              Forall Q : val -> mpred,
              (binds ** PQ Q) -* (wp ti ρ body (Kfree frees (val_return (fun x => |>Q x))))
          end)
      end.

    Definition wp_ctor (cls : globname) (ti : thread_info) (ρ : region)
               (this_val : val)
               (inits : list Initializer) (body : Stmt)
               (Q : Kpreds)
    : mpred :=
      wpis ti ρ cls this_val inits
           (fun free => free ** wp ti ρ body Q).


    Definition ctor_ok (ctor : Ctor) ti (spec : function_spec)
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
        ForallEaches spec.(fs_arguments) (fun args =>
          Forall ρ,
          let vals := List.map snd args in
          let PQ := spec.(fs_spec) ti vals in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds :=
                this_addr ρ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type ρ t x v) ctor.(c_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                this_addr ρ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type_free ρ t x v) (rev ctor.(c_params)) (rev rest_vals))
            in
            Forall Q : mpred,
            (binds ** PQ (fun x => Q)) -*
            (wp_ctor ctor.(c_class) ti ρ this_val init body
                     (Kfree frees (void_return (|>Q))))
          end)
      end.

    Definition wp_dtor (cls : globname) (ti : thread_info) (ρ : region)
               (this_val : val)
               (body : Stmt) (dtors : list (FieldOrBase * globname))
               (frees : mpred) (Q : mpred)
    : mpred :=
      wp ti ρ body
         (Kfree frees (void_return (wpds ti ρ cls this_val dtors Q))).

    Definition dtor_ok (dtor : Dtor) ti (spec : function_spec)
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
        ForallEaches spec.(fs_arguments) (fun args =>
          Forall ρ,
          let vals := List.map snd args in
          let PQ := spec.(fs_spec) ti vals in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds := this_addr ρ this_val in
            (* this is what is freed on return *)
            let frees := this_addr ρ this_val in
            Forall Q : mpred,
              (binds ** PQ (fun x => Q)) -*
              (wp_dtor dtor.(d_class) ti ρ this_val body deinit frees (|>Q))
          end)
      end.
  End with_Σ.

End Func.

Declare Module F : Func.

Export F.
