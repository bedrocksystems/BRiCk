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
     pred heap_pred wp intensional (* initializers destructors call intensional *).

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

  (* this is the core definition that everything will be based on.
   * it is really an assertion about assembly
   *)
  Definition cptr_def {Σ} ti (fs : function_spec Σ) : Rep Σ :=
    as_Rep (fun p =>
         Forall vs,
         [| List.length vs = List.length fs.(fs_arguments) |] -*
         Forall Q, fs.(fs_spec) ti vs Q -* fspec (Vptr p) ti vs Q).
  Definition cptr_aux : seal (@cptr_def). by eexists. Qed.
  Definition cptr := cptr_aux.(unseal).
  Definition cptr_eq : @cptr = _ := cptr_aux.(seal_eq).
  Arguments cptr {Σ}.

  Record WithEx@{X Z Y} Σ : Type :=
    { we_ex   : tele@{X}
    ; we_post : tele_fun@{X Z Y} we_ex (val * mpred Σ) }.
  Arguments we_ex {Σ} _.
  Arguments we_post {Σ} _.

  Definition WithEx_map {Σ} (f : val -> mpred Σ -> val * mpred Σ) (we : WithEx Σ) : WithEx Σ :=
    {| we_ex := we.(we_ex)
     ; we_post := tele_map (fun '(r,Q) => f r Q) we.(we_post) |}.

  Record WithPrePost@{X Z Y} Σ : Type :=
    { wpp_with : tele@{X}
    ; wpp_pre  : tele_fun@{X Z Y} wpp_with (list val * mpred Σ)
    ; wpp_post : tele_fun@{X Z Y} wpp_with (WithEx@{X Z Z} Σ) }.
  Arguments wpp_with {_} _.
  Arguments wpp_pre {_} _.
  Arguments wpp_post {_} _.

  Section with_Σ.
  Context {Σ : gFunctors} {resolve:genv}.

  Fixpoint tbi_exist@{X Z Y} {t : tele@{X}} : forall (P : tele_fun@{X Z Y} t (mpred Σ)), mpred Σ :=
    match t as t0 return ((t0 -t> L.mpred Σ) → L.mpred Σ) with
    | [tele] => fun x : L.mpred Σ => x
    | @TeleS X binder =>
      fun P : (∀ x : X, binder x -t> L.mpred Σ) => Exists x : X, tbi_exist (P x)
    end.

  Fixpoint tbi_forall@{X Z Y} {t : tele@{X}} : forall (P : tele_fun@{X Z Y} t (mpred Σ)), mpred Σ :=
    match t as t0 return ((t0 -t> L.mpred Σ) → L.mpred Σ) with
    | [tele] => fun x : L.mpred Σ => x
    | @TeleS X binder =>
      fun P : (∀ x : X, binder x -t> L.mpred Σ) => Forall x : X, tbi_forall (P x)
    end.

  Definition WppD@{X Z Y} (wpp : WithPrePost@{X Z Y} Σ) (params : list val) (Q : val -> mpred Σ) : mpred Σ.
  refine (
    tbi_exist@{X Z Y} (tele_bind (TT:=wpp.(wpp_with)) (fun args =>
      let P := tele_app wpp.(wpp_pre) args in
      let Q' := tele_app wpp.(wpp_post) args in
      [| params = fst P |] ** snd P ** (tbi_forall@{X Z Y} (tele_map (fun '(result,Q') => Q' -* Q result) Q'.(we_post)))))).
  Defined.
  Global Arguments WppD !_ / .


  (* Hoare triple for a function.
   * note(gmm): these should include linkage specifications.
   *)
  Definition TSFunction@{X Z Y} (ret : type) (targs : list type)
             (PQ : thread_info -> WithPrePost@{X Z Y} Σ)
  : function_spec Σ :=
    {| fs_return    := ret
     ; fs_arguments := targs
     ; fs_spec ti   := WppD (PQ ti) |}.

  Definition SFunction@{X Z  Y} (ret : type) (targs : list type)
             (PQ : WithPrePost@{X Z Y} Σ)
  : function_spec Σ :=
    TSFunction ret targs (fun _ => PQ).

  Local Notation uninitR := (@uninitR Σ resolve) (only parsing).
  Local Notation anyR := (@anyR Σ resolve) (only parsing).
  Local Notation primR := (@primR Σ resolve) (only parsing).

  (* Hoare triple for a constructor.
   *)
  Definition TSConstructor@{X Z Y} (class : globname)
             (targs : list type)
             (PQ : thread_info -> ptr -> WithPrePost@{X Z Y} Σ)
  : function_spec Σ :=
    let map_pre this '(args, P) :=
        (this :: args,
         _at (_eqv this) (uninitR (Tref class) 1) ** P) in
    let this_type := Qmut (Tref class) in
    TSFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
               (fun ti =>
                  {| wpp_with := TeleS (fun this : ptr => (PQ ti this).(wpp_with))
                   ; wpp_pre this :=
                       tele_map (map_pre (Vptr this)) (PQ ti this).(wpp_pre)
                   ; wpp_post this := (PQ ti this).(wpp_post)
                   |}).

  Definition SConstructor@{X Z Y} (class : globname) (targs : list type)
             (PQ : ptr -> WithPrePost@{X Z Y} Σ)
  : function_spec Σ := TSConstructor class targs (fun _ => PQ).

  (* Hoare triple for a destructor.
   *)
  Definition TSDestructor@{X Z Y} (class : globname)
             (PQ : thread_info -> ptr -> WithPrePost@{X Z Y} Σ)
  : function_spec Σ :=
    let map_pre this '(args, P) := (Vptr this :: args, P) in
    let map_post this '({| we_ex := pwiths ; we_post := Q|}) :=
        {| we_ex := pwiths
         ; we_post := tele_map (fun '(result, Q) =>
                                  (result, _at (_eq this) (anyR (Tref class) 1) ** Q)) Q |}
    in
    let this_type := Qmut (Tref class) in
    TSFunction@{X Z Y} (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
               (fun ti =>
                 {| wpp_with := TeleS (fun this : ptr => (PQ ti this).(wpp_with))
                  ; wpp_pre this :=
                       tele_map (map_pre this) (PQ ti this).(wpp_pre)
                  ; wpp_post this :=
                       tele_map (map_post this) (PQ ti this).(wpp_post)
                  |}).

  Definition SDestructor@{X Z Y} (class : globname) (PQ : ptr -> WithPrePost@{X Z Y} Σ)
  : function_spec Σ := TSDestructor class (fun _ => PQ).

  (* Hoare triple for a method.
   *)
  Definition TSMethod@{X Z Y} (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : thread_info -> ptr -> WithPrePost@{X Z Y} Σ)
  : function_spec Σ :=
    let map_pre this '(args, P) := (this :: args, P) in
    let class_type := Tref class in
    let this_type := Tqualified qual class_type in
    TSFunction ret (Qconst (Tpointer this_type) :: targs)
               (fun ti =>
                  {| wpp_with := TeleS (fun this : ptr => (PQ ti this).(wpp_with))
                   ; wpp_pre this :=
                       tele_map (map_pre (Vptr this)) (PQ ti this).(wpp_pre)
                   ; wpp_post this := (PQ ti this).(wpp_post)
                   |}).
      (* ^ todo(gmm): this looks wrong. something isn't going
       * to fit together with respect to calling conventions and
       * specifications.
       *)

  Definition SMethod@{X Z Y} (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : ptr -> WithPrePost@{X Z Y} Σ)
  : function_spec Σ := TSMethod class qual ret targs (fun _ => PQ).

  Local Definition local_addr_v (r : region) (x : ident) (v : val) : mpred Σ :=
    Exists p, [| v = Vptr p |] ** local_addr r x p.

  Fixpoint bind_type ρ (t : type) (x : ident) (v : val) : mpred Σ :=
    match t with
    | Tqualified _ t => bind_type ρ t x v
    | Treference ref => local_addr_v ρ x v
    | Trv_reference ref => local_addr_v ρ x v
    | Tref _         => local_addr_v ρ x v
    | _              => tlocal ρ x (primR (erase_qualifiers t) 1 v)
    end.

  Fixpoint free_type ρ (t : type) (x : ident) (v : val) : mpred Σ :=
    match t with
    | Tqualified _ t => free_type ρ t x v
    | Treference ref => local_addr_v ρ x v
    | Trv_reference ref => local_addr_v ρ x v
    | Tref cls       => local_addr_v ρ x v
    | _              => tlocal ρ x (anyR (erase_qualifiers t) 1)
    end.

  Fixpoint ForallEaches (ts : list type) : (list (type * val) -> mpred Σ) -> mpred Σ :=
    match ts with
    | nil => fun k => k nil
    | t :: ts => fun k => Forall v : val, ForallEaches ts (fun args => k ((t,v) :: args))
    end.

    (* the proof obligation for a function
     *)

  Definition wp_func (f : Func) (ti : thread_info) (args : list val) (Q : val -> epred Σ) : mpred Σ.
  refine (
      match f.(f_body) with
      | None => lfalse
      | Some body =>
        let ret := f.(f_return) in
        Forall ρ : region,
        (* this is what is created from the parameters *)
        let binds :=
            sepSPs (zip_with (fun '(x, t) 'v => bind_type ρ t x v) f.(f_params) args) in
        (* this is what is freed on return *)
        let frees :=
            sepSPs (zip_with (fun '(x, t) 'v => free_type ρ t x v) (rev f.(f_params)) (rev args)) in
        ([| length args = length f.(f_params) |] ** ltrue) //\\
        if is_void ret
        then
          binds -*
          wp (resolve:=resolve) ti ρ body (Kfree frees (void_return (|> Q Vvoid)))
        else if is_aggregate ret then
          Forall ra,
          (binds ** result_addr ρ ra ** _at (_eq ra) (uninitR (erase_qualifiers ret) 1)) -*
          wp (resolve:=resolve) ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |> Q x)))
        else
          binds -*
          wp (resolve:=resolve) ti ρ body (Kfree frees (val_return (fun x => |> Q x)))
      end).
  Defined.

    Definition wp_method (meth : Method) (ti : thread_info) (args : list val) (Q : val -> epred Σ) : mpred Σ.
    refine
      match meth.(m_body) with
      | None => lfalse
      | Some body =>
          Forall ρ : region,
          match args with
          | this_val :: rest_vals =>
            Forall thisp, [| this_val = Vptr thisp |] -*
            (* this is what is created from the parameters *)
            let binds :=
                this_addr ρ thisp **
                sepSPs (zip_with (fun '(x, t) 'v => bind_type ρ t x v) meth.(m_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                this_addr ρ thisp **
                sepSPs (zip_with (fun '(x, t) 'v => free_type ρ t x v) (rev meth.(m_params))
                       (rev rest_vals))
            in
            let ret_ty := meth.(m_return) in
            ([| (length args = 1 + length meth.(m_params))%nat |] ** ltrue) //\\
            if is_void ret_ty
            then
              binds -* (wp (resolve:=resolve) ti ρ body (Kfree frees (void_return (|>Q Vvoid))))
            else if is_aggregate ret_ty then
              Forall ra,
              (binds ** result_addr ρ ra ** _at (_eq ra) (uninitR (erase_qualifiers ret_ty) 1)) -* (wp (resolve:=resolve) ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |>Q x))))
            else
              binds -* (wp (resolve:=resolve) ti ρ body (Kfree frees (val_return (fun x => |>Q x))))
          | _ => lfalse
          end
      end.
    Defined.
    (* ^ todo(gmm): move the [frees] to the left hand side of the [-*], this
     * will make the right-hand-side more canonical
     *)

    (* todo(gmm): i should be able to define this using [wp_func] *)
    Definition func_ok (ret : type) (params : list (ident * type))
               (body : Stmt)
               (ti : thread_info) (spec : function_spec Σ)
    : mpred Σ :=
      [| ret = spec.(fs_return) |] **
      [| spec.(fs_arguments) = List.map snd params |] **
      (* forall each argument, apply to [fs_spec ti] *)
      ForallEaches (spec.(fs_arguments)) (fun args =>
        Forall ρ : region,
        let vals := List.map snd args in
        let PQ := spec.(fs_spec) ti vals in

        (* this is what is created from the parameters *)
        let binds :=
            sepSPs (zip_with (fun '(x, t) 'v => bind_type ρ t x v) params vals) in
        (* this is what is freed on return *)
        let frees :=
            sepSPs (zip_with (fun '(x, t) 'v => free_type ρ t x v)
                   (rev params) (rev vals)) in
        if is_void ret
        then
          Forall Q : mpred Σ,
          (binds ** PQ (fun x => Q)) -*
          wp (resolve:=resolve) ti ρ body (Kfree frees (void_return (|>Q)))
        else if is_aggregate ret then
          Forall Q : val -> mpred Σ,
          Forall ra,
          (binds ** result_addr ρ ra ** _at (_eq ra) (uninitR (erase_qualifiers ret) 1) ** PQ Q) -*
          wp (resolve:=resolve) ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |> Q x)))
        else
          Forall Q : val -> mpred Σ,
          (binds ** PQ Q) -*
          wp (resolve:=resolve) ti ρ body (Kfree frees (val_return (fun x => |> Q x)))).
    (* ^ todo(gmm): the new semantics of function gets an address for a return value
     * so the semantics for `return` should be that *)



    Definition method_ok (meth : Method) (ti : thread_info) (spec : function_spec Σ)
      : mpred Σ :=
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
          | this_val :: rest_vals =>
            Forall thisp, [| this_val = Vptr thisp |] -*
            (* this is what is created from the parameters *)
            let binds :=
                this_addr ρ thisp **
                sepSPs (zip_with (fun '(x, t) 'v => bind_type ρ t x v) meth.(m_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                this_addr ρ thisp **
                sepSPs (zip_with (fun '(x, t) 'v => free_type ρ t x v) (rev meth.(m_params))
                       (rev rest_vals))
            in
            let ret_ty := meth.(m_return) in
            if is_void ret_ty
            then
              Forall Q : mpred Σ,
              (binds ** PQ (fun x => Q)) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (void_return (|>Q))))
            else if is_aggregate ret_ty then
              Forall Q : val -> mpred Σ,
              Forall ra,
              (binds ** result_addr ρ ra ** _at (_eq ra) (uninitR (erase_qualifiers ret_ty) 1) ** PQ Q) -* (wp (resolve:=resolve) ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |>Q x))))
            else
              Forall Q : val -> mpred Σ,
              (binds ** PQ Q) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (val_return (fun x => |>Q x))))
          | _ => lfalse
          end)
      end.
    (* ^ todo(gmm): move the [frees] to the left hand side of the [-*], this
     * will make the right-hand-side more canonical
     *)

    Fixpoint wpis (ti : thread_info) (ρ : region)  (cls : globname) (this : val)
             (inits : list Initializer)
             (Q : mpred Σ -> mpred Σ) : mpred Σ :=
      match inits with
      | nil => Q empSP
      | i :: is' => wpi (resolve:=resolve) ti ρ cls this i (fun f => f ** wpis ti ρ cls this is' Q)
      end.


    Definition wp_ctor (cls : globname) (ti : thread_info) (ρ : region)
               (this_val : val)
               (inits : list Initializer) (body : Stmt)
               (Q : Kpreds Σ)
    : mpred Σ :=
      wpis ti ρ cls this_val inits
           (fun free => free ** wp (resolve:=resolve) ti ρ body Q).


    Definition ctor_ok (ctor : Ctor) ti (spec : function_spec Σ)
    : mpred Σ :=
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
          | this_val :: rest_vals =>
            Forall thisp, [| this_val = Vptr thisp |] -*
            (* this is what is created from the parameters *)
            let binds :=
                this_addr ρ thisp **
                sepSPs (zip_with (fun '(x, t) 'v => bind_type ρ t x v) ctor.(c_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                this_addr ρ thisp **
                sepSPs (zip_with (fun '(x, t) 'v => free_type ρ t x v) (rev ctor.(c_params)) (rev rest_vals))
            in
            Forall Q : mpred Σ,
            (binds ** PQ (fun x => Q)) -*
            (wp_ctor ctor.(c_class) ti ρ (Vptr thisp) init body
                     (Kfree frees (void_return (|>Q))))
          | _ => lfalse
          end)
      end.

    Fixpoint wpds ti ρ
             (cls : globname) (this : val)
             (dests : list (FieldOrBase * globname))
             (Q : mpred Σ) : mpred Σ :=
      match dests with
      | nil => Q
      | d :: ds => @wpd Σ resolve ti ρ cls this d (wpds ti ρ cls this ds Q)
      end.


    Definition wp_dtor (cls : globname) (ti : thread_info) (ρ : region)
               (this_val : val)
               (body : Stmt) (dtors : list (FieldOrBase * globname))
               (frees : mpred Σ) (Q : mpred Σ)
    : mpred Σ :=
      @wp Σ resolve ti ρ body
         (Kfree frees (void_return (wpds ti ρ cls this_val dtors Q))).

    Definition dtor_ok (dtor : Dtor) ti (spec : function_spec Σ)
    : mpred Σ :=
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
          | this_val :: rest_vals =>
            Forall thisp, [| this_val = Vptr thisp |] -*
            (* this is what is created from the parameters *)
            let binds := this_addr ρ thisp in
            (* this is what is freed on return *)
            let frees := this_addr ρ thisp in
            Forall Q : mpred Σ,
              (binds ** PQ (fun x => Q)) -*
              (wp_dtor dtor.(d_class) ti ρ (Vptr thisp) body deinit frees (|>Q))
          | _ => lfalse
          end)
      end.
  End with_Σ.

End Func.

Declare Module F : Func.

Export F.
