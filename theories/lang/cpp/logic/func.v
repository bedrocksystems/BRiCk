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
     pred path_pred heap_pred
     wp intensional.

Local Open Scope string_scope.


Local Set Universe Polymorphism.

Module Type Func.

  Section with_prop.
    Context {PROP : bi}.

    Record WithEx@{X Z Y} : Type :=
      { we_ex   : tele@{X}
      ; we_post : tele_fun@{X Z Y} we_ex (val * PROP) }.

    Definition WithEx_map (f : val -> PROP -> val * PROP) (we : WithEx) : WithEx :=
      {| we_ex := we.(we_ex)
       ; we_post := tele_map (fun '(r,Q) => f r Q) we.(we_post) |}.

    Record WithPrePost@{X Z Y} : Type :=
      { wpp_with : tele@{X}
      ; wpp_pre  : tele_fun@{X Z Y} wpp_with (list val * PROP)
      ; wpp_post : tele_fun@{X Z Y} wpp_with WithEx@{X Z Z} }.

    Fixpoint tbi_exist@{X Z Y} {t : tele@{X}} : forall (P : tele_fun@{X Z Y} t PROP), PROP :=
      match t as t0 return ((t0 -t> PROP) → PROP) with
      | [tele] => fun x : PROP => x
      | @TeleS X binder =>
        fun P : (∀ x : X, binder x -t> PROP) => Exists x : X, tbi_exist (P x)
      end.

    Fixpoint tbi_forall@{X Z Y} {t : tele@{X}} : forall (P : tele_fun@{X Z Y} t PROP), PROP :=
      match t as t0 return ((t0 -t> PROP) → PROP) with
      | [tele] => fun x : PROP => x
      | @TeleS X binder =>
        fun P : (∀ x : X, binder x -t> PROP) => Forall x : X, tbi_forall (P x)
      end.

    Definition WppD@{X Z Y} (wpp : WithPrePost@{X Z Y}) (params : list val) (Q : val -> PROP) : PROP :=
      tbi_exist@{X Z Y} (tele_bind (TT:=wpp.(wpp_with)) (fun args =>
         let P := tele_app wpp.(wpp_pre) args in
         let Q' := tele_app wpp.(wpp_post) args in
         [| params = fst P |] ** snd P **
         tbi_forall@{X Z Y} (tele_map (fun '(result,Q') => Q' -* Q result) Q'.(we_post)))).

  End with_prop.
  Arguments WithPrePost : clear implicits.
  Arguments Build_WithPrePost _ _ _ : clear implicits.
  Arguments WithEx : clear implicits.
  Arguments Build_WithEx _ _ _ : clear implicits.

  Arguments we_ex {PROP} _.
  Arguments we_post {PROP} _.
  Arguments wpp_with {_} _.
  Arguments wpp_pre {_} _.
  Arguments wpp_post {_} _.

  Global Arguments WppD !_ / .

  Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

    Record function_spec : Type :=
      { fs_return : type
      ; fs_arguments : list type
      ; fs_spec : thread_info -> list val -> (val -> mpred) -> mpred
      }.
  Arguments function_spec : clear implicits.
  Arguments Build_function_spec : clear implicits.

  (* function specifications written in weakest pre-condition style.
   *)

  Definition type_of_spec `(fs : function_spec) : type :=
    normalize_type (Tfunction fs.(fs_return) fs.(fs_arguments)).

  (* this is the core definition that everything will be based on.
   * it is really an assertion about assembly
   *)
  Definition cptr_def (fs : function_spec) : Rep :=
    as_Rep (fun p =>
         Forall vs,
         [| List.length vs = List.length fs.(fs_arguments) |] -*
         Forall Q (ti : thread_info), fs.(fs_spec) ti vs Q -* fspec ti (Vptr p) vs Q).
  Definition cptr_aux : seal (@cptr_def). by eexists. Qed.
  Definition cptr := cptr_aux.(unseal).
  Definition cptr_eq : @cptr = _ := cptr_aux.(seal_eq).

  (* Hoare triple for a function.
   * note(gmm): these should include linkage specifications.
   *)
  Definition TSFunction@{X Z Y} (ret : type) (targs : list type)
             (PQ : thread_info -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    {| fs_return    := ret
     ; fs_arguments := targs
     ; fs_spec ti   := WppD (PQ ti) |}.


  Definition SFunction@{X Z Y} (ret : type) (targs : list type)
             (PQ : WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    {| fs_return    := ret
     ; fs_arguments := targs
     ; fs_spec _    := WppD PQ |}.

  Local Notation uninitR := (@uninitR _ Σ resolve) (only parsing).
  Local Notation anyR := (@anyR _ Σ resolve) (only parsing).
  Local Notation primR := (@primR _ Σ resolve) (only parsing).

  (* Hoare triple for a constructor.
   *)
  Definition SConstructor@{X Z Y} (class : globname)
             (targs : list type)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let map_pre this '(args, P) :=
        (this :: args,
         _at (_eqv this) (uninitR (Tnamed class) 1) ** P) in
    let this_type := Qmut (Tnamed class) in
    SFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
              {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
               ; wpp_pre this :=
                   tele_map (map_pre (Vptr this)) (PQ this).(wpp_pre)
               ; wpp_post this := (PQ this).(wpp_post)
               |}.

  (* Hoare triple for a destructor.
   *)
  Definition SDestructor@{X Z Y} (class : globname)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let map_pre this '(args, P) := (Vptr this :: args, P) in
    let map_post this '{| we_ex := pwiths ; we_post := Q|} :=
        {| we_ex := pwiths
         ; we_post := tele_map (fun '(result, Q) =>
                                  (result, _at (_eq this) (anyR (Tnamed class) 1) ** Q)) Q |}
    in
    let this_type := Qmut (Tnamed class) in
    SFunction@{X Z Y} (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
              {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
               ; wpp_pre this :=
                   tele_map (map_pre this) (PQ this).(wpp_pre)
               ; wpp_post this :=
                   tele_map (map_post this) (PQ this).(wpp_post)
              |}.

  (* Hoare triple for a method.
   *)
  Definition SMethod@{X Z Y} (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let map_pre this '(args, P) := (this :: args, P) in
    let class_type := Tnamed class in
    let this_type := Tqualified qual class_type in
    SFunction ret (Qconst (Tpointer this_type) :: targs)
              {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
               ; wpp_pre this :=
                   tele_map (map_pre (Vptr this)) (PQ this).(wpp_pre)
               ; wpp_post this := (PQ this).(wpp_post)
               |}.
      (* ^ todo(gmm): this looks wrong. something isn't going
       * to fit together with respect to calling conventions and
       * specifications.
       *)

  Local Definition local_addr_v (r : region) (x : ident) (v : val) : mpred :=
    Exists p, [| v = Vptr p |] ** local_addr r x p.

  Fixpoint bind_type ρ (t : type) (x : ident) (v : val) : mpred :=
    match t with
    | Tqualified _ t => bind_type ρ t x v
    | Treference ref => local_addr_v ρ x v
    | Trv_reference ref => local_addr_v ρ x v
    | Tnamed _       => local_addr_v ρ x v
    | _              => Exists a, tlocal_at ρ x a (primR (erase_qualifiers t) 1 v)
    end.

  Fixpoint free_type ρ (t : type) (x : ident) (v : val) : mpred :=
    match t with
    | Tqualified _ t => free_type ρ t x v
    | Treference ref => local_addr_v ρ x v
    | Trv_reference ref => local_addr_v ρ x v
    | Tnamed cls     => local_addr_v ρ x v
    | _              => Exists a, tlocal_at ρ x a (anyR (erase_qualifiers t) 1)
    end.

  Fixpoint ForallEaches (ts : list type) : (list (type * val) -> mpred) -> mpred :=
    match ts with
    | nil => fun k => k nil
    | t :: ts => fun k => Forall v : val, ForallEaches ts (fun args => k ((t,v) :: args))
    end.

    (* the proof obligation for a function
     *)

  Definition wp_func (f : Func) (ti : thread_info) (args : list val) (Q : val -> epred) : mpred :=
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
      end.

  Definition wp_method (meth : Method) ti (args : list val) (Q : val -> epred) : mpred :=
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
    (* ^ todo(gmm): move the [frees] to the left hand side of the [-*], this
     * will make the right-hand-side more canonical
     *)

    (* todo(gmm): i should be able to define this using [wp_func] *)
    Definition func_ok (f : Func)
               (ti : thread_info) (spec : function_spec)
    : mpred :=
      match f.(f_body) with
      | None => lfalse
      | Some body =>
        let params := f.(f_params) in
        let ret := f.(f_return) in
      [| type_of_spec spec = normalize_type (Tfunction ret (List.map snd params)) |] **
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
          Forall Q : mpred,
          (binds ** PQ (fun x => Q)) -*
          wp (resolve:=resolve) ti ρ body (Kfree frees (void_return (|>Q)))
        else if is_aggregate ret then
          Forall Q : val -> mpred,
          Forall ra,
          (binds ** result_addr ρ ra ** _at (_eq ra) (uninitR (erase_qualifiers ret) 1) ** PQ Q) -*
          wp (resolve:=resolve) ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |> Q x)))
        else
          Forall Q : val -> mpred,
          (binds ** PQ Q) -*
          wp (resolve:=resolve) ti ρ body (Kfree frees (val_return (fun x => |> Q x))))
      end.
    (* ^ todo(gmm): the new semantics of function gets an address for a return value
     * so the semantics for `return` should be that *)



    Definition method_ok (meth : Method) (ti : thread_info) (spec : function_spec)
      : mpred :=
      match meth.(m_body) with
      | None => lfalse
      | Some body =>
        let this_type :=
            Qconst (Tpointer (Tqualified meth.(m_this_qual) (Tnamed meth.(m_class))))
        in
        [| type_of_spec spec =
           normalize_type (Tfunction meth.(m_return) (this_type :: List.map snd meth.(m_params))) |] **
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
              Forall Q : mpred,
              (binds ** PQ (fun x => Q)) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (void_return (|>Q))))
            else if is_aggregate ret_ty then
              Forall Q : val -> mpred,
              Forall ra,
              (binds ** result_addr ρ ra ** _at (_eq ra) (uninitR (erase_qualifiers ret_ty) 1) ** PQ Q) -* (wp (resolve:=resolve) ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |>Q x))))
            else
              Forall Q : val -> mpred,
              (binds ** PQ Q) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (val_return (fun x => |>Q x))))
          | _ => lfalse
          end)
      end.
    (* ^ todo(gmm): move the [frees] to the left hand side of the [-*], this
     * will make the right-hand-side more canonical
     *)

    Fixpoint wpis (ti : thread_info) (ρ : region) (cls : globname) (this : val)
             (inits : list Initializer)
             (Q : mpred -> mpred) : mpred :=
      match inits with
      | nil => Q empSP
      | i :: is' => wpi (resolve:=resolve) ti ρ cls this i (fun f => f ** wpis ti ρ cls this is' Q)
      end.


    Definition wp_ctor (cls : globname) (ti : thread_info) (ρ : region)
               (this_val : val)
               (inits : list Initializer) (body : Stmt)
               (Q : Kpreds)
    : mpred :=
      wpis ti ρ cls this_val inits
           (fun free => free ** wp (resolve:=resolve) ti ρ body Q).


    Definition ctor_ok (ctor : Ctor) (ti : thread_info) (spec : function_spec)
    : mpred :=
      match ctor.(c_body) with
      | None => lfalse
      | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
      | Some (UserDefined (init, body)) =>
        let this_type :=
            Qconst (Tpointer (Qmut (Tnamed ctor.(c_class))))
        in
        [| type_of_spec spec =
           normalize_type (Tfunction Tvoid (this_type :: List.map snd ctor.(c_params))) |] **
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
            Forall Q : mpred,
            (binds ** PQ (fun x => Q)) -*
            (wp_ctor ctor.(c_class) ti ρ (Vptr thisp) init body
                     (Kfree frees (void_return (|>Q))))
          | _ => lfalse
          end)
      end.

    Fixpoint wpds (ti : thread_info) (ρ : region)
             (cls : globname) (this : val)
             (dests : list (FieldOrBase * globname))
             (Q : mpred) : mpred :=
      match dests with
      | nil => Q
      | d :: ds => @wpd _ Σ resolve ti ρ cls this d (wpds ti ρ cls this ds Q)
      end.


    Definition wp_dtor (ti : thread_info) (ρ : region) (cls : globname)
               (this_val : val)
               (body : Stmt) (dtors : list (FieldOrBase * globname))
               (frees : mpred) (Q : mpred)
    : mpred :=
      @wp _ Σ resolve ti ρ body
         (Kfree frees (void_return (wpds ti ρ cls this_val dtors Q))).

    Definition dtor_ok (dtor : Dtor) (ti : thread_info) (spec : function_spec)
    : mpred :=
      match dtor.(d_body) with
      | None => lfalse
      | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
      | Some (UserDefined (body, deinit)) =>
        let this_type :=
            Qconst (Tpointer (Qmut (Tnamed dtor.(d_class))))
        in
        [| type_of_spec spec = normalize_type (Tfunction Tvoid (this_type :: nil)) |] **
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
            Forall Q : mpred,
              (binds ** PQ (fun x => Q)) -*
              (wp_dtor ti ρ dtor.(d_class) (Vptr thisp) body deinit frees (|>Q))
          | _ => lfalse
          end)
      end.
  End with_cpp.

End Func.

Declare Module F : Func.

Export F.
