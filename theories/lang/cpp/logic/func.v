(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
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

From bedrock.lang.cpp Require Import ast semantics spec.
From bedrock.lang.cpp Require Import
     pred path_pred heap_pred
     wp intensional.

Local Open Scope string_scope.

Local Set Universe Polymorphism.

Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

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

  Let local_addr_v (r : region) (x : ident) (v : val) : mpred :=
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

  Fixpoint Forall_with_type (ts : list type) : (list (type * val) -> mpred) -> mpred :=
    match ts with
    | nil => fun k => k nil
    | t :: ts => fun k => Forall v : val, Forall_with_type ts (fun args => k ((t,v) :: args))
    end.

  (* the meaning of a function
   *)
  Definition wp_func (f : Func) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
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
          wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid)))
        else if is_aggregate ret then
          Forall ra,
          (binds ** result_addr ρ ra ** _at (_eq ra) (uninitR (erase_qualifiers ret) 1)) -*
          wp (resolve:=resolve) ⊤ ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |> Q x)))
        else
          binds -*
          wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (val_return (fun x => |> Q x)))
      end.

  Definition func_ok (f : Func) (ti : thread_info) (spec : function_spec)
    : mpred :=
      [| type_of_spec spec =
         normalize_type (Tfunction f.(f_return) (List.map snd f.(f_params))) |] **
      (* forall each argument, apply to [fs_spec ti] *)
      □ Forall Q : val -> mpred, Forall vals,
        spec.(fs_spec) ti vals Q -* wp_func f ti vals Q.

  Definition wp_method (meth : Method) ti (args : list val)
             (Q : val -> epred) : mpred :=
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
          binds -* (wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|>Q Vvoid))))
        else if is_aggregate ret_ty then
          Forall ra,
          (binds ** result_addr ρ ra ** _at (_eq ra) (uninitR (erase_qualifiers ret_ty) 1)) -* (wp (resolve:=resolve) ⊤ ti ρ body (Kfree (frees ** result_addr ρ ra) (val_return (fun x => |>Q x))))
        else
          binds -* (wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (val_return (fun x => |>Q x))))
      | _ => lfalse
      end
    end.

  Definition method_ok (m : Method) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec =
       normalize_type (Tfunction m.(m_return) (Tpointer (Tqualified m.(m_this_qual) (Tnamed m.(m_class))) :: List.map snd m.(m_params))) |] **
    (* forall each argument, apply to [fs_spec ti] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_method m ti vals Q.


  Fixpoint wpis (ti : thread_info) (ρ : region) (cls : globname) (this : val)
           (inits : list Initializer)
           (Q : mpred -> mpred) : mpred :=
    match inits with
    | nil => Q empSP
    | i :: is' => wpi (resolve:=resolve) ⊤ ti ρ cls this i (fun f => f ** wpis ti ρ cls this is' Q)
    end.

  Definition wp_ctor (ctor : Ctor) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match ctor.(c_body) with
    | None => lfalse
    | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
    | Some (UserDefined (inits, body)) =>
      let this_type :=
          Qconst (Tpointer (Qmut (Tnamed ctor.(c_class))))
      in
      Forall ρ,
      match args with
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
        binds -*
        wpis ti ρ ctor.(c_class) this_val inits
           (fun free => free **
                      wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid))))
      | _ => lfalse
      end
    end.

  Definition ctor_ok (ctor : Ctor) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec =
       normalize_type (Tfunction Tvoid (Tpointer (Tnamed ctor.(c_class)) :: List.map snd ctor.(c_params))) |] **
    (* forall each argument, apply to [fs_spec ti] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_ctor ctor ti vals Q.

  Fixpoint wpds (ti : thread_info) (ρ : region)
           (cls : globname) (this : val)
           (dests : list (FieldOrBase * globname))
           (Q : mpred) : mpred :=
    match dests with
    | nil => Q
    | d :: ds => @wpd _ Σ resolve ⊤ ti ρ cls this d (wpds ti ρ cls this ds Q)
    end.

  Definition wp_dtor (dtor : Dtor) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match dtor.(d_body) with
    | None => lfalse
    | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
    | Some (UserDefined (body, deinit)) =>
      let this_type :=
          Qconst (Tpointer (Qmut (Tnamed dtor.(d_class))))
      in
      Forall ρ,
      match args with
      | this_val :: rest_vals =>
        Forall thisp, [| this_val = Vptr thisp |] -*
        (* this is what is created from the parameters *)
        let binds := this_addr ρ thisp in
        (* this is what is freed on return *)
        let frees := this_addr ρ thisp in
          binds -*
          wp (resolve:=resolve) ⊤ ti ρ body
          (Kfree frees (void_return (wpds ti ρ dtor.(d_class) this_val deinit (|> Q Vvoid))))
      | _ => lfalse
      end
    end.


  Definition dtor_ok (dtor : Dtor) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec =
       normalize_type (Tfunction Tvoid (Tpointer (Tnamed dtor.(d_class)) :: nil)) |] **
    (* forall each argument, apply to [fs_spec ti] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_dtor dtor ti vals Q.

End with_cpp.
