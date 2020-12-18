(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Lists.List.

Require Import stdpp.telescopes.

From iris.proofmode Require Import tactics.
Require Import bedrock.lang.bi.ChargeCompat.

From bedrock.lang.cpp Require Import ast semantics spec.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred
     wp builtins.
Require Import bedrock.lang.cpp.heap_notations.

Local Set Universe Polymorphism.

Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

  Local Notation _base := (o_base resolve).
  Local Notation _derived := (o_derived resolve).

  (* Hoare triple for a function. *)
  Definition TSFunction@{X Z Y} {cc : calling_conv} (ret : type) (targs : list type)
             (PQ : thread_info -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    {| fs_cc        := cc
     ; fs_return    := ret
     ; fs_arguments := targs
     ; fs_spec ti   := WppD (PQ ti) |}.


  Definition SFunction@{X Z Y} {cc : calling_conv} (ret : type) (targs : list type)
             (PQ : WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    {| fs_cc        := cc
     ; fs_return    := ret
     ; fs_arguments := targs
     ; fs_spec _    := WppD PQ |}.

  Local Notation anyR := (@anyR _ Σ resolve) (only parsing).
  Local Notation primR := (@primR _ Σ resolve) (only parsing).

  (* Hoare triple for a constructor.
   *)
  Definition SConstructor@{X Z Y} {cc : calling_conv} (class : globname)
             (targs : list type)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let this_type := Qmut (Tnamed class) in
    let map_pre this '(args, P) :=
        (Vptr this :: args,
         this |-> anyR (Tnamed class) 1 (* TODO backwards compat [tblockR (Tnamed class)] *) ** P) in
    SFunction (cc:=cc) (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
              {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
               ; wpp_pre this :=
                   tele_map (map_pre this) (PQ this).(wpp_pre)
               ; wpp_post this := (PQ this).(wpp_post)
               |}.

  (* Hoare triple for a destructor.
   *)
  Definition SDestructor@{X Z Y} {cc : calling_conv} (class : globname)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let this_type := Qmut (Tnamed class) in
    let map_pre this '(args, P) := (Vptr this :: args, P) in
    let map_post (this : ptr) '{| we_ex := pwiths ; we_post := Q|} :=
        {| we_ex := pwiths
         ; we_post := tele_map (fun '(result, Q) =>
                                  (result, this |-> anyR (Tnamed class) 1 (* TODO backwards compat [tblockR this_type] *) ** Q)) Q |}
    in
    (** ^ NOTE the size of an object might be different in the presence of virtual base
        classes.
     *)
    SFunction@{X Z Y} (cc:=cc) (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
              {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
               ; wpp_pre this :=
                   tele_map (map_pre this) (PQ this).(wpp_pre)
               ; wpp_post this :=
                   tele_map (map_post this) (PQ this).(wpp_post)
              |}.

  (* Hoare triple for a method.
   *)
  Definition SMethod@{X Z Y} {cc : calling_conv}
             (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let map_pre this '(args, P) := (this :: args, P) in
    let class_type := Tnamed class in
    let this_type := Tqualified qual class_type in
    SFunction (cc:=cc) ret (Qconst (Tpointer this_type) :: targs)
              {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
               ; wpp_pre this :=
                   tele_map (map_pre (Vptr this)) (PQ this).(wpp_pre)
               ; wpp_post this := (PQ this).(wpp_post)
               |}.

  Definition bind_base_this (o : option ptr) (rty : type) (Q : region -> mpred) : mpred :=
    if is_aggregate rty then
      Forall ra : ptr, ra |-> anyR rty 1 (* TODO backwards compat [tblockR (erase_qualifiers rty)] *) -*
                       Q (Remp o (Some ra))
    else Q (Remp o None).

  Definition Rbind_check (x : ident) (p : ptr) (r : region) : region :=
    if decide (x = ""%bs)
    then r
    else Rbind x p r.

  Fixpoint bind_vars (args : list (ident * type)) (vals : list val) (r : region) (Q : region -> FreeTemps -> mpred) : mpred :=
    match args , vals with
    | nil , nil => Q r empSP
    | (x,ty) :: xs , v :: vs  =>
      match drop_qualifiers ty with
      | Tqualified _ t => ltrue (* unreachable *)
      | Treference    _
      | Trv_reference _
      | Tnamed _ =>
        match v with
        | Vptr p => bind_vars xs vs (Rbind_check x p r) Q
        | _ => lfalse
        end
      | _              =>
        Forall a : ptr, a |-> primR (erase_qualifiers ty) 1 v -*
        bind_vars xs vs (Rbind_check x a r) (fun r free => Q r (a |-> anyR (erase_qualifiers ty) 1 ** free))
      end
    | _ , _ => lfalse
    end.

  (* the meaning of a function
   *)
  Definition wp_func (f : Func) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match f.(f_body) with
    | None => lfalse
    | Some body =>
      match body with
      | Impl body =>
        bind_base_this None f.(f_return) (fun ρ =>
        bind_vars f.(f_params) args ρ (fun ρ frees =>
        if is_void f.(f_return) then
          wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid)))
        else
          wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (val_return (fun x => |> Q x)))))
      | Builtin builtin =>
        wp_builtin ⊤ ti builtin (Tfunction (cc:=f.(f_cc)) f.(f_return) (List.map snd f.(f_params))) args Q
      end
    end.

  Definition func_ok (f : Func) (ti : thread_info) (spec : function_spec)
    : mpred :=
      [| type_of_spec spec = type_of_value (Ofunction f) |] **
      (* forall each argument, apply to [fs_spec ti] *)
      □ Forall Q : val -> mpred, Forall vals,
        spec.(fs_spec) ti vals Q -* wp_func f ti vals Q.

  Definition wp_method (m : Method) ti (args : list val)
             (Q : val -> epred) : mpred :=
    match m.(m_body) with
    | None => lfalse
    | Some body =>
      match args with
      | Vptr thisp :: rest_vals =>
        bind_base_this (Some thisp) m.(m_return) (fun ρ =>
        bind_vars m.(m_params) rest_vals ρ (fun ρ frees =>
        if is_void m.(m_return) then
          wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|>Q Vvoid)))
        else
          wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (val_return (fun x => |>Q x)))))
      | _ => lfalse
      end
    end.

  Definition method_ok (m : Method) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Omethod m) |] **
    (* forall each argument, apply to [fs_spec ti] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_method m ti vals Q.

  Fixpoint all_identities' (f : nat) (mdc : option globname) (cls : globname) : Rep :=
    match f with
    | 0 => False
    | S f =>
      match resolve.(genv_tu).(globals) !! cls with
      | Some (Gstruct st) =>
        identityR cls mdc 1 **
        [∗list] b ∈ st.(s_bases),
           let '(base,_) := b in
           _base cls base |-> all_identities' f mdc base
      | _ => False
      end
    end.

  Definition all_identities : option globname -> globname -> Rep :=
    let size := avl.IM.cardinal resolve.(genv_tu).(globals) in
    (* ^ the number of global entries is an upper bound on the height of the
       derivation tree.
     *)
    all_identities' size.

  (* this function creates an [_instance_of] fact for this class *and*,
     transitively, updates all of the [_instance_of] assertions for all base
     classes.
   *)
  Definition init_identity (cls : globname) (Q : mpred) : Rep :=
    match resolve.(genv_tu).(globals) !! cls with
    | Some (Gstruct st) =>
      ([∗list] b ∈ st.(s_bases),
         let '(base,_) := b in
         _base cls base |-> all_identities (Some base) base) **
       identityR cls None 1 **
      (identityR cls (Some cls) 1 -*
       ([∗list] b ∈ st.(s_bases),
          let '(base,_) := b in
          _base cls base |-> all_identities (Some cls) base) -* pureR Q)
    | _ => lfalse
    end.

  (* initialization of members in the initializer list *)
  Fixpoint wpi_members
           (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
           (inits : list Initializer)
           (Q : mpred -> mpred) : mpred :=
    match inits with
    | nil => Q empSP
    | i :: is' =>
      match i.(init_path) with
      | This
      | Base _ => False
      | _ =>
        (* TODO backwards compat [this ., offset_for _ cls i.(init_path) |-> tblockR i.(init_type) -*] *)
        wpi (resolve:=resolve) ⊤ ti ρ cls this i (fun f => f ** wpi_members ti ρ cls this is' Q)
      end
    end.

  (* initialization of bases in the initializer list *)
  Fixpoint wpi_bases (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
           (inits : list Initializer)
           (Q : mpred -> mpred) : mpred :=
    match inits with
    | nil => this |-> init_identity cls (Q empSP)
    | i :: is' =>
      match i.(init_path) with
      | Field _
      | Indirect _ _ =>
        this |-> init_identity cls (wpi_members ti ρ cls this inits Q)
      | This =>
        (* this is a delegating constructor *)
        [| is' = nil |] **
        [| drop_qualifiers i.(init_type) = Tnamed cls |] **
        ((* TODO backwards compat [this |-> tblockR i.(init_type) -*] *) wpi (resolve:=resolve) ⊤ ti ρ cls this i Q)
        (* the constructor that we are delegating to will already initialize the object
         * identity, so we don't have to do that here.
         *)
      | Base _ =>
        (* TODO backwards compat [this ., offset_for _ cls i.(init_path) |-> tblockR i.(init_type) -*] *)
        wpi (resolve:=resolve) ⊤ ti ρ cls this i (fun f => f ** wpi_bases ti ρ cls this is' Q)
      end
    end.

  (* note(gmm): supporting virtual inheritence will require us to add
   * constructor kinds here
   *
   * NOTE that the constructor semantics consumes the entire [blockR] of the object
   * that is being constructed and the C++ abstract machine breaks this block down
   * and provides each sub-block immediately before the initialization of the field
   * or base.
   *)
  Definition wp_ctor (ctor : Ctor)
             (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match ctor.(c_body) with
    | None => False
    | Some Defaulted => False
      (* ^ defaulted constructors are not supported yet *)
    | Some (UserDefined (inits, body)) =>
      match args with
      | Vptr thisp :: rest_vals =>
        let ty := Tnamed ctor.(c_class) in
        (* TODO backwards compat [thisp |-> tblockR ty **] *)
        (* ^ this requires that you give up the *entire* block of memory that the object
           will use.
         *)
        bind_base_this (Some thisp) Tvoid (fun ρ =>
        bind_vars ctor.(c_params) rest_vals ρ (fun ρ frees =>
          (wpi_bases ti ρ ctor.(c_class) thisp inits
              (fun free => free **
                             (type_ptr ty thisp -* wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid))))))))
      | _ => False
      end
    end.

  Definition ctor_ok (ctor : Ctor) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Oconstructor ctor) |] **
    (* forall each argument, apply to [fs_spec ti] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_ctor ctor ti vals Q.

  Definition revert_identity (cls : globname) (Q : mpred) : Rep :=
    match resolve.(genv_tu).(globals) !! cls with
    | Some (Gstruct st) =>
      identityR cls (Some cls) 1 **
      ([∗list] b ∈ st.(s_bases),
          let '(base,_) := b in
          _base cls base |-> all_identities (Some cls) base) **
      (identityR cls None 1 -*
       ([∗list] b ∈ st.(s_bases),
         let '(base,_) := b in
         _base cls base |-> all_identities (Some base) base) -* pureR Q)
    | _ => lfalse
    end.

  Fixpoint wpd_bases (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
           (dests : list (FieldOrBase * globname))
           (Q : mpred) : mpred :=
    match dests with
    | nil => Q
    | d :: is' =>
      match d.1 with
      | Field _
      | Indirect _ _
      | This => False
      | Base b => wpd (resolve:=resolve) ⊤ ti ρ cls this d
                ((* TODO backwards compat [this ., offset_for _ cls d.1 |-> tblockR (Tnamed b) **] *) wpd_bases ti ρ cls this is' Q)
      end
    end.

  Fixpoint wpd_members
           (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
           (dests : list (FieldOrBase * globname))
           (Q : mpred) : mpred :=
    match dests with
    | nil => this |-> revert_identity cls Q
    | d :: is' =>
      match d.1 with
      | This
      | Indirect _ _ => False
      | Base _ =>
        this |-> revert_identity cls (wpd_bases ti ρ cls this dests Q)
      | _ =>
        match type_of_path cls d.1 with
        | Some ty =>
          wpd (resolve:=resolve) ⊤ ti ρ cls this d (
            (* TODO backwards compat [this ., offset_for _ cls d.1 |-> tblockR ty **] *)
                     wpd_members ti ρ cls this is' Q)
        | None => False
        end
      end
    end.

  Definition wp_dtor (dtor : Dtor) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match dtor.(d_body) with
    | None => False
    | Some Defaulted => False
      (* ^ defaulted constructors are not supported *)
    | Some (UserDefined (body, deinit)) =>
      match args with
      | Vptr thisp :: rest_vals =>
        bind_base_this (Some thisp) Tvoid (fun ρ =>
        wp (resolve:=resolve) ⊤ ti ρ body
           (void_return (wpd_members ti ρ dtor.(d_class) thisp deinit
                (|> ((* TODO backwards compat [thisp |-> tblockR (Tnamed dtor.(d_class)) -*] *) Q Vvoid)))))
      | _ => False
      end
    end.

  Definition dtor_ok (dtor : Dtor) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Odestructor dtor) |] **
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_dtor dtor ti vals Q.

End with_cpp.
