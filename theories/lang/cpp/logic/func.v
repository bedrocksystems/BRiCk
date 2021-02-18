(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Lists.List.

Require Import stdpp.telescopes.

From iris.proofmode Require Import tactics.
Require Import bedrock.lang.bi.ChargeCompat.

From bedrock.lang.cpp Require Import ast semantics spec.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred
     wp builtins.
Require Import bedrock.lang.cpp.logic.destroy.
Require Import bedrock.lang.cpp.heap_notations.

#[local] Set Universe Polymorphism.

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

  (* Hoare triple for a constructor.
   *)
  Definition SConstructor@{X Z Y} {cc : calling_conv} (class : globname)
             (targs : list type)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let this_type := Qmut (Tnamed class) in
    let map_pre this '(args, P) :=
        (Vptr this :: args,
         this |-> tblockR (Tnamed class) 1 ** P) in
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
                                  (result, this |-> tblockR (Tnamed class) 1 ** Q)) Q |}
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

  Fixpoint bind_vars (args : list (ident * type)) (vals : list val) (r : region) (Q : region -> FreeTemps -> mpred) : mpred :=
    match args , vals with
    | nil , nil => Q r emp
    | (x,ty) :: xs , v :: vs  =>
      match drop_qualifiers ty with
      | Tqualified _ t => True (* unreachable *)
      | Treference    _
      | Trv_reference _
      | Tnamed _ =>
        match v with
        | Vptr p => bind_vars xs vs (Rbind_check x p r) Q
        | _ => False
        end
      | _              =>
        Forall a : ptr, a |-> primR (erase_qualifiers ty) 1 v -*
        bind_vars xs vs (Rbind_check x a r) (fun r free => Q r (a |-> anyR (erase_qualifiers ty) 1 ** free))
        (* TODO the use of [anyR] above is a bit strange. *)
      end
    | _ , _ => False
    end%I.

  Lemma bind_vars_frame : forall ts args ρ Q Q',
      (Forall ρ free, Q ρ free -* Q' ρ free) |-- bind_vars ts args ρ Q -* bind_vars ts args ρ Q'.
  Proof.
    induction ts; destruct args => /= *; eauto.
    { iIntros "A B"; iApply "A"; eauto. }
    { iIntros "A B". destruct a.
      destruct (typing.drop_qualifiers t);
        try solve
            [ iIntros (?) "X"; iDestruct ("B" with "X") as "B"; iRevert "B"; iApply IHts; iIntros (? ?) "Z"; iApply "A"; iFrame
            | destruct v; eauto; iRevert "B"; iApply IHts; eauto ]. }
  Qed.

  (* the meaning of a function
   *)
  Definition wp_func (f : Func) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match f.(f_body) with
    | None => False
    | Some body =>
      match body with
      | Impl body =>
        let ρ := Remp None f.(f_return) in
        bind_vars f.(f_params) args ρ (fun ρ frees =>
        |> if is_void f.(f_return) then
             wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid)))
           else
             wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (val_return (fun x => |> Q x))))
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
        let ρ := Remp (Some thisp) m.(m_return) in
        bind_vars m.(m_params) rest_vals ρ (fun ρ frees =>
        |> if is_void m.(m_return) then
             wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|>Q Vvoid)))
           else
             wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (val_return (fun x => |>Q x))))
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
           (members : list Member) (inits : list Initializer)
           (Q : mpred) : mpred :=
    match members with
    | nil => Q
    | m :: members =>
      match List.filter (fun i =>
                           match i.(init_path) with
                           | InitField x
                           | InitIndirect ((x,_) :: _) _ => bool_decide (m.(mem_name) = x)
                           | _ => false
                           end) inits with
      | nil =>
        (* there is no initializer for this member, so we "default initialize" it
           (see https://eel.is/c++draft/dcl.init#general-7 )
         *)
        False
      | i :: is' =>
        match i.(init_path) with
        | InitField _ (* = m.(mem_name) *) =>
          match is' with
          | nil =>
            (* there is a *unique* initializer for this field *)
            this ., offset_for _ cls i.(init_path) |-> tblockR i.(init_type) 1 -*
            wpi (resolve:=resolve) ⊤ ti ρ cls this i (fun f => f ** wpi_members ti ρ cls this members inits Q)
          | _ =>
            (* there are multiple initializers for this field *)
            False
          end
        | InitIndirect _ _ =>
          (* this is initializing an object via sub-objets using indirect initialization.
             TODO currently not supported
           *)
          False
        | _ => False (* unreachable due to the filter *)
        end
      end
    end%I.

  (* initialization of bases in the initializer list *)
  Fixpoint wpi_bases (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
           (bases : list globname) (inits : list Initializer)
           (Q : mpred) : mpred :=
    match bases with
    | nil => Q
    | b :: bases =>
      match List.filter (fun i => bool_decide (i.(init_path) = InitBase b)) inits with
      | nil =>
        (* there is no initializer for this base class, so we use the default constructor *)
        False
      | i :: nil =>
        (* there is an initializer for this class *)
        this ., offset_for _ cls i.(init_path) |-> tblockR i.(init_type) 1 -*
        wpi (resolve:=resolve) ⊤ ti ρ cls this i (fun f => f ** wpi_bases ti ρ cls this bases inits Q)
      | _ :: _ :: _ =>
        (* there are multiple initializers for this, so we fail *)
        False
      end
    end%I.

  Definition wp_initializer_list  (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
             (inits : list Initializer) (Q : mpred) : mpred :=
    match List.find (fun i => bool_decide (i.(init_path) = InitThis)) inits with
    | Some {| init_type := ty ; init_init := e |} =>
      match inits with
      | _ :: nil =>
        if bool_decide (drop_qualifiers ty = Tnamed cls) then
          (* this is a delegating constructor, simply delegate *)
          (this |-> tblockR ty 1 -* wp_init ⊤ ti ρ (Tnamed cls) this e (fun free => free ** Q))
        else
          (* the type names do not match, this should never happen *)
          False
      | _ =>
        (* delegating constructors are not allowed to have any other initializers
         *)
        False
      end
    | None =>
      match resolve.(genv_tu).(globals) !! cls with
      | Some (Gstruct s) =>
        let bases := wpi_bases ti ρ cls this (List.map fst s.(s_bases)) inits in
        let members := wpi_members ti ρ cls this s.(s_fields) inits in
        let ident Q := this |-> init_identity cls Q in
        (** initialize the bases, then the identity, then the members *)
        bases (ident (members (type_ptr (Tnamed cls) this -* Q)))
        (* TODO here we are constructing the [type_ptr] after the members have been initialized
           TODO we should also get [_padding] and anything else here.
         *)
      | _ =>
        (* We only support initializer lists for struct/class. *)
        False
      end
    end%I.

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
        thisp |-> tblockR ty 1 **
        (* ^ this requires that you give up the *entire* block of memory that the object
           will use.
         *)
        let ρ := Remp (Some thisp) Tvoid in
        bind_vars ctor.(c_params) rest_vals ρ (fun ρ frees =>
          wp_initializer_list ti ρ ctor.(c_class) thisp inits
              (type_ptr ty thisp -* wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid)))))
              (* TODO shoudl we get [type_ptr] here instead of above? if so, then construction (might not be) compositional in the
                 way that we want it to be
               *)
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
    | _ => False
    end.

  Fixpoint wpd_bases
           (ti : thread_info) (cls : globname) (this : ptr)
           (bases : list globname)
           (Q : mpred) : mpred :=
    match bases with
    | nil => Q
    | base :: bases =>
      destruct_val (σ:=resolve) ti (Tnamed base) (this ., _base cls base) None (wpd_bases ti cls this bases Q)
    end.

  Fixpoint wpd_members
           (ti : thread_info) (cls : globname) (this : ptr)
           (members : list Member)
           (Q : mpred) : mpred :=
    match members with
    | nil => Q
    | member :: members =>
      destruct_val (σ:=resolve) ti member.(mem_type) (this ., _field {| f_name := member.(mem_name) ; f_type := cls |}) None
                   (wpd_members ti cls this members Q)
    end.

  Definition wp_dtor (dtor : Dtor) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match dtor.(d_body) with
    | None => False
    | Some Defaulted => False
      (* ^ defaulted constructors are not supported *)
    | Some (UserDefined body) =>
      match resolve.(genv_tu).(globals) !! dtor.(d_class) with
      | Some (Gstruct s) =>
        match args with
        | Vptr thisp :: nil =>
          let ρ := Remp (Some thisp) Tvoid in
            wp (resolve:=resolve) ⊤ ti ρ body
               (void_return (wpd_members ti dtor.(d_class) thisp s.(s_fields)
                               (thisp |-> revert_identity dtor.(d_class) (wpd_bases ti dtor.(d_class) thisp (List.map fst s.(s_bases))
                                                                     (|> (thisp |-> tblockR (Tnamed dtor.(d_class)) 1 -* Q Vvoid)))))))
        | _ => False
        end
      | Some (Gunion u) =>
        match args with
        | Vptr thisp :: nil =>
          let ρ := Remp (Some thisp) Tvoid in
            wp (resolve:=resolve) ⊤ ti ρ body
               (void_return (|> thisp |-> tblockR (Tnamed dtor.(d_class)) 1 -* Q Vvoid)))
        | _ => False
        end
      | _ => False
      end
    end.

  Definition dtor_ok (dtor : Dtor) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Odestructor dtor) |] **
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_dtor dtor ti vals Q.

End with_cpp.

