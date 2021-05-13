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
     wp builtins layout initializers.
Require Import bedrock.lang.cpp.logic.destroy.
Require Import bedrock.lang.cpp.heap_notations.
Require Import bedrock.lang.bi.errors.

#[local] Set Universe Polymorphism.
Arguments ERROR {_ _} _%bs.

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
      | Tqualified _ t => ERROR "unreachable" (* unreachable *)
      | Treference    _
      | Trv_reference _
      | Tnamed _ =>
        match v with
        | Vptr p => bind_vars xs vs (Rbind_check x p r) Q
        | _ => ERROR "non-pointer passed for aggregate"
        end
      | _              =>
        Forall a : ptr, a |-> primR (erase_qualifiers ty) 1 v -*
        bind_vars xs vs (Rbind_check x a r) (fun r free => Q r (a |-> anyR (erase_qualifiers ty) 1 ** free))
        (* Here we view [anyR (erase_quaifiers ty) 1] as essentially the pre-condition
           to the "destructor" of a primitive. *)
      end
    | _ , _ => ERROR "bind_vars: argument mismatch"
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
    | _ => False
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
        default_initialize m.(mem_type) (this ., _field {| f_type := cls ; f_name := m.(mem_name) |}) (fun _ => Q)
      | i :: is' =>
        match i.(init_path) with
        | InitField _ (* = m.(mem_name) *) =>
          match is' with
          | nil =>
            (* there is a *unique* initializer for this field *)
            this ., offset_for cls i.(init_path) |-> tblockR (erase_qualifiers i.(init_type)) 1 -*
            wpi (resolve:=resolve) ⊤ ti ρ cls this i (fun f => f ** wpi_members ti ρ cls this members inits Q)
          | _ =>
            (* there are multiple initializers for this field *)
            ERROR "multiple initializers for field"
          end
        | InitIndirect _ _ =>
          (* this is initializing an object via sub-objets using indirect initialization.
             TODO currently not supported
           *)
          UNSUPPORTED "indirect initialization"
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
        ERROR "missing base class initializer"
      | i :: nil =>
        (* there is an initializer for this class *)
        this ., offset_for cls i.(init_path) |-> tblockR (erase_qualifiers i.(init_type)) 1 -*
        wpi (resolve:=resolve) ⊤ ti ρ cls this i (fun f => f ** wpi_bases ti ρ cls this bases inits Q)
      | _ :: _ :: _ =>
        (* there are multiple initializers for this, so we fail *)
        ERROR "multiple initializers for base"
      end
    end%I.

  Lemma wpi_bases_frame:
    ∀ (ti : thread_info) ρ (p : ptr) (ty : globname) bases (inits : list Initializer) (Q Q' : mpredI),
      (Q -* Q')
        |-- wpi_bases ti ρ ty p bases inits Q -*
        wpi_bases ti ρ ty p bases inits Q'.
  Proof.
    induction bases => /=; eauto.
    intros.
    case_match; eauto.
    case_match; eauto.
    iIntros "a b c"; iDestruct ("b" with "c") as "b"; iRevert "b".
    iApply wpi_frame; first by reflexivity.
    iIntros (f) "[$ b]"; iRevert "b".
      by iApply IHbases.
  Qed.

  Lemma wpi_members_frame:
    ∀ (ti : thread_info) (ρ : region) flds (p : ptr) (ty : globname) (li : list Initializer) (Q Q' : mpredI),
      (Q -* Q') |-- wpi_members ti ρ ty p flds li Q -*
                wpi_members ti ρ ty p flds li Q'.
  Proof.
    induction flds => /=; eauto.
    intros.
    case_match.
    { iIntros "a"; iApply default_initialize_frame; iIntros (?); eauto. }
    { case_match; eauto.
      case_match; eauto.
      iIntros "a b c"; iDestruct ("b" with "c") as "b". iRevert "b".
      iApply wpi_frame; first by reflexivity.
      iIntros (?) "[$ x]"; iRevert "x"; iApply IHflds; eauto. }
  Qed.

  Definition wp_struct_initializer_list (s : Struct) (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
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
          ERROR "type name mismatch"
      | _ =>
        (* delegating constructors are not allowed to have any other initializers
         *)
        ERROR "delegating constructor has other initializers"
      end
    | None =>
      let bases := wpi_bases ti ρ cls this (List.map fst s.(s_bases)) inits in
      let members := wpi_members ti ρ cls this s.(s_fields) inits in
      let ident Q := this |-> init_identity cls Q in
      (** initialize the bases, then the identity, then the members *)
      bases (ident (members (type_ptr (Tnamed cls) this -* this |-> struct_padding 1 cls -*  Q)))
      (* NOTE here we are constructing the [type_ptr] for the *full object*
         after we have provided the [type_ptr] for the individual fields.
         TODO we should also get [_padding] and anything else here.
         NOTE [struct_padding] now implies [type_ptr], so this is a little bit redundant.
       *)
    end%I.

  Lemma wp_struct_initializer_list_frame : forall ti ρ cls p ty li Q Q',
      (Q -* Q') |-- wp_struct_initializer_list cls ti ρ ty p li Q -* wp_struct_initializer_list cls ti ρ ty p li Q'.
  Proof.
    rewrite /wp_struct_initializer_list/=. intros. case_match.
    { case_match => //.
      destruct l; eauto.
      case_match; eauto.
      iIntros "X Y Z".
      iDestruct ("Y" with "Z") as "Y"; iRevert "Y".
      iApply wp_init_frame. reflexivity. iIntros (?) "[$ ?]"; iApply "X"; eauto. }
    {
      iIntros "a"; iApply wpi_bases_frame.
      rewrite /init_identity.
      case_match; eauto.
      case_match; eauto.
      rewrite !_at_sep !_at_wand !_at_pureR.
      iIntros "[$ [$ x]]".
      iIntros "b c"; iDestruct ("x" with "b c") as "x".
      iRevert "x"; iApply wpi_members_frame. iIntros "b c d".
      iApply "a".
      iApply ("b" with "c d"). }
  Qed.

  Definition wp_union_initializer_list (s : translation_unit.Union) (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
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
          ERROR "type name mismatch"
      | _ =>
        (* delegating constructors are not allowed to have any other initializers
         *)
        ERROR "delegating constructor has other initializers"
      end
    | None =>
      UNSUPPORTED "union initialization"
      (* TODO what is the right thing to do when initializing unions? *)
    end%I.

  (* TODO this is easy to prove, but will be replaced fairly soon. *)
  Lemma wp_union_initializer_list_frame : forall ti ρ cls p ty li Q Q',
      (Q -* Q') |-- wp_union_initializer_list cls ti ρ ty p li Q -* wp_union_initializer_list cls ti ρ ty p li Q'.
  Proof.
    rewrite /wp_union_initializer_list/=. intros. case_match; eauto.
    { case_match => //.
      destruct l; eauto.
      case_bool_decide; eauto.
      iIntros "X Y Z".
      iDestruct ("Y" with "Z") as "Y"; iRevert "Y".
      iApply wp_init_frame. reflexivity. iIntros (?) "[$ ?]"; iApply "X"; eauto. }
  Qed.

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
        match resolve.(genv_tu).(globals) !! ctor.(c_class) with
        | Some (Gstruct cls) =>
          (* this is a structure *)
          thisp |-> tblockR ty 1 **
          (* ^ this requires that you give up the *entire* block of memory that the object
             will use.
           *)
          |> let ρ := Remp (Some thisp) Tvoid in
             bind_vars ctor.(c_params) rest_vals ρ (fun ρ frees =>
               (wp_struct_initializer_list cls ti ρ ctor.(c_class) thisp inits
                  (wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid))))))
        | Some (Gunion union) =>
        (* this is a union *)
          thisp |-> tblockR ty 1 **
          (* ^ this requires that you give up the *entire* block of memory that the object
             will use.
           *)
          |> let ρ := Remp (Some thisp) Tvoid in
             bind_vars ctor.(c_params) rest_vals ρ (fun ρ frees =>
               (wp_union_initializer_list union ti ρ ctor.(c_class) thisp inits
                  (wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid))))))
        | Some _ =>
          ERROR "constructor for non-aggregate"
        | None => False
        end
      | _ => ERROR "constructor without leading [this] argument"
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
      destruct_val (σ:=resolve) ti false (Tnamed base) (this ., _base cls base) None (wpd_bases ti cls this bases Q)
    end.

  Fixpoint wpd_members
           (ti : thread_info) (cls : globname) (this : ptr)
           (members : list Member)
           (Q : mpred) : mpred :=
    match members with
    | nil => Q
    | member :: members =>
      (** TODO this needs to actually invoke a destructor if one exists *)
      destruct_val (σ:=resolve) ti false member.(mem_type) (this ., _field {| f_name := member.(mem_name) ; f_type := cls |}) None
                   (wpd_members ti cls this members Q)
    end.

  (** [wp_dtor dtor ti args Q] defines the semantics of the destructor [dtor] when
      applied to [args] with post-condition [Q].
   *)
  Definition wp_dtor (dtor : Dtor) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match dtor.(d_body) with
    | None => False
    | Some Defaulted => False
      (* ^ defaulted constructors are not supported *)
    | Some (UserDefined body) =>
      let epilog :=
          match resolve.(genv_tu).(globals) !! dtor.(d_class) with
          | Some (Gstruct s) => Some $ fun thisp : ptr =>
            thisp |-> struct_padding 1 dtor.(d_class) **
            wpd_members ti dtor.(d_class) thisp s.(s_fields)
               (* ^ fields are destroyed *)
               (thisp |-> revert_identity dtor.(d_class)
               (* ^ the identity of the object is destroyed *)
                  (wpd_bases ti dtor.(d_class) thisp (List.map fst s.(s_bases))
                  (* ^ the base classes are destroyed (reverse order) *)
                     (thisp |-> tblockR (Tnamed dtor.(d_class)) 1 -* |> Q Vvoid)))
                     (* ^ the operations above destroy each object returning its memory to
                        the abstract machine. Then the abstract machine gives this memory
                        back to the program.
                        NOTE the [|>] here is for the function epilog.
                      *)
          | Some (Gunion u) => Some $ fun thisp : ptr =>
            (* the function epilog of a union destructor doesn't actually destroy anything
               because it isn't clear what to destroy (this is dictated by the C++ standard).
               Instead, the epilog provides a fancy update to destroy things.

               In practice, this means that programs can only destroy unions
               automatically where they can prove the active entry has a trivial destructor.
             *)
            |={⊤}=> thisp |-> tblockR (Tnamed dtor.(d_class)) 1 **
                   (thisp |-> tblockR (Tnamed dtor.(d_class)) 1 -* |> Q Vvoid)
          | _ => None
          end%I
      in
      match epilog , args with
      | Some epilog , Vptr thisp :: nil =>
        let ρ := Remp (Some thisp) Tvoid in
          |> (* the function prolog consumes a step. *)
             wp (resolve:=resolve) ⊤ ti ρ body
               (void_return (epilog thisp))
      | _ , _ => False
      end
    end.

(*
  template<typename T>
  struct optional {
    union U { T val; char nothing[sizeof(T)]; ~u() {} } u;
    bool has_value;
    ~optional() {
      if (has_value)
        val.~T();

    } // has_value.~bool(); u.~U();
  }

  p |-> classR .... -* |==> p |-> tblockR "class" 1

  union { int x; short y; } u;
    // u |-> tblockR "U" 1
    // CREATE(0)
    u.x = 1;
    // DESTROY(0)
    // CREATE(1)
    u.y = 1;
    // DESTROY(1)
    // u |-> tblockR "U" 1

    // [CREATE(n)] implicit pick a union branch
    u |-> tblockR "U" 1 ==*
        u |-> (upaddingR "U" 1 ** ucaseR "U" 0 1 ** _field "x" |-> uninitR "U" 1)
    // [DESTROY(n)] implicit "destruction" of the union
    u |-> (upaddingR "U" 1 ** ucaseR "U" 0 1 ** _field "x" |-> uninitR "U" 1) ==*
        u |-> tblockR "U" 1
*)

  Definition dtor_ok (dtor : Dtor) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Odestructor dtor) |] **
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_dtor dtor ti vals Q.

End with_cpp.

