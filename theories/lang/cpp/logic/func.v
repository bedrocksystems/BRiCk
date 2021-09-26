(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.bi.ChargeCompat.
Require Import bedrock.lang.bi.errors.
Require Import bedrock.lang.cpp.logic.entailsN.
Require Import iris.proofmode.tactics.	(** Early to get the right [ident] *)
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
  pred path_pred heap_pred wp builtins
  layout initializers destroy.
Require Import bedrock.lang.cpp.heap_notations.

#[local] Set Printing Coercions.

Arguments ERROR {_ _} _%bs.
Arguments UNSUPPORTED {_ _} _%bs.

Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

  #[local] Open Scope free_scope.

  #[local] Notation _base := (o_base resolve).
  #[local] Notation _derived := (o_derived resolve).

  Definition Kfree (free : FreeTemp) : KpredI -> KpredI :=
    Kat_exit (interp free).

  (** * Aggregate identity *)
  #[local] Fixpoint all_identities' (f : nat) (mdc : option globname) (cls : globname) : Rep :=
    match f with
    | 0 => False
    | S f =>
      match resolve.(genv_tu).(globals) !! cls with
      | Some (Gstruct st) =>
        (if has_vtable st then identityR cls mdc 1 else emp) **
        [∗list] b ∈ st.(s_bases),
           let '(base,_) := b in
           _base cls base |-> all_identities' f mdc base
      | _ => False
      end
    end.

  (** [this |-> all_identities mdc cls] is all of the object identities
      of the [this] object where [this] is of type [cls*] and is part of
      a most-derived-class [cls].
   *)
  Definition all_identities : option globname -> globname -> Rep :=
    let size := avl.IM.cardinal resolve.(genv_tu).(globals) in
    (* ^ the number of global entries is an upper bound on the height of the
       derivation tree.
     *)
    all_identities' size.

  (* [init_identities cls Q] initializes the identities of this function creates an [_instance_of] fact for this class *and*,
     transitively, updates all of the [_instance_of] assertions for all base
     classes.
   *)
  Definition init_identity (cls : globname) (Q : mpred) : Rep :=
    match resolve.(genv_tu).(globals) !! cls with
    | Some (Gstruct st) =>
      ([∗list] b ∈ st.(s_bases),
         let '(base,_) := b in
         _base cls base |-> all_identities (Some base) base) **
      ((if has_vtable st then identityR cls (Some cls) 1 else emp) -*
       ([∗list] b ∈ st.(s_bases),
          let '(base,_) := b in
          _base cls base |-> all_identities (Some cls) base) -* pureR Q)
    | _ => False
    end.

  Theorem init_identity_frame cls Q Q' :
    pureR (Q' -* Q) |-- init_identity cls Q' -* init_identity cls Q.
  Proof.
    rewrite /init_identity.
    case_match; eauto.
    case_match; eauto.
    iIntros "X [$ Y] Z K".
    iDestruct ("Y" with "Z K") as "Y".
    iStopProof. rewrite -pureR_sep. apply pureR_mono.
    iIntros "[X Y]"; iApply "X"; eauto.
  Qed.

  Definition revert_identity (cls : globname) (Q : mpred) : Rep :=
    match resolve.(genv_tu).(globals) !! cls with
    | Some (Gstruct st) =>
      (if has_vtable st then identityR cls (Some cls) 1 else emp) **
      ([∗list] b ∈ st.(s_bases),
          let '(base,_) := b in
          _base cls base |-> all_identities (Some cls) base) **
      (([∗list] b ∈ st.(s_bases),
         let '(base,_) := b in
         _base cls base |-> all_identities (Some base) base) -* pureR Q)
    | _ => False
    end.

  Theorem revert_identity_frame cls Q Q' :
    pureR (Q' -* Q) |-- revert_identity cls Q' -* revert_identity cls Q.
  Proof.
    rewrite /revert_identity.
    case_match; eauto.
    case_match; eauto.
    iIntros "X [$ [$ Y]] Z".
    iDestruct ("Y" with "Z") as "Y".
    iStopProof. rewrite -pureR_sep. apply pureR_mono.
    iIntros "[X Y]"; iApply "X"; eauto.
  Qed.

  (** sanity chect that initialization and revert are inverses *)
  Corollary init_revert cls Q (p : ptr) st :
    globals (genv_tu resolve) !! cls = Some (Gstruct st) ->
    let REQ :=
        ([∗ list] b ∈ s_bases st,
          let '(base, _) := b in
          _base cls base |-> all_identities (Some base) base)%I
    in
        p |-> REQ ** Q
    |-- p |-> init_identity cls (p |-> revert_identity cls (p |-> REQ ** Q)).
  Proof.
    rewrite /revert_identity/init_identity => ->.
    rewrite !_at_sep !_at_wand !_at_pureR.
    iIntros "[$ $] $ $ $".
  Qed.

  (** * Binding parameters *)

  (** [bind_vars args vals r Q] preforms initialization of the parameters
      given the values being passed.

      TODO this is technically inaccurate, because the caller of the function
      should be constructing the pointers. In this setup, [vals] should
      just be a list of [ptr] and the signature would be:
      [bind_vars : list (ident * type) -> list ptr -> region -> region]
   *)
  Fixpoint bind_vars (args : list (ident * type)) (vals : list val) (r : region) (Q : region -> FreeTemps -> mpred) : mpred :=
    match args , vals with
    | nil , nil => Q r FreeTemps.id
    | (x,ty) :: xs , v :: vs  =>
      match drop_qualifiers ty with
      | Tqualified _ t => ERROR "unreachable" (* unreachable *)
      | Treference    _
      | Trv_reference _ =>
        match v with
        | Vptr p => bind_vars xs vs (Rbind_check x p r) Q
        | _ => ERROR $ "non-pointer passed for reference"
        end
      | Tnamed nm =>
        match v with
        | Vptr p => bind_vars xs vs (Rbind_check x p r) Q
        | _ => ERROR $ "non-pointer passed for aggregate (named " ++ nm ++ ")"
        end
      | _              =>
        Forall a : ptr, a |-> primR (erase_qualifiers ty) 1 v -*
        bind_vars xs vs (Rbind_check x a r) (fun r free => Q r (FreeTemps.delete (erase_qualifiers ty) a |*| free))
      end

    (* the (more) correct definition would rely on the caller to create primitive
       values (in the logic). See the note on [wp_args']. The corresponding implementation
       here would be the following:
      match v with
      | Vptr p => bind_vars xs vs (Rbind_check x p r) Q
      | _ => ERROR "non-pointer passed to function (the caller is responsible for constructing objects)"
      end
     *)
    | _ , _ => ERROR "bind_vars: argument mismatch"
    end%I%bs.

  Lemma bind_vars_frame : forall ts args ρ Q Q',
        Forall ρ free, Q ρ free -* Q' ρ free
    |-- bind_vars ts args ρ Q -* bind_vars ts args ρ Q'.
  Proof.
    induction ts; destruct args => /= *; eauto.
    { iIntros "A B"; iApply "A"; eauto. }
    { iIntros "A B". destruct a.
      destruct (typing.drop_qualifiers t);
        try solve
            [ iIntros (?) "X"; iDestruct ("B" with "X") as "B"; iRevert "B";
              iApply IHts; iIntros (? ?) "Z"; iApply "A"; iFrame
            | destruct v; eauto; iRevert "B"; iApply IHts; eauto ]. }
  Qed.

  (** * Weakest preconditions of the flavors of C++ "functions"  *)

  (** ** the weakest precondition of a function *)
  Definition wp_func (f : Func) (args : list val)
             (Q : val -> epred) : mpred :=
    match f.(f_body) with
    | None => False
    | Some body =>
      match body with
      | Impl body =>
        let ρ := Remp None f.(f_return) in
        bind_vars f.(f_params) args ρ (fun ρ frees =>
        |> if is_void f.(f_return) then
             wp ⊤ ρ body (Kfree frees $ void_return (|={⊤}=> |> Q Vvoid))
           else
             wp ⊤ ρ body (Kfree frees $ val_return (fun x => |={⊤}=> |> Q x)))
      | Builtin builtin =>
        wp_builtin ⊤ builtin (Tfunction (cc:=f.(f_cc)) f.(f_return) (List.map snd f.(f_params))) args Q
      end
    end.

  Definition func_ok (f : Func) (spec : function_spec)
    : mpred :=
      [| type_of_spec spec = type_of_value (Ofunction f) |] **
      (* forall each argument, apply to [fs_spec] *)
      □ Forall Q : val -> mpred, Forall vals,
        spec.(fs_spec) vals Q -* wp_func f vals Q.

  (** ** The weakest precondition of a method *)
  Definition wp_method (m : Method) (args : list val)
             (Q : val -> epred) : mpred :=
    match m.(m_body) with
    | None => False
    | Some (UserDefined body) =>
      match args with
      | Vptr thisp :: rest_vals =>
        let ρ := Remp (Some thisp) m.(m_return) in
        bind_vars m.(m_params) rest_vals ρ (fun ρ frees =>
        |> if is_void m.(m_return) then
             wp ⊤ ρ body (Kfree frees (void_return (|={⊤}=> |>Q Vvoid)))
           else
             wp ⊤ ρ body (Kfree frees (val_return (fun x => |={⊤}=> |>Q x))))
      | _ => False
      end
    | Some _ => UNSUPPORTED "defaulted methods"%bs
    end.

  Definition method_ok (m : Method) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Omethod m) |] **
    (* forall each argument, apply to [fs_spec] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) vals Q -* wp_method m vals Q.

  (** ** Weakest precondition of a constructor *)

  (* initialization of members in the initializer list *)
  Fixpoint wpi_members
           (ρ : region) (cls : globname) (this : ptr)
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
        default_initialize m.(mem_type)
          (this ., _field {| f_type := cls ; f_name := m.(mem_name) |})
          (fun frees => interp frees (wpi_members ρ cls this members inits Q))
      | i :: is' =>
        match i.(init_path) with
        | InitField _ (* = m.(mem_name) *) =>
          match is' with
          | nil =>
            (* there is a *unique* initializer for this field *)
            this ., offset_for cls i.(init_path) |-> tblockR (erase_qualifiers i.(init_type)) 1 -*
            wpi ⊤ ρ cls this i (wpi_members ρ cls this members inits Q)
          | _ =>
            (* there are multiple initializers for this field *)
            ERROR $ "multiple initializers for field: " ++ cls ++ "::" ++ m.(mem_name)
          end
        | InitIndirect _ _ =>
          (* this is initializing an object via sub-objets using indirect initialization.
             TODO currently not supported
           *)
          UNSUPPORTED $ "indirect initialization: " ++ cls ++ "::" ++ m.(mem_name)
        | _ => False (* unreachable due to the filter *)
        end
      end
    end%I%bs.

  (* initialization of bases in the initializer list *)
  Fixpoint wpi_bases (ρ : region) (cls : globname) (this : ptr)
           (bases : list globname) (inits : list Initializer)
           (Q : mpred) : mpred :=
    match bases with
    | nil => Q
    | b :: bases =>
      match List.filter (fun i => bool_decide (i.(init_path) = InitBase b)) inits with
      | nil =>
        (* there is no initializer for this base class, so we use the default constructor *)
        ERROR $ "missing base class initializer: " ++ cls
      | i :: nil =>
        (* there is an initializer for this class *)
        this ., offset_for cls i.(init_path) |-> tblockR (erase_qualifiers i.(init_type)) 1 -*
        wpi ⊤ ρ cls this i (wpi_bases ρ cls this bases inits Q)
      | _ :: _ :: _ =>
        (* there are multiple initializers for this, so we fail *)
        ERROR $ "multiple initializers for base: " ++ cls ++ "::" ++ b
      end
    end%I%bs.

  Lemma wpi_bases_frame:
    ∀ ρ (p : ptr) (ty : globname) bases (inits : list Initializer) (Q Q' : mpredI),
      Q -* Q'
      |-- wpi_bases ρ ty p bases inits Q -* wpi_bases ρ ty p bases inits Q'.
  Proof.
    induction bases => /=; eauto.
    intros.
    case_match; eauto.
    case_match; eauto.
    iIntros "a b c"; iDestruct ("b" with "c") as "b"; iRevert "b".
    iApply wpi_frame => //.
    by iApply IHbases.
  Qed.

  Lemma wpi_members_frame:
    ∀ (ρ : region) flds (p : ptr) (ty : globname) (li : list Initializer) (Q Q' : mpredI),
      Q -* Q'
      |-- wpi_members ρ ty p flds li Q -* wpi_members ρ ty p flds li Q'.
  Proof.
    induction flds => /=; eauto; intros.
    case_match.
    { iIntros "a"; iApply default_initialize_frame.
      iIntros (?); iApply interp_frame. by iApply IHflds. }
    { case_match; eauto.
      case_match; eauto.
      iIntros "a b c"; iDestruct ("b" with "c") as "b". iRevert "b".
      iApply wp_initialize_frame => //; iIntros (?); iApply interp_frame; by iApply IHflds. }
  Qed.

  Definition wp_struct_initializer_list (s : Struct) (ρ : region) (cls : globname) (this : ptr)
             (inits : list Initializer) (Q : mpred) : mpred :=
    match List.find (fun i => bool_decide (i.(init_path) = InitThis)) inits with
    | Some {| init_type := ty ; init_init := e |} =>
      match inits with
      | _ :: nil =>
        if bool_decide (drop_qualifiers ty = Tnamed cls) then
          (* this is a delegating constructor, simply delegate *)
          this |-> tblockR ty 1 -* wp_init ⊤ ρ (Tnamed cls) this e (fun free => interp free Q)
        else
          (* the type names do not match, this should never happen *)
          ERROR "type name mismatch"
      | _ =>
        (* delegating constructors are not allowed to have any other initializers
         *)
        ERROR "delegating constructor has other initializers"
      end
    | None =>
      let bases := wpi_bases ρ cls this (List.map fst s.(s_bases)) inits in
      let members := wpi_members ρ cls this s.(s_fields) inits in
      let ident Q := this |-> init_identity cls Q in
      (** initialize the bases, then the identity, then the members *)
      bases (ident (members (this |-> struct_paddingR 1 cls -*  Q)))
      (* NOTE we get the [struct_paddingR] at the end since
         [struct_paddingR 1 cls |-- type_ptrR (Tnamed cls)].
       *)
    end.

  Lemma wp_struct_initializer_list_frame : forall ρ cls p ty li Q Q',
      Q -* Q' |-- wp_struct_initializer_list cls ρ ty p li Q -* wp_struct_initializer_list cls ρ ty p li Q'.
  Proof.
    rewrite /wp_struct_initializer_list/=. intros. case_match.
    { case_match => //.
      destruct l; eauto.
      case_match; eauto.
      iIntros "x y z".
      iDestruct ("y" with "z") as "y"; iRevert "y"; iApply wp_init_frame => //.
      iIntros (?); by iApply interp_frame. }
    { iIntros "a"; iApply wpi_bases_frame.
      rewrite /init_identity.
      case_match; eauto.
      case_match; eauto.
      rewrite !_at_sep !_at_wand !_at_pureR.
      iIntros "[$ x]".
      iIntros "b c"; iDestruct ("x" with "b c") as "x".
      iRevert "x"; iApply wpi_members_frame. iIntros "b c".
      iApply "a".
      iApply ("b" with "c"). }
  Qed.

  Definition wp_union_initializer_list (s : translation_unit.Union) (ρ : region) (cls : globname) (this : ptr)
             (inits : list Initializer) (Q : mpred) : mpred :=
    match List.find (fun i => bool_decide (i.(init_path) = InitThis)) inits with
    | Some {| init_type := ty ; init_init := e |} =>
      match inits with
      | _ :: nil =>
        if bool_decide (drop_qualifiers ty = Tnamed cls) then
          (* this is a delegating constructor, simply delegate *)
          this |-> tblockR ty 1 -* wp_init ⊤ ρ (Tnamed cls) this e (fun free => interp free Q)
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
    end%bs%I.

  Lemma wp_union_initializer_list_frame : forall ρ cls p ty li Q Q',
        Q -* Q'
    |-- wp_union_initializer_list cls ρ ty p li Q -*
        wp_union_initializer_list cls ρ ty p li Q'.
  Proof.
    rewrite /wp_union_initializer_list/=. intros. case_match; eauto.
    { case_match => //.
      destruct l; eauto.
      case_bool_decide; eauto.
      iIntros "X Y Z".
      iDestruct ("Y" with "Z") as "Y"; iRevert "Y".
      iApply wp_init_frame. reflexivity. iIntros (?); by iApply interp_frame. }
  Qed.

  (* [type_validity ty p] is the pointer validity of a class that is learned
     at the beginning of the constructor.

     Generally, it is the **strict** validity of all of the sub-objects.
     [[
         type_validity (Tnamed cls) this
     |-- strict_valid_ptr this **
         [∗list] f ∈ s_fields , type_validity f.(f_type) (this ., _field f)
     ]]

     TODO we leave this trivival for now.
   *)
  Definition type_valdity : type -> ptr -> mpred := fun _ _ => emp%I.

  (* note(gmm): supporting virtual inheritence will require us to add
   * constructor kinds here
   *
   * NOTE that the constructor semantics consumes the entire [blockR] of the object
   * that is being constructed and the C++ abstract machine breaks this block down
   * and provides each sub-block immediately before the initialization of the field
   * or base.
   *
   * Alternative: it would also be sound for the class to provide the [tblockR]
   * for each sub-object up front.
   *)
  Definition wp_ctor (ctor : Ctor) (args : list val) (Q : val -> epred) : mpred :=
    match ctor.(c_body) with
    | None => False
    | Some Defaulted => UNSUPPORTED "defaulted constructors"
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
               (wp_struct_initializer_list cls ρ ctor.(c_class) thisp inits
                  (wp ⊤ ρ body (Kfree frees (void_return (|={⊤}=> |> Q Vvoid))))))
        | Some (Gunion union) =>
        (* this is a union *)
          thisp |-> tblockR ty 1 **
          (* ^ this requires that you give up the *entire* block of memory that the object
             will use.
           *)
          |> let ρ := Remp (Some thisp) Tvoid in
             bind_vars ctor.(c_params) rest_vals ρ (fun ρ frees =>
               (wp_union_initializer_list union ρ ctor.(c_class) thisp inits
                  (wp ⊤ ρ body (Kfree frees (void_return (|={⊤}=> |> Q Vvoid))))))
        | Some _ =>
          ERROR $ "constructor for non-aggregate (" ++ ctor.(c_class) ++ ")"
        | None => False
        end
      | _ => ERROR "constructor without leading [this] argument"
      end
    end%I%bs.

  Definition ctor_ok (ctor : Ctor) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Oconstructor ctor) |] **
    (* forall each argument, apply to [fs_spec] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) vals Q -* wp_ctor ctor vals Q.

  (** ** Weakest precondition of a destructor *)

  Fixpoint wpd_bases
           (cls : globname) (this : ptr)
           (bases : list globname)
           (Q : mpred) : mpred :=
    match bases with
    | nil => Q
    | base :: bases =>
      delete_val (Tnamed base) (this ., _base cls base) (wpd_bases cls this bases Q)
    end.

  Lemma wpd_bases_frame cls this : forall bases Q Q',
      Q -* Q' |-- wpd_bases cls this bases Q -* wpd_bases cls this bases Q'.
  Proof.
    induction bases => /=; eauto.
    intros. by iIntros "X"; iApply delete_val_frame; iApply IHbases.
  Qed.

  Fixpoint wpd_members
           (cls : globname) (this : ptr)
           (members : list Member)
           (Q : mpred) : mpred :=
    match members with
    | nil => Q
    | member :: members =>
      delete_val member.(mem_type) (this ., _field {| f_name := member.(mem_name) ; f_type := cls |})
           (wpd_members cls this members Q)
    end.

  Lemma wpd_members_frame cls this : forall members Q Q',
      Q -* Q' |-- wpd_members cls this members Q -* wpd_members cls this members Q'.
  Proof.
    induction members => /=; eauto.
    intros. by iIntros "X"; iApply delete_val_frame; iApply IHmembers.
  Qed.

  (** [wp_dtor dtor args Q] defines the semantics of the destructor [dtor] when
      applied to [args] with post-condition [Q].
   *)
  Definition wp_dtor (dtor : Dtor) (args : list val)
             (Q : val -> epred) : mpred :=
    match dtor.(d_body) with
    | None => False
    | Some Defaulted => UNSUPPORTED "defaulted destructors"
      (* ^ defaulted destructors are not supported *)
    | Some (UserDefined body) =>
      let epilog :=
          match resolve.(genv_tu).(globals) !! dtor.(d_class) with
          | Some (Gstruct s) => Some $ fun thisp : ptr =>
            thisp |-> struct_paddingR 1 dtor.(d_class) **
            wpd_members dtor.(d_class) thisp s.(s_fields)
               (* ^ fields are destroyed *)
               (thisp |-> revert_identity dtor.(d_class)
               (* ^ the identity of the object is destroyed *)
                  (wpd_bases dtor.(d_class) thisp (List.map fst s.(s_bases))
                  (* ^ the base classes are destroyed (reverse order) *)
                     (thisp |-> tblockR (Tnamed dtor.(d_class)) 1 -* |={⊤}=> |> Q Vvoid)))
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
                   (thisp |-> tblockR (Tnamed dtor.(d_class)) 1 -* |={⊤}=> |> Q Vvoid)
          | _ => None
          end%I
      in
      match epilog , args with
      | Some epilog , Vptr thisp :: nil =>
        let ρ := Remp (Some thisp) Tvoid in
          |> (* the function prolog consumes a step. *)
             wp ⊤ ρ body (void_return (epilog thisp))
      | _ , _ => False
      end
    end%bs%I.

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

  Definition dtor_ok (dtor : Dtor) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Odestructor dtor) |] **
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) vals Q -* wp_dtor dtor vals Q.

End with_cpp.
