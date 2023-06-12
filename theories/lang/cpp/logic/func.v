(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.proofmode.proofmode.	(** Early to get the right [ident] *)
Require Import bedrock.lang.bi.ChargeCompat.
Require Import bedrock.lang.bi.errors.
Require Import bedrock.lang.cpp.logic.entailsN.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.

From bedrock.lang.cpp.logic Require Import
  pred path_pred heap_pred wp builtins cptr const
  layout initializers destroy.

(* UPSTREAM. *)
Lemma wand_frame {PROP : bi} (R Q Q' : PROP) :
  Q -* Q' |--
  (R -* Q) -* (R -* Q').
Proof. iIntros "Q W R". iApply ("Q" with "(W R)"). Qed.

#[local] Set Printing Coercions.

Arguments ERROR {_ _} _%bs.
Arguments UNSUPPORTED {_ _} _%bs.
#[local] Arguments wpi : simpl never.

Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.
  Variable tu : translation_unit.

  Notation wp := (wp tu).
  Notation wpi := (wpi tu).
  Notation wp_init := (wp_init tu).
  #[local] Notation interp := (interp tu).

  #[local] Open Scope free_scope.

  #[local] Notation _base := (o_base resolve).
  #[local] Notation _derived := (o_derived resolve).

  Implicit Types p : ptr.

  Definition Kfree (free : FreeTemp) : KpredI -> KpredI :=
    Kat_exit (interp free).

  (** * Aggregate identity *)
  (* Part of [all_identities path cls], but indexed by fuel [f].
     TODO replace this with a version that is built by well-founded recursion.
   *)
  #[local]
  Fixpoint derivationsR' (f : nat) (include_base : bool) (cls : globname) (path : list globname) (q : cQp.t) : Rep :=
    match f with
    | 0 => False
    | S f =>
      match tu !! cls with
      | Some (Gstruct st) =>
        (if include_base && has_vtable st then derivationR cls path q else emp) **
        [∗list] b ∈ st.(s_bases),
           let '(base,_) := b in
           _base cls base |-> derivationsR' f true base (path ++ [base]) q
      | _ => False
      end
    end.

  (** [this |-> derivationsR include_base cls path q] is all of the object
      identities of the [this] object (of type [cls]) where the most derived
      class is reached from [cls] using [path]. For example, consider the
      following
      ```c++
      class A {};
      class B : public A {};
      class C : public B {};
      ```
      here, [derivationsR true "::B" ["::C"] q] produces:
      [[
      derivationR "::B" ["::C","::B"] q **
      _base "::B" "::A" |-> derivationR "::A" ["::C","::B","::A"] q
      ]]

      while [derivationsR true "::C" [] q] produces all the identities for A, B and C:
      [[
      derivationR "::C" ["::C"] q **
      _base "::C" "::B" |-> derivationR true "::B" ["::C"] q
      ]]
   *)
  Definition derivationsR : bool -> globname -> list globname -> cQp.t -> Rep :=
    let size := avl.IM.cardinal resolve.(genv_tu).(types) in
    (* ^ the number of global entries is an upper bound on the height of the
       derivation tree.
     *)
    derivationsR' size.

  (** [wp_init_identity cls Q] updates the identities of "this" by updating the
      [identity] of all base classes (transitively) and producing the new identity
      for "this".
   *)
  Definition wp_init_identity (cls : globname) (Q : mpred) : Rep :=
    derivationsR false cls [] (cQp.mut 1) **
    (derivationsR true cls [cls] (cQp.mut 1) -* pureR Q).

  Theorem wp_init_identity_frame cls Q Q' :
    pureR (Q' -* Q) |-- wp_init_identity cls Q' -* wp_init_identity cls Q.
  Proof.
    iIntros "X [$ Y] Z".
    rewrite pureR_wand.
    by iApply "X"; iApply "Y".
  Qed.

  (* variant of [wp_init_identity_frame] for [mpred]. *)
  Theorem wp_init_identity_frame' cls Q Q' p :
    Q' -* Q |-- (p |-> wp_init_identity cls Q') -* (p |-> wp_init_identity cls Q).
  Proof. by rewrite -_at_wand -wp_init_identity_frame _at_pureR. Qed.

  (** [wp_revert_identity cls Q] updates the identities of "this" by taking the
      [identity] of this class and transitively updating the [identity] of all base
      classes to remove [cls] as the most derived class.
   *)
  Definition wp_revert_identity (cls : globname) (Q : mpred) : Rep :=
    derivationsR true cls [cls] (cQp.mut 1) **
    (derivationsR false cls [] (cQp.mut 1) -* pureR Q).

  Theorem wp_revert_identity_frame cls Q Q' :
    pureR (Q' -* Q) |-- wp_revert_identity cls Q' -* wp_revert_identity cls Q.
  Proof.
    iIntros "X [$ Y] Z".
    rewrite pureR_wand.
    by iApply "X"; iApply "Y".
  Qed.

  (** sanity chect that initialization and revert are inverses *)
  Corollary wp_init_revert cls Q p :
    let REQ := derivationsR false cls [] (cQp.mut 1) in
        p |-> REQ ** Q
    |-- p |-> wp_init_identity cls (p |-> wp_revert_identity cls (p |-> REQ ** Q)).
  Proof.
    rewrite /wp_revert_identity/wp_init_identity.
    rewrite !_at_sep !_at_wand !_at_pureR.
    iIntros "[$ $] $ $".
  Qed.

  (** * Binding parameters *)

  Fixpoint wp_make_mutables (ls : list (ptr * type)) (Q : epred) : mpred :=
    match ls with
    | nil => Q
    | (p,t) :: ls => wp_make_mutables ls $ wp_make_mutable tu p t Q
    end.

  Lemma wp_make_mutables_frame ls : forall Q Q',
      Q -* Q' |-- wp_make_mutables ls Q -* wp_make_mutables ls Q'.
  Proof.
    induction ls =>/=; eauto.
    iIntros (??) "X"; case_match; iApply (IHls with "[X]").
    iApply wp_const_frame; first reflexivity; eauto.
  Qed.

  Definition Kcleanup (ls : list (ptr * type)) : Kpred -> Kpred :=
    Kat_exit (wp_make_mutables ls).

  Lemma Kcleanup_frame ls (Q Q' : Kpred) rt :
    Q rt -* Q' rt |-- Kcleanup ls Q rt -* Kcleanup ls Q' rt.
  Proof.
    iIntros "K". iApply Kat_exit_frame; eauto.
    iIntros (??) "X"; iApply wp_make_mutables_frame; eauto.
  Qed.

  (** [bind_vars args vals r Q] preforms initialization of the parameters
      given the values being passed.

      NOTE. We make arguments [const] here if necessary and then make them
            mutable again in the second argument to [Q].
   *)
  Fixpoint bind_vars (args : list (ident * type)) (ar : function_arity) (ptrs : list ptr)
    (ρ : option ptr -> region) (Q : region -> list (ptr * type) -> mpred) : mpred :=
    match args with
    | nil =>
        match ar with
        | Ar_Definite =>
            match ptrs with
            | nil => Q (ρ None) []
            | _ :: _ => ERROR "bind_vars: extra arguments"
            end
        | Ar_Variadic =>
            match ptrs with
            | vap :: nil => Q (ρ $ Some vap) []
            | _ => ERROR "bind_vars: variadic function missing varargs"
            end
        end
    | (x,ty) :: xs =>
        match ptrs with
        | p :: ps =>
            let '(cv, ty) := decompose_type ty in
            if q_const cv then
              wp_make_const tu p ty $ bind_vars xs ar ps (fun vap => Rbind x p $ ρ vap)
                (fun ρ consts => Q ρ $ (p,ty) :: consts)
            else
              bind_vars xs ar ps (fun vap => Rbind x p $ ρ vap) Q
        | nil => ERROR "bind_vars: insufficient arguments"
        end
    end.


  Lemma bind_vars_frame : forall ts ar args ρ Q Q',
        Forall ρ free, Q ρ free -* Q' ρ free
    |-- bind_vars ts ar args ρ Q -* bind_vars ts ar args ρ Q'.
  Proof.
    induction ts; destruct args => /= *; eauto.
    { case_match; eauto.
      iIntros "A B"; iApply "A"; eauto. }
    { case_match; eauto. case_match; eauto.
      iIntros "A"; iApply "A". }
    { iIntros "A".
      repeat case_match; subst.
      { iApply wp_const_frame; first reflexivity.
        iApply IHts. iIntros (??). iApply "A". }
      { iApply IHts; iApply "A". } }
  Qed.

  (** * Weakest preconditions of the flavors of C++ "functions"  *)

  (** ** the weakest precondition of a function *)
  Definition wp_func (f : Func) (args : list ptr) (Q : ptr -> epred) : mpred :=
    match f.(f_body) with
    | None => False
    | Some body =>
      match body with
      | Impl body =>
        let ρ va := Remp None va f.(f_return) in
        bind_vars f.(f_params) f.(f_arity) args ρ (fun ρ cleanup =>
        |> wp ρ body (Kcleanup cleanup $ Kreturn (funI x => |={⊤}=> |> Q x)))
      | Builtin builtin =>
        wp_builtin_func builtin (Tfunction (cc:=f.(f_cc)) f.(f_return) (List.map snd f.(f_params))) args Q
      end
    end.

  Definition func_ok (f : Func) (spec : function_spec)
    : mpred :=
      [| type_of_spec spec = type_of_value (Ofunction f) |] **
      (* forall each argument, apply to [fs_spec] *)
      □ Forall Q : ptr -> mpred, Forall vals,
        spec.(fs_spec) vals Q -* wp_func f vals Q.

  (** ** The weakest precondition of a method

      Note that in the calling convention for methods, the [this] parameter
      is passed directly rather than being materialized like normal parameters.
   *)
  Definition wp_method (m : Method) (args : list ptr)
             (Q : ptr -> epred) : mpred :=
    match m.(m_body) with
    | None => False
    | Some (UserDefined body) =>
      match args with
      | thisp :: rest_vals =>
        let ρ va := Remp (Some thisp) va m.(m_return) in
        bind_vars m.(m_params) m.(m_arity) rest_vals ρ (fun ρ cleanup =>
        |> wp ρ body (Kcleanup cleanup (Kreturn (funI x => |={⊤}=> |>Q x))))
      | _ => False
      end
    | Some _ => UNSUPPORTED "defaulted methods"%bs
    end.

  Definition method_ok (m : Method) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Omethod m) |] **
    (* forall each argument, apply to [fs_spec] *)
    □ Forall Q : ptr -> mpred, Forall vals,
      spec.(fs_spec) vals Q -* wp_method m vals Q.

  (** ** Weakest precondition of a constructor *)

  (* mark members as strictly valid. *)
  Fixpoint wpi_members_svalid
           (cls : globname) (this : ptr)
           (members : list Member)
           (Q : mpred) : mpred :=
    match members with
    | nil => Q
    | m :: members =>
        this ,, _field {| f_type := cls ; f_name := m.(mem_name) |} |->
          (svalidR ** aligned_ofR (erase_qualifiers m.(mem_type)))
          (* Alignment should be deducible otherwise. *)
        -* wpi_members_svalid cls this members Q
    end.

  Lemma wpi_members_svalid_frame p cls (Q Q' : mpredI) flds :
      Q -* Q'
      |-- wpi_members_svalid cls p flds Q -* wpi_members_svalid cls p flds Q'.
  Proof.
    induction flds => /=; first done.
    iIntros "Q W S".
    iApply (IHflds with "Q (W S)").
  Qed.

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
        default_initialize tu m.(mem_type)
          (this ,, _field {| f_type := cls ; f_name := m.(mem_name) |})
          (fun frees => interp frees (wpi_members ρ cls this members inits Q))
      | i :: is' =>
        match i.(init_path) with
        | InitField _ (* = m.(mem_name) *) =>
          match is' with
          | nil =>
            (* there is a *unique* initializer for this field *)
            wpi ρ cls this i (wpi_members ρ cls this members inits Q)
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
        wpi ρ cls this i (wpi_bases ρ cls this bases inits Q)
      | _ :: _ :: _ =>
        (* there are multiple initializers for this, so we fail *)
        ERROR $ "multiple initializers for base: " ++ cls ++ "::" ++ b
      end
    end%I%bs.

  Lemma wpi_bases_frame:
    ∀ ρ p (ty : globname) bases (inits : list Initializer) (Q Q' : mpredI),
      Q -* Q'
      |-- wpi_bases ρ ty p bases inits Q -* wpi_bases ρ ty p bases inits Q'.
  Proof.
    induction bases => /=; eauto.
    intros.
    case_match; eauto.
    case_match; eauto.
    iIntros "a".
    iApply wpi_frame => //.
    by iApply IHbases.
  Qed.

  Lemma wpi_members_frame:
    ∀ (ρ : region) flds p (ty : globname) (li : list Initializer) (Q Q' : mpredI),
      Q -* Q'
      |-- wpi_members ρ ty p flds li Q -* wpi_members ρ ty p flds li Q'.
  Proof.
    induction flds => /=; eauto; intros.
    case_match.
    { iIntros "a"; iApply default_initialize_frame; [done|].
      iIntros (?); iApply interp_frame. by iApply IHflds. }
    { case_match; eauto.
      case_match; eauto.
      iIntros "a".
      iApply wpi_frame => //.
      by iApply IHflds. }
  Qed.

  Definition wp_struct_initializer_list (s : Struct) (ρ : region) (cls : globname) (this : ptr)
             (inits : list Initializer) (Q : mpred) : mpred :=
    match List.find (fun i => bool_decide (i.(init_path) = InitThis)) inits with
    | Some {| init_type := ty ; init_init := e |} =>
      match inits with
      | _ :: nil =>
        if bool_decide (drop_qualifiers ty = Tnamed cls) then
          (* this is a delegating constructor, simply delegate. *)
          wp_init ρ (Tnamed cls) this e (fun frees => interp frees Q)
        else
          (* the type names do not match, this should never happen *)
          ERROR "type name mismatch"
      | _ =>
        (* delegating constructors are not allowed to have any other initializers
         *)
        ERROR "delegating constructor has other initializers"
      end
    | None =>
      let members_valid := wpi_members_svalid cls this s.(s_fields) in
      let bases := wpi_bases ρ cls this (List.map fst s.(s_bases)) inits in
      let members := wpi_members ρ cls this s.(s_fields) inits in
      let ident Q := this |-> wp_init_identity cls Q in
      (** validity, initialize the bases, then the identity, then the members *)
      this |-> svalidR -*
      members_valid (bases (ident (members (this |-> struct_paddingR (cQp.mut 1) cls -* Q))))
      (* NOTE we get the [struct_paddingR] at the end since
         [struct_paddingR (cQp.mut 1) cls |-- type_ptrR (Tnamed cls)].
       *)
    end.

  Lemma wp_struct_initializer_list_frame : forall ρ cls p ty li Q Q',
      Q -* Q' |-- wp_struct_initializer_list cls ρ ty p li Q -* wp_struct_initializer_list cls ρ ty p li Q'.
  Proof.
    rewrite /wp_struct_initializer_list/=. intros. case_match.
    { case_match => //.
      destruct l; eauto.
      case_match; eauto.
      iIntros "x".
      iApply wp_init_frame => //.
      iIntros (?); by iApply interp_frame. }
    { iIntros "Q".
      iApply wand_frame.
      iApply wpi_members_svalid_frame.
      iApply wpi_bases_frame.
      iApply wp_init_identity_frame'.
      iApply wpi_members_frame.
      by iApply wand_frame. }
  Qed.

  Definition wp_union_initializer_list (u : translation_unit.Union) (ρ : region) (cls : globname) (this : ptr)
             (inits : list Initializer) (Q : option nat -> epred) : mpred :=
    match inits with
    | [] => Q None
    | [{| init_path := InitField f ; init_type := te ; init_init := e |} as init] =>
        match list_find (fun m => f = m.(mem_name)) u.(u_fields) with
        | None => ERROR "field not found in union initialization"
        | Some (n, m) => wpi ρ cls this init $ Q (Some n)
        end
    | _ =>
      UNSUPPORTED "indirect (or self) union initialization is not currently supported"
    end.

  Lemma wp_union_initializer_list_frame : forall ρ cls p ty li (Q Q' : option nat -> epred),
        (Forall n, Q n -* Q' n)
    |-- wp_union_initializer_list cls ρ ty p li Q -*
        wp_union_initializer_list cls ρ ty p li Q'.
  Proof.
    rewrite /wp_union_initializer_list/=. intros. case_match; eauto.
    { iIntros "K"; iApply "K". }
    { iIntros "K".
      repeat case_match; eauto.
      iApply wpi_frame; [done|].
      iApply "K". }
  Qed.

  (* [type_validity ty p] is the pointer validity of a class that is learned
     at the beginning of the constructor.

     Generally, it is the **strict** validity of all of the sub-objects.
     [[
         type_validity (Tnamed cls) this
     |-- strict_valid_ptr this **
         [∗list] f ∈ s_fields , type_validity f.(f_type) (this ,, _field f)
     ]]

     TODO we leave this trivial for now.
   *)
  Definition type_valdity : type -> ptr -> mpred := fun _ _ => emp.

  (** A special version of return to match the C++ rule that
     constructors and destructors must not syntactically return a value, e.g.
     `return f()` for `void f()` are not allowed.

     NOTE: we could drop this in favor of relying on the compiler to
           check this.
   *)
  Definition Kreturn_void (P : mpred) : KpredI :=
    KP (funI rt =>
          match rt with
          | Normal | ReturnVoid => P
          | _ => False
          end).

  (**
     [wp_ctor ctor args Q] is the weakest pre-condition (with post-condition [Q])
     running the constructor [ctor] with arguments [args].

     Note that the constructor semantics consumes the entire [blockR] of the object
     that is being constructed and the C++ abstract machine breaks this block down
     producing usable† memory.
     **Alternative**: Because constructor calls are *always* syntactically distinguished
     (since C++ does not allow taking a pointer to a constructor), we know that any
     invocation of a constructor will be from a [wp_init] which means that the C++
     abstract machine will already own the memory (see the documentation for [wp_init]
     in [wp.v]). In order to enforce this semantically within the abstract machine,
     we would need a new predicate to say "a constructor with the given specification"
     (rather than simply desugaring this to "a function with the given specification").

     NOTE: supporting virtual inheritence will require us to add
     constructor kinds here

     † It is not necessarily initialized, e.g. because primitive fields are not
       initialized (you get an [uninitR]), but you will get something that implies
       [type_ptr].
   *)
  Definition wp_ctor (ctor : Ctor) (args : list ptr) (Q : ptr -> epred) : mpred :=
    match ctor.(c_body) with
    | None => False
    | Some Defaulted => UNSUPPORTED "defaulted constructors"
      (* ^ defaulted constructors are not supported yet *)
    | Some (UserDefined (inits, body)) =>
      match args with
      | thisp :: rest_vals =>
        let ty := Tnamed ctor.(c_class) in
        match tu !! ctor.(c_class) with
        | Some (Gstruct cls) =>
          (* this is a structure *)
          thisp |-> tblockR ty (cQp.mut 1) **
          (* ^ this requires that you give up the *entire* block of memory that the object
             will use.
           *)
          |> let ρ va := Remp (Some thisp) va Tvoid in
             bind_vars ctor.(c_params) ctor.(c_arity) rest_vals ρ (fun ρ cleanup =>
               (wp_struct_initializer_list cls ρ ctor.(c_class) thisp inits
                  (wp ρ body (Kcleanup cleanup (Kreturn_void (|={⊤}=> |> Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p))))))
        | Some (Gunion union) =>
        (* this is a union *)
          thisp |-> tblockR ty (cQp.mut 1) **
          (* ^ this requires that you give up the *entire* block of memory that the object
             will use.
           *)
          |> let ρ va := Remp (Some thisp) va Tvoid in
             bind_vars ctor.(c_params) ctor.(c_arity) rest_vals ρ (fun ρ cleanup =>
               (wp_union_initializer_list union ρ ctor.(c_class) thisp inits
                  (fun which => thisp |-> union_paddingR (cQp.mut 1) ctor.(c_class) which -*
                             wp ρ body (Kcleanup cleanup (Kreturn_void (|={⊤}=> |> Forall p, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p))))))
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
    □ Forall Q : ptr -> mpred, Forall vals,
      spec.(fs_spec) vals Q -* wp_ctor ctor vals Q.

  (** ** Weakest precondition of a destructor *)
  Definition wpd_bases (cls : globname) (this : ptr) (bases : list globname) : epred -> mpred :=
    let del_base base := FreeTemps.delete (Tnamed base) (this ,, _base cls base) in
    interp (FreeTemps.seqs_rev (List.map del_base bases)).

  Lemma wpd_bases_frame cls this : forall bases Q Q',
      Q -* Q' |-- wpd_bases cls this bases Q -* wpd_bases cls this bases Q'.
  Proof. intros. apply interp_frame. Qed.

  Definition wpd_members (cls : globname) (this : ptr) (members : list Member) : epred -> mpred :=
    let del_member m := FreeTemps.delete m.(mem_type) (this ,, _field {| f_name := m.(mem_name) ; f_type := cls |}) in
    interp (FreeTemps.seqs_rev (List.map del_member members)).

  Lemma wpd_members_frame cls this : forall members Q Q',
      Q -* Q' |-- wpd_members cls this members Q -* wpd_members cls this members Q'.
  Proof. intros; apply interp_frame. Qed.

  (** [wp_dtor dtor args Q] defines the semantics of the destructor [dtor] when
      applied to [args] with post-condition [Q].

      Note that destructors are not always syntactically distinguished from
      function calls (e.g. in the case of [c.~C()]). Therefore, in order to
      have a uniform specification, they need to return the underlying memory
      (i.e. a [this |-> tblockR (Tnamed cls) 1]) to the caller.
      When the program is destroying this object, e.g. due to stack allocation,
      this resource will be consumed immediately.
   *)
  Definition wp_dtor (dtor : Dtor) (args : list ptr)
             (Q : ptr -> epred) : mpred :=
    match dtor.(d_body) with
    | None => False
    | Some body =>
      let epilog :=
          match tu !! dtor.(d_class) with
          | Some (Gstruct s) => Some $ fun (thisp : ptr) =>
            thisp |-> struct_paddingR (cQp.mut 1) dtor.(d_class) **
            wpd_members dtor.(d_class) thisp s.(s_fields)
               (* ^ fields are destroyed *)
               (thisp |-> wp_revert_identity dtor.(d_class)
               (* ^ the identity of the object is destroyed *)
                  (wpd_bases dtor.(d_class) thisp (List.map fst s.(s_bases))
                  (* ^ the base classes are destroyed (reverse order) *)
                     (thisp |-> tblockR (Tnamed dtor.(d_class)) (cQp.mut 1) -* |={⊤}=> |> Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p)))
                     (* ^ the operations above destroy each object returning its memory to
                        the abstract machine. Then the abstract machine gives this memory
                        back to the program.
                        NOTE the [|>] here is for the function epilog.
                      *)
          | Some (Gunion u) => Some $ fun (thisp : ptr) =>
            (* the function epilog of a union destructor doesn't actually destroy anything
               because it isn't clear what to destroy (this is dictated by the C++ standard).
               Instead, the epilog provides a fancy update to destroy things.

               In practice, this means that programs can only destroy unions
               automatically where they can prove the active entry has a trivial destructor
               or is already destroyed.
             *)
            |={⊤}=> thisp |-> tblockR (Tnamed dtor.(d_class)) (cQp.mut 1) **
                   (thisp |-> tblockR (Tnamed dtor.(d_class)) (cQp.mut 1) -* |={⊤}=> |> Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p)
          | _ => None
          end%I
      in
      match epilog , args with
      | Some epilog , thisp :: nil =>
        let ρ := Remp (Some thisp) None Tvoid in
          |> (* the function prolog consumes a step. *)
             match body return Kpred -> mpred with
             | Defaulted => fun k => k Normal
             | UserDefined body => wp ρ body
             end (Kreturn_void (epilog thisp))
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
    □ Forall Q : ptr -> mpred, Forall vals,
      spec.(fs_spec) vals Q -* wp_dtor dtor vals Q.

End with_cpp.
(* conveniences for the common pattern *)
Notation init_derivationR cls path q := (derivationR cls%bs (path%bs ++ [cls%bs]) q).
Notation init_derivationsR cls path q := (derivationsR cls%bs (path%bs ++ [cls%bs]) q).
