(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.bi.ChargeCompat.
Require Import bedrock.lang.bi.errors.
Require Import bedrock.lang.bi.telescopes.
Require Import bedrock.lang.cpp.logic.entailsN.
Require Import iris.proofmode.tactics.	(** Early to get the right [ident] *)
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
  spec pred path_pred heap_pred wp builtins
  layout initializers destroy.
Require Import bedrock.lang.cpp.heap_notations.

#[local] Set Universe Polymorphism.
#[local] Set Printing Universes.
#[local] Set Printing Coercions.

Arguments ERROR {_ _} _%bs.
Arguments UNSUPPORTED {_ _} _%bs.

(** * Wrappers to build [function_spec] from a [WithPrePost] *)

(* A specification for a function (with explicit thread info) *)
Definition TSFunction@{X Z Y} `{Σ : cpp_logic} {cc : calling_conv}
    (ret : type) (targs : list type) (PQ : thread_info -> WithPrePost@{X Z Y} mpredI)
    : function_spec :=
  {| fs_cc        := cc
   ; fs_return    := ret
   ; fs_arguments := targs
   ; fs_spec ti   := WppD (PQ ti) |}.

(* A specification for a function  *)
Definition SFunction@{X Z Y} `{Σ : cpp_logic} {cc : calling_conv}
    (ret : type) (targs : list type) (PQ : WithPrePost@{X Z Y} mpredI)
    : function_spec :=
  {| fs_cc        := cc
   ; fs_return    := ret
   ; fs_arguments := targs
   ; fs_spec _    := WppD PQ |}.

(* A specification for a constructor *)
Definition SConstructor@{X Z Y} `{Σ : cpp_logic, resolve : genv} {cc : calling_conv}
    (class : globname) (targs : list type) (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
    : function_spec :=
  let this_type := Qmut (Tnamed class) in
  let map_pre this '(args, P) :=
    (Vptr this :: args,
     this |-> tblockR (Tnamed class) 1 ** P)
  in
  SFunction (cc:=cc) (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
    {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
     ; wpp_pre this := tele_map (map_pre this) (PQ this).(wpp_pre)
     ; wpp_post this := (PQ this).(wpp_post)
     |}.

(* A specification for a destructor *)
Definition SDestructor@{X Z Y} `{Σ : cpp_logic, resolve : genv} {cc : calling_conv}
    (class : globname) (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
    : function_spec :=
  let this_type := Qmut (Tnamed class) in
  let map_pre this '(args, P) := (Vptr this :: args, P) in
  let map_post (this : ptr) '{| we_ex := pwiths ; we_post := Q|} :=
    {| we_ex := pwiths
     ; we_post := tele_map (fun '(result, Q) =>
      (result, this |-> tblockR (Tnamed class) 1 ** Q)) Q
     |}
  in
  (** ^ NOTE the size of an object might be different in the presence
      of virtual base classes. *)
  SFunction@{X Z Y} (cc:=cc) (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
    {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
     ; wpp_pre this := tele_map (map_pre this) (PQ this).(wpp_pre)
     ; wpp_post this := tele_map (map_post this) (PQ this).(wpp_post)
    |}.

(* A specification for a method *)
#[local] Definition SMethod_wpp@{X Z Y} `{Σ : cpp_logic}
    (wpp : ptr -> WithPrePost@{X Z Y} mpredI) : WithPrePost@{X Z Y} mpredI :=
  let map_pre this pair := (this :: pair.1, pair.2) in
  {| wpp_with := TeleS (fun this : ptr => (wpp this).(wpp_with))
   ; wpp_pre this := tele_map (map_pre (Vptr this)) (wpp this).(wpp_pre)
   ; wpp_post this := (wpp this).(wpp_post)
   |}.
Definition SMethod@{X Z Y} `{Σ : cpp_logic} {cc : calling_conv}
    (class : globname) (qual : type_qualifiers) (ret : type) (targs : list type)
    (PQ : ptr -> WithPrePost@{X Z Y} mpredI) : function_spec :=
  let class_type := Tnamed class in
  let this_type := Tqualified qual class_type in
  SFunction@{X Z Y} (cc:=cc) ret (Qconst (Tpointer this_type) :: targs)
    (SMethod_wpp PQ).

Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

  #[local] Notation _base := (o_base resolve).
  #[local] Notation _derived := (o_derived resolve).

  (** The following monotonicity lemmas are (i) stated so that they
      don't force a pair of related WPPs to share universes and (ii)
      proved so that they don't constrain the WPP universes [Y1], [Y2]
      from above. The TC instances are strictly less useful, as they
      necessarily give up on both (i) and (ii). *)
  Section TSFunction.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} (ret : type) (targs : list type).

    Lemma TSFunction_mono@{X1 X2 Z1 Z2 Y1 Y2} wpp1 wpp2 :
      (∀ ti, wpp_entails (wpp1 ti) (wpp2 ti)) ->
      fs_entails
        (TSFunction@{X1 Z1 Y1} (cc:=cc) ret targs wpp2)
        (TSFunction@{X2 Z2 Y2} (cc:=cc) ret targs wpp1).
    Proof.
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (ti vs K) "wpp". by iApply Hwpp.
    Qed.

    #[global] Instance: Params (@TSFunction) 5 := {}.
    #[global] Instance TSFunction_ne n :
      Proper (dist (A:=thread_info -d> WithPrePostO mpredI) n ==> dist n)
        (TSFunction (cc:=cc) ret targs).
    Proof.
      intros wpp1 wpp2 Hwpp. split. by rewrite/type_of_spec/=. done.
    Qed.

    #[global] Instance TSFunction_proper :
      Proper (equiv (A:=thread_info -d> WithPrePostO mpredI) ==> equiv)
        (TSFunction (cc:=cc) ret targs).
    Proof. exact: ne_proper. Qed.

    #[global] Instance TSFunction_mono'@{X Z Y} :
      Proper (pointwise_relation _ (flip wpp_entails) ==> fs_entails)
        (TSFunction@{X Z Y} (cc:=cc) ret targs).
    Proof. repeat intro. by apply TSFunction_mono. Qed.

    #[global] Instance TSFunction_flip_mono'@{X Z Y} :
      Proper (pointwise_relation _ (wpp_entails) ==> flip fs_entails)
        (TSFunction@{X Z Y} (cc:=cc) ret targs).
    Proof. solve_proper. Qed.

  End TSFunction.

  Section SFunction.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} (ret : type) (targs : list type).

    Lemma SFunction_mono@{X1 X2 Z1 Z2 Y1 Y2} wpp1 wpp2 :
      wpp_entails wpp2 wpp1 ->
      fs_entails
        (SFunction@{X1 Z1 Y1} (cc:=cc) ret targs wpp1)
        (SFunction@{X2 Z2 Y2} (cc:=cc) ret targs wpp2).
    Proof.
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (_ vs K) "wpp". by iApply Hwpp.
    Qed.

    #[global] Instance: Params (@SFunction) 5 := {}.
    #[global] Instance SFunction_ne : NonExpansive (SFunction (cc:=cc) ret targs).
    Proof.
      intros n wpp1 wpp2 Hwpp. split. by rewrite/type_of_spec/=. by move=>ti.
    Qed.

    #[global] Instance SFunction_proper :
      Proper (equiv ==> equiv) (SFunction (cc:=cc) ret targs).
    Proof. exact: ne_proper. Qed.

    #[global] Instance SFunction_mono'@{X Z Y} :
      Proper (flip wpp_entails ==> fs_entails) (SFunction@{X Z Y} (cc:=cc) ret targs).
    Proof. repeat intro. by apply SFunction_mono. Qed.

    #[global] Instance SFunction_flip_mono'@{X Z Y} :
      Proper (wpp_entails ==> flip fs_entails)
        (SFunction@{X Z Y} (cc:=cc) ret targs).
    Proof. solve_proper. Qed.
  End SFunction.

  Section SMethod.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} (class : globname) (qual : type_qualifiers).
    Context (ret : type) (targs : list type).

    (** We could derive [SMethod_mono] from the following
        [SMethod_wpp_monoN]. We retain this proof because it's easier
        to understand and it goes through without [BiEntailsN]. *)
    Lemma SMethod_mono@{X1 X2 Z1 Z2 Y1 Y2} wpp1 wpp2 :
      (∀ this, wpp_entails (wpp2 this) (wpp1 this)) ->
      fs_entails
        (SMethod@{X1 Z1 Y1} (cc:=cc) class qual ret targs wpp1)
        (SMethod@{X2 Z2 Y2} (cc:=cc) class qual ret targs wpp2).
    Proof.
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (_ vs K) "wpp".
      (** To apply [Hwpp], we have to deconstruct the WPP we've got,
          stripping off the extra "this" argument. *)
      iDestruct "wpp" as (this) "wpp". rewrite {1}tbi_exist_exist.
      iDestruct "wpp" as (xs) "wpp". rewrite tele_app_bind tele_map_app.
      destruct (tele_app _ xs) as [args P] eqn:Hargs. simpl.
      iDestruct "wpp" as "(-> & pre & post)".
      iDestruct (Hwpp this args K with "[pre post]") as "wpp".
      { rewrite /WppD/WppGD. rewrite tbi_exist_exist.
        iExists xs. rewrite tele_app_bind Hargs/=. by iFrame "pre post". }
      iExists this. rewrite tbi_exist_exist. rewrite/WppD/WppGD tbi_exist_exist.
      iDestruct "wpp" as (ys) "wpp". rewrite tele_app_bind.
      iDestruct "wpp" as "(-> & pre & post)".
      iExists ys. rewrite tele_app_bind tele_map_app. simpl. by iFrame "pre post".
    Qed.

    #[local] Lemma SMethod_wpp_monoN@{X1 X2 Z1 Z2 Y1 Y2} wpp1 wpp2 vs K n :
      (∀ this, wpp_entailsN n (wpp1 this) (wpp2 this)) ->
      WppD@{X1 Z1 Y1} (SMethod_wpp wpp1) vs K ⊢{n}
      WppD@{X2 Z2 Y2} (SMethod_wpp wpp2) vs K.
    Proof.
      move=>Hwpp /=. f_equiv=>this.
      rewrite !tbi_exist_exist. set M1 := tele_app _. set M2 := tele_app _.
      apply exist_elimN=>x1. rewrite /M1 {M1} tele_app_bind tele_map_app.
      destruct (tele_app _ x1) as [vs1 P1] eqn:Hvs1; simpl.
      apply wand_elimN_l', only_provable_elimN'; intros ->;
        apply wand_introN_r; rewrite left_id.
      move: {Hwpp} (Hwpp this vs1 K). rewrite/WppD/WppGD.
      rewrite !tbi_exist_exist. set F1 := tele_app _. set F2 := tele_app _.
      move=>HF. trans (Exists x, F1 x).
      { apply (exist_introN' _ _ x1). rewrite/F1 tele_app_bind Hvs1 /=.
        rewrite -{1}[P1](left_id emp%I bi_sep) -assoc. f_equiv.
        exact: only_provable_introN. }
      rewrite {F1}HF. f_equiv=>x2. rewrite /F2 {F2} tele_app_bind.
      rewrite /M2 {M2} tele_app_bind tele_map_app. simpl. f_equiv.
      apply only_provable_elimN'=>->. exact: only_provable_introN.
    Qed.

    Lemma SMethod_ne@{X Y Z} wpp1 wpp2 n :
      (∀ this, wpp_dist n (wpp1 this) (wpp2 this)) ->
      SMethod@{X Y Z} (cc:=cc) class qual ret targs wpp1 ≡{n}≡
      SMethod@{X Y Z} (cc:=cc) class qual ret targs wpp2.
    Proof.
      setoid_rewrite wpp_dist_entailsN=>Hwpp.
      rewrite/SMethod. f_equiv=>vs K /=. apply dist_entailsN.
      split; apply SMethod_wpp_monoN=>this; by destruct (Hwpp this).
    Qed.

    Lemma SMethod_proper@{X1 X2 Z1 Z2 Y1 Y2} wpp1 wpp2 :
      (∀ this, wpp_equiv (wpp1 this) (wpp2 this)) ->
      SMethod@{X1 Z1 Y1} (cc:=cc) class qual ret targs wpp1 ≡
      SMethod@{X2 Z2 Y2} (cc:=cc) class qual ret targs wpp2.
    Proof.
      setoid_rewrite wpp_equiv_spec=>Hwpp. apply function_spec_equiv_split.
      split; apply SMethod_mono=>this; by destruct (Hwpp this).
    Qed.

    #[global] Instance: Params (@SMethod) 7 := {}.
    #[global] Instance SMethod_ne' n :
      Proper (dist (A:=ptr -d> WithPrePostO mpredI) n ==> dist n)
        (SMethod (cc:=cc) class qual ret targs).
    Proof. repeat intro. by apply SMethod_ne. Qed.

    #[global] Instance SMethod_proper' :
      Proper (equiv (A:=ptr -d> WithPrePostO mpredI) ==> equiv)
        (SMethod (cc:=cc) class qual ret targs).
    Proof. exact: ne_proper. Qed.

    #[global] Instance SMethod_mono'@{X Z Y} :
      Proper (pointwise_relation _ (flip wpp_entails) ==> fs_entails)
        (SMethod@{X Z Y} (cc:=cc) class qual ret targs).
    Proof. repeat intro. by apply SMethod_mono. Qed.

    #[global] Instance SMethod_flip_mono'@{X Z Y} :
      Proper (pointwise_relation _ wpp_entails ==> flip fs_entails)
        (SMethod@{X Z Y} (cc:=cc) class qual ret targs).
    Proof. repeat intro. by apply SMethod_mono. Qed.
  End SMethod.

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
             wp ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid)))
           else
             wp ⊤ ti ρ body (Kfree frees (val_return (fun x => |> Q x))))
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

  (** ** The weakest precondition of a method *)
  Definition wp_method (m : Method) ti (args : list val)
             (Q : val -> epred) : mpred :=
    match m.(m_body) with
    | None => False
    | Some body =>
      match args with
      | Vptr thisp :: rest_vals =>
        let ρ := Remp (Some thisp) m.(m_return) in
        bind_vars m.(m_params) rest_vals ρ (fun ρ frees =>
        |> if is_void m.(m_return) then
             wp ⊤ ti ρ body (Kfree frees (void_return (|>Q Vvoid)))
           else
             wp ⊤ ti ρ body (Kfree frees (val_return (fun x => |>Q x))))
      | _ => False
      end
    end.

  Definition method_ok (m : Method) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec = type_of_value (Omethod m) |] **
    (* forall each argument, apply to [fs_spec ti] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_method m ti vals Q.

  (** ** Weakest precondition of a constructor *)

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
        default_initialize m.(mem_type) (this ., _field {| f_type := cls ; f_name := m.(mem_name) |})
          (fun free => free ** wpi_members ti ρ cls this members inits Q)
      | i :: is' =>
        match i.(init_path) with
        | InitField _ (* = m.(mem_name) *) =>
          match is' with
          | nil =>
            (* there is a *unique* initializer for this field *)
            this ., offset_for cls i.(init_path) |-> tblockR (erase_qualifiers i.(init_type)) 1 -*
            wpi ⊤ ti ρ cls this i (fun f => f ** wpi_members ti ρ cls this members inits Q)
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
        wpi ⊤ ti ρ cls this i (fun f => f ** wpi_bases ti ρ cls this bases inits Q)
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
    { iIntros "a"; iApply default_initialize_frame; iIntros (?) "[$ x]".
      iRevert "x"; by iApply IHflds. }
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
      bases (ident (members (this |-> struct_padding 1 cls -*  Q)))
      (* NOTE we get the [struct_padding] at the end since
         [struct_padding 1 cls |-- type_ptrR (Tnamed cls)].
       *)
    end.

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
    end.

  Lemma wp_union_initializer_list_frame : forall ti ρ cls p ty li Q Q',
        Q -* Q'
    |-- wp_union_initializer_list cls ti ρ ty p li Q -*
        wp_union_initializer_list cls ti ρ ty p li Q'.
  Proof.
    rewrite /wp_union_initializer_list/=. intros. case_match; eauto.
    { case_match => //.
      destruct l; eauto.
      case_bool_decide; eauto.
      iIntros "X Y Z".
      iDestruct ("Y" with "Z") as "Y"; iRevert "Y".
      iApply wp_init_frame. reflexivity. iIntros (?) "[$ ?]"; iApply "X"; eauto. }
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
                  (wp ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid))))))
        | Some (Gunion union) =>
        (* this is a union *)
          thisp |-> tblockR ty 1 **
          (* ^ this requires that you give up the *entire* block of memory that the object
             will use.
           *)
          |> let ρ := Remp (Some thisp) Tvoid in
             bind_vars ctor.(c_params) rest_vals ρ (fun ρ frees =>
               (wp_union_initializer_list union ti ρ ctor.(c_class) thisp inits
                  (wp ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid))))))
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

  (** ** Weakest precondition of a destructor *)

  Fixpoint wpd_bases
           (ti : thread_info) (cls : globname) (this : ptr)
           (bases : list globname)
           (Q : mpred) : mpred :=
    match bases with
    | nil => Q
    | base :: bases =>
      destruct_val ti false (Tnamed base) (this ., _base cls base) (wpd_bases ti cls this bases Q)
    end.

  Fixpoint wpd_members
           (ti : thread_info) (cls : globname) (this : ptr)
           (members : list Member)
           (Q : mpred) : mpred :=
    match members with
    | nil => Q
    | member :: members =>
      destruct_val ti false member.(mem_type) (this ., _field {| f_name := member.(mem_name) ; f_type := cls |})
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
             wp ⊤ ti ρ body
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
