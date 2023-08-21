(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import elpi.apps.locker.
Require Import iris.proofmode.proofmode.	(** Early to get the right [ident] *)
Require Import bedrock.lang.bi.ChargeCompat.
Require Import bedrock.lang.bi.errors.
Require Import bedrock.lang.cpp.logic.entailsN.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.

From bedrock.lang.cpp.logic Require Import
  pred path_pred heap_pred wp builtins cptr const
  initializers translation_unit destroy.

(* UPSTREAM. *)
Lemma wand_frame {PROP : bi} (R Q Q' : PROP) :
  Q -* Q' |--
  (R -* Q) -* (R -* Q').
Proof. iIntros "Q W R". iApply ("Q" with "(W R)"). Qed.

#[local] Set Printing Coercions.

#[local] Arguments ERROR {_ _} _%bs.
#[local] Arguments UNSUPPORTED {_ _} _%bs.
#[local] Arguments wpi : simpl never.

(** ** Weakest precondition of a constructor: Initial construction step. *)
(**
Makes [this] and immediate [members] of [cls] strictly valid, to
implement the part of http://eel.is/c++draft/class.cdtor#3 about
members. This enables their dereference via [wp_lval_deref].
*)
mlock Definition svalid_members `{Σ : cpp_logic, σ : genv}
    (cls : globname) (members : list (bs * type)) : Rep :=
  reference_toR (Tnamed cls) **
  [** list] m ∈ members,
  _field {| f_type := cls ; f_name := m.1 |} |-> reference_toR m.2.
#[global] Arguments svalid_members {_ _ _} _ _ : assert.

Section svalid_members.
  Context `{Σ : cpp_logic, σ : genv}.

  #[global] Instance svalid_members_persistent : Persistent2 svalid_members.
  Proof. rewrite svalid_members.unlock. apply _. Qed.

  #[global] Instance svalid_members_affine : Affine2 svalid_members := _.
End svalid_members.

(** ** Aggregate identity *)
(**
Part of [all_identities path cls], but indexed by fuel [f].

TODO: Replace this with a version that is built by well-founded
recursion.
*)
#[local]
Definition derivationsR' `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (q : cQp.t) :=
  fix derivationsR' (f : nat) (include_base : bool) (cls : globname) (path : list globname) : Rep :=
  match f with
  | 0 => ERROR "derivationsR: no fuel"
  | S f =>
    match tu !! cls with
    | Some (Gstruct st) =>
      (if include_base && has_vtable st then derivationR cls path q else emp) **
      [** list] b ∈ st.(s_bases),
      let base := b.1 in
      _base cls base |-> derivationsR' f true base (path ++ [base])
    | _ => ERROR "derivationsR: not a structure"
    end
  end%I.

(**
[this |-> derivationsR include_base cls path q] is all of the object
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
Definition derivationsR `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (include_base : bool) (cls : globname) (path : list globname) (q : cQp.t) : Rep :=
  (**
  The number of global entries is an upper bound on the height of the
  derivation tree.
  *)
  let size := avl.IM.cardinal σ.(genv_tu).(types) in
  derivationsR' tu q size include_base cls path.

(* conveniences for the common pattern *)
Notation init_derivationR cls path q := (derivationR cls%bs (path%bs ++ [cls%bs]) q).
Notation init_derivationsR cls path q := (derivationsR cls%bs (path%bs ++ [cls%bs]) q).

(**
[wp_init_identity cls Q] updates the identities of "this" by updating
the [identity] of all base classes (transitively) and producing the
new identity for "this".

TODO: Make this an [mpred]
*)
Definition wp_init_identity `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (Q : mpred) : Rep :=
  derivationsR tu false cls [] (cQp.mut 1) **
  (derivationsR tu true cls [cls] (cQp.mut 1) -* pureR Q).

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : mpred).

  Lemma wp_init_identity_frame tu cls Q Q' :
    pureR (Q' -* Q) |-- wp_init_identity tu cls Q' -* wp_init_identity tu cls Q.
  Proof.
    iIntros "X [$ Y] Z". rewrite pureR_wand. iApply "X". by iApply "Y".
  Qed.

  Lemma _at_wp_init_identity_frame tu cls Q Q' p :
    Q' -* Q |-- (p |-> wp_init_identity tu cls Q') -* (p |-> wp_init_identity tu cls Q).
  Proof. by rewrite -_at_wand -wp_init_identity_frame _at_pureR. Qed.
End with_cpp.

(**
[wp_revert_identity cls Q] updates the identities of "this" by taking
the [identity] of this class and transitively updating the [identity]
of all base classes to remove [cls] as the most derived class.

TODO: Make this an [mpred]
*)
Definition wp_revert_identity `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (Q : mpred) : Rep :=
  derivationsR tu true cls [cls] (cQp.mut 1) **
  (derivationsR tu false cls [] (cQp.mut 1) -* pureR Q).

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : mpred).

  Lemma wp_revert_identity_frame tu cls Q Q' :
    pureR (Q' -* Q) |-- wp_revert_identity tu cls Q' -* wp_revert_identity tu cls Q.
  Proof.
    iIntros "X [$ Y] Z". rewrite pureR_wand. iApply "X". by iApply "Y".
  Qed.

  (** sanity chect that initialization and revert are inverses *)
  Lemma wp_init_revert tu cls Q p :
    let REQ := derivationsR tu false cls [] (cQp.mut 1) in
    p |-> REQ ** Q
    |-- p |-> wp_init_identity tu cls (p |-> wp_revert_identity tu cls (p |-> REQ ** Q)).
  Proof.
    rewrite /wp_revert_identity/wp_init_identity.
    rewrite !_at_sep !_at_wand !_at_pureR.
    iIntros "[$ $] $ $".
  Qed.
End with_cpp.
#[deprecated(since="20230820", note="use [_at_wp_init_identity_frame]")]
Notation wp_init_identity_frame' := _at_wp_init_identity_frame (only parsing).

(** ** Binding parameters *)

Definition wp_make_mutables `{Σ : cpp_logic, σ : genv} (tu : translation_unit) :=
  fix wp_make_mutables (args : list (ptr * decltype)) (Q : epred) : mpred :=
  match args with
  | nil => Q
  | p :: args => wp_make_mutables args $ wp_make_mutable tu p.1 p.2 Q
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wp_make_mutables_frame tu args Q Q' :
    Q -* Q' |-- wp_make_mutables tu args Q -* wp_make_mutables tu args Q'.
  Proof.
    move: Q Q'. induction args; intros; first done. cbn. iIntros "HQ".
    iApply (IHargs with "[HQ]"). by iApply wp_const_frame.
  Qed.
End with_cpp.

Definition Kcleanup `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (args : list (ptr * decltype)) (Q : Kpred) : Kpred :=
  Kat_exit (wp_make_mutables tu args) Q.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : Kpred).

  Lemma Kcleanup_frame tu args (Q Q' : Kpred) rt :
    Q rt -* Q' rt |-- Kcleanup tu args Q rt -* Kcleanup tu args Q' rt.
  Proof.
    iIntros "?". iApply Kat_exit_frame; [|done].
    iIntros (??) "?". by iApply wp_make_mutables_frame.
  Qed.
End with_cpp.

(**
[bind_vars tu ar ts args ρ Q] initializes a function's arguments
[args] according to its arity [ar] and declared parameter types [ts].

NOTE. We make arguments [const] here if necessary and then make them
mutable again in the second argument to [Q].
*)
Definition bind_vars `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (ar : function_arity) :=
  fix bind_vars (ts : list (ident * decltype)) (args : list ptr)
    (ρ : option ptr -> region) (Q : region -> list (ptr * decltype) -> epred) : mpred :=
  match ts with
  | nil =>
    match ar with
    | Ar_Definite =>
      match args with
      | nil => Q (ρ None) []
      | _ :: _ => ERROR "bind_vars: extra arguments"
      end
    | Ar_Variadic =>
      match args with
      | vap :: nil => Q (ρ $ Some vap) []
      | _ => ERROR "bind_vars: variadic function missing varargs"
      end
    end
  | xty :: ts =>
    match args with
    | p :: args =>
      (*
      NOTE: We need not gather additional qualifiers from an array's
      element type as Clang's parser eagerly "decays" a function's
      array parameter types to pointer types.
      *)
      let recurse := bind_vars ts args (fun vap => Rbind xty.1 p $ ρ vap) in
      let qty := decompose_type xty.2 in
      let ty := qty.2 in
      if q_const qty.1 then
        let* := wp_make_const tu p ty in
        let* ρ, consts := recurse in
        Q ρ $ (p,ty) :: consts
      else
        recurse Q
    | nil => ERROR "bind_vars: insufficient arguments"
    end
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : region -> list (ptr * decltype) -> epred).

  Lemma bind_vars_frame tu ar ts args ρ Q Q' :
    Forall ρ free, Q ρ free -* Q' ρ free
    |-- bind_vars tu ar ts args ρ Q -* bind_vars tu ar ts args ρ Q'.
  Proof.
    move: args ρ Q Q'. induction ts; intros [] *; cbn.
    { destruct ar; eauto. iIntros "HQ ?". by iApply "HQ". }
    { destruct ar; eauto. case_match; eauto. iIntros "HQ ?". by iApply "HQ". }
    { eauto. }
    { iIntros "HQ". case_match.
      - iApply wp_const_frame; [done|]. iApply IHts. iIntros (??) "?". by iApply "HQ".
      - iApply IHts. iIntros (??) "?". by iApply "HQ". }
  Qed.
End with_cpp.

(** ** The weakest precondition of a function *)

Definition wp_func `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (f : Func) (args : list ptr) (Q : ptr -> epred) : mpred :=
  match f.(f_body) with
  | None => ERROR "wp_func: no body"
  | Some body =>
    match body with
    | Impl body =>
      let ρ vap := Remp None vap f.(f_return) in
      letI* ρ, cleanup := bind_vars tu f.(f_arity) f.(f_params) args ρ in
      |> wp tu ρ body (Kcleanup tu cleanup $ Kreturn $ fun x => |={⊤}=> |> Q x)
    | Builtin builtin =>
      let ts := List.map snd f.(f_params) in
      (**
      TODO: This seems to ignore [f_arity].
      *)
      wp_builtin_func builtin (Tfunction (cc:=f.(f_cc)) f.(f_return) ts) args Q
    end
  end.

Definition func_ok `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (f : Func) (spec : function_spec) : mpred :=
  [| type_of_spec spec = type_of_value (Ofunction f) |] **
  □ Forall (Q : ptr -> epred) vals,
  spec.(fs_spec) vals Q -* wp_func tu f vals Q.

(** ** The weakest precondition of a method *)
(**
Note that in the calling convention for methods, the [this] parameter
is passed directly rather than being materialized like normal
parameters.
*)
Definition wp_method `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (m : Method) (args : list ptr) (Q : ptr -> epred) : mpred :=
  match m.(m_body) with
  | None => ERROR "wp_method: no body"
  | Some (UserDefined body) =>
    match args with
    | thisp :: rest_vals =>
      let ρ va := Remp (Some thisp) va m.(m_return) in
      letI* ρ, cleanup := bind_vars tu m.(m_arity) m.(m_params) rest_vals ρ in
      |> wp tu ρ body (Kcleanup tu cleanup $ Kreturn $ fun x => |={⊤}=> |> Q x)
    | _ => ERROR "wp_method: no arguments"
    end
  | Some _ => UNSUPPORTED "wp_method: defaulted methods"
  end.

Definition method_ok `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (m : Method) (spec : function_spec) : mpred :=
  [| type_of_spec spec = type_of_value (Omethod m) |] **
  □ Forall (Q : ptr -> mpred) vals,
  spec.(fs_spec) vals Q -* wp_method tu m vals Q.

(** ** Weakest precondition of a constructor *)

(**
Initialization of members in the initializer list
*)
Definition wpi_members `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (ρ : region)
    (cls : globname) (this : ptr) (inits : list Initializer) :=
  fix wpi_members (members : list Member) (Q : epred) : mpred :=
  match members with
  | nil => Q
  | m :: members =>
    let initializer_for (i : Initializer) :=
      match i.(init_path) with
      | InitField x
      | InitIndirect ((x,_) :: _) _ => bool_decide (m.(mem_name) = x)
      | _ => false
      end
    in
    match List.filter initializer_for inits with
    | nil =>
      (*
      there is no initializer for this member, so we "default
      initialize" it (see https://eel.is/c++draft/dcl.init#general-7 )
      *)
      let* frees :=
        default_initialize tu m.(mem_type)
          (this ,, _field {| f_type := cls ; f_name := m.(mem_name) |})
      in
      let* := interp tu frees in
      wpi_members members Q
    | i :: is' =>
      match i.(init_path) with
      | InitField _ (* = m.(mem_name) *) =>
        match is' with
        | nil =>
          (* there is a *unique* initializer for this field *)
          wpi tu ρ cls this i (wpi_members members Q)
        | _ =>
          (* there are multiple initializers for this field *)
          ERROR ("multiple initializers for field: " ++ cls ++ "::" ++ m.(mem_name))
        end
      | InitIndirect _ _ =>
        (*
        this is initializing an object via sub-objets using indirect
        initialization.

        TODO currently not supported
        *)
        UNSUPPORTED ("indirect initialization: " ++ cls ++ "::" ++ m.(mem_name))
      | _ => False%I (* unreachable due to the filter *)
      end
    end
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : epred).

  Lemma wpi_members_frame tu ρ cls this inits flds Q Q' :
    Q -* Q'
    |-- wpi_members tu ρ cls this inits flds Q -* wpi_members tu ρ cls this inits flds Q'.
  Proof.
    move: Q Q'. induction flds; intros; first done. cbn.
    case_match.
    { iIntros "a"; iApply default_initialize_frame; [done|].
      iIntros (?); iApply interp_frame. by iApply IHflds. }
    { case_match; eauto.
      case_match; eauto.
      iIntros "a".
      iApply wpi_frame => //.
      by iApply IHflds. }
  Qed.
End with_cpp.

(**
Initialization of bases in the initializer list
*)
Definition wpi_bases `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ρ : region) (cls : globname) (this : ptr) (inits : list Initializer) :=
  fix wpi_bases (bases : list globname) (Q : epred) : mpred :=
  match bases with
  | nil => Q
  | b :: bases =>
    match List.filter (fun i => bool_decide (i.(init_path) = InitBase b)) inits with
    | nil =>
      (*
      There is no initializer for this base class.

      TODO: Use the default constructor, or drop this TODO
      *)
      ERROR ("missing base class initializer: " ++ cls)
    | i :: nil =>
      (* there is an initializer for this class *)
      wpi tu ρ cls this i (wpi_bases bases Q)
    | _ :: _ :: _ =>
      (* there are multiple initializers for this, so we fail *)
      ERROR ("multiple initializers for base: " ++ cls ++ "::" ++ b)
    end
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : epred).

  Lemma wpi_bases_frame tu ρ cls p inits bases Q Q' :
    Q -* Q'
    |-- wpi_bases tu ρ cls p inits bases Q -* wpi_bases tu ρ cls p inits bases Q'.
  Proof.
    move: Q Q'. induction bases; intros; first done. cbn.
    case_match; eauto.
    case_match; eauto.
    iIntros "a".
    iApply wpi_frame => //.
    by iApply IHbases.
  Qed.
End with_cpp.

Definition wp_struct_initializer_list `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (s : Struct) (ρ : region) (cls : globname) (this : ptr)
    (inits : list Initializer) (Q : epred) : mpred :=
  match List.find (fun i => bool_decide (i.(init_path) = InitThis)) inits with
  | Some {| init_type := ty ; init_init := e |} =>
    match inits with
    | _ :: nil =>
      if bool_decide (drop_qualifiers ty = Tnamed cls) then
        (* this is a delegating constructor, simply delegate. *)
        wp_init tu ρ (Tnamed cls) this e (fun frees => interp tu frees Q)
      else
        (* the type names do not match, this should never happen *)
        ERROR "type name mismatch"
    | _ =>
      (*
      delegating constructors are not allowed to have any other
      initializers
      *)
      ERROR "delegating constructor has other initializers"
    end
  | None =>
    let bases := wpi_bases tu ρ cls this inits (List.map fst s.(s_bases)) in
    let members := wpi_members tu ρ cls this inits s.(s_fields) in
    let ident Q := this |-> wp_init_identity tu cls Q in
    (**
    Provide strict validity for [this] and immediate members,
    initialize the bases, then the identity, then initialize the
    members, following http://eel.is/c++draft/class.base.init#13
    (except virtual base classes, which are unsupported)

    NOTE we get the [structR] at the end since [structR (cQp.mut 1)
    cls |-- type_ptrR (Tnamed cls)].
    *)
    this |-> svalid_members cls ((fun m => (m.(mem_name), m.(mem_type))) <$> s.(s_fields)) -*
    bases (ident (members (this |-> structR cls (cQp.mut 1) -* Q)))
  end.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : epred).

  Lemma wp_struct_initializer_list_frame tu s ρ cls p inits Q Q' :
    Q -* Q'
    |-- wp_struct_initializer_list tu s ρ cls p inits Q -* wp_struct_initializer_list tu s ρ cls p inits Q'.
  Proof.
    rewrite /wp_struct_initializer_list/=. case_match.
    { case_match => //.
      destruct l; eauto.
      case_match; eauto.
      iIntros "x".
      iApply wp_init_frame => //.
      iIntros (?); by iApply interp_frame. }
    { iIntros "Q".
      iApply wand_frame.
      iApply wpi_bases_frame.
      iApply _at_wp_init_identity_frame.
      iApply wpi_members_frame.
      by iApply wand_frame. }
  Qed.
End with_cpp.

Definition wp_union_initializer_list `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (u : translation_unit.Union) (ρ : region) (cls : globname) (this : ptr)
    (inits : list Initializer) (Q : epred) : mpred :=
  match inits with
  | [] => Q
  | [{| init_path := InitField f ; init_type := te ; init_init := e |} as init] =>
    match list_find (fun m => f = m.(mem_name)) u.(u_fields) with
    | None => ERROR "field not found in union initialization"
    | Some (n, m) => wpi tu ρ cls this init $ this |-> unionR cls (cQp.m 1) (Some n) -* Q
    end
  | _ =>
    UNSUPPORTED "indirect (or self) union initialization is not currently supported"
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : epred).

  Lemma wp_union_initializer_list_frame tu u ρ cls p inits Q Q' :
    Q -* Q'
    |-- wp_union_initializer_list tu u ρ cls p inits Q -* wp_union_initializer_list tu u ρ cls p inits Q'.
  Proof.
    rewrite /wp_union_initializer_list/=. case_match; eauto.
    { iIntros "K".
      repeat case_match; eauto.
      iApply wpi_frame; [done|].
      iIntros "X Y"; iApply "K"; iApply "X"; done. }
  Qed.
End with_cpp.

(**
A special version of return to match the C++ rule that constructors
and destructors must not syntactically return a value, e.g. `return
f()` for `void f()` are not allowed.

NOTE: we could drop this in favor of relying on the compiler to check
this.
*)
Definition Kreturn_void `{Σ : cpp_logic} (P : mpred) : Kpred :=
  KP $ funI rt =>
  match rt with
  | Normal | ReturnVoid => P
  | _ => False
  end.

(**
[wp_ctor tu ctor args Q] is the weakest pre-condition (with
post-condition [Q]) running the constructor [ctor] with arguments
[args].

Note that the constructor semantics consumes the entire [blockR] of
the object that is being constructed and the C++ abstract machine
breaks this block down producing usable† memory.

**Alternative**: Because constructor calls are *always* syntactically
distinguished (since C++ does not allow taking a pointer to a
constructor), we know that any invocation of a constructor will be
from a [wp_init] which means that the C++ abstract machine will
already own the memory (see the documentation for [wp_init] in
[wp.v]). In order to enforce this semantically within the abstract
machine, we would need a new predicate to say "a constructor with the
given specification" (rather than simply desugaring this to "a
function with the given specification").

NOTE: supporting virtual inheritence will require us to add
constructor kinds here

† It is not necessarily initialized, e.g. because primitive fields are
not initialized (you get an [uninitR]), but you will get something
that implies [type_ptr].
*)
Definition wp_ctor `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ctor : Ctor) (args : list ptr) (Q : ptr -> epred) : mpred :=
  match ctor.(c_body) with
  | None => ERROR "wp_ctor: no body"
  | Some Defaulted => UNSUPPORTED "defaulted constructors"
  | Some (UserDefined (inits, body)) =>
    match args with
    | thisp :: rest_vals =>
      let ty := Tnamed ctor.(c_class) in
      match tu !! ctor.(c_class) with
      | Some (Gstruct cls) =>
        (*
        this is a structure.

        We require that you give up the *entire* block of memory
        [tblockR] that the object will use.
        *)
        thisp |-> tblockR ty (cQp.mut 1) **
        |>
        let ρ vap := Remp (Some thisp) vap Tvoid in
        let* ρ, cleanup := bind_vars tu ctor.(c_arity) ctor.(c_params) rest_vals ρ in
        let* := wp_struct_initializer_list tu cls ρ ctor.(c_class) thisp inits in
        let* := wp tu ρ body in
        let* := Kcleanup tu cleanup in
        let* := Kreturn_void in
        |={⊤}=> |>
        Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p

      | Some (Gunion union) =>
        (*
        this is a union.

        We require that you give up the *entire* block of memory
        [tblockR] that the object will use.
        *)
        thisp |-> tblockR ty (cQp.mut 1) **
        |>
        let ρ vap := Remp (Some thisp) vap Tvoid in
        let* ρ, cleanup := bind_vars tu ctor.(c_arity) ctor.(c_params) rest_vals ρ in
        let* := wp_union_initializer_list tu union ρ ctor.(c_class) thisp inits in
        let* := wp tu ρ body in
        let* := Kcleanup tu cleanup in
        let* := Kreturn_void in
        |={⊤}=> |>
        Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p

      | _ => ERROR ("constructor for non-aggregate (" ++ ctor.(c_class) ++ ")")
      end
    | _ => ERROR "constructor without leading [this] argument"
    end
  end%I.

Definition ctor_ok `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ctor : Ctor) (spec : function_spec) : mpred :=
  [| type_of_spec spec = type_of_value (Oconstructor ctor) |] **
  □ Forall (Q : ptr -> epred) vals,
  spec.(fs_spec) vals Q -* wp_ctor tu ctor vals Q.


(** ** Weakest precondition of a destructor *)

Definition wpd_bases `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) (bases : list globname) (Q : epred) : mpred :=
  let del_base base := FreeTemps.delete (Tnamed base) (this ,, _base cls base) in
  interp tu (FreeTemps.seqs_rev (List.map del_base bases)) Q.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wpd_bases_frame tu cls this bases Q Q' :
    Q -* Q' |-- wpd_bases tu cls this bases Q -* wpd_bases tu cls this bases Q'.
  Proof. apply interp_frame. Qed.
End with_cpp.

Definition wpd_members `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) (members : list Member) (Q : epred) : mpred :=
  let del_member m := FreeTemps.delete m.(mem_type) (this ,, _field {| f_name := m.(mem_name) ; f_type := cls |}) in
  interp tu (FreeTemps.seqs_rev (List.map del_member members)) Q.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wpd_members_frame tu cls this members Q Q' :
    Q -* Q' |-- wpd_members tu cls this members Q -* wpd_members tu cls this members Q'.
  Proof. apply interp_frame. Qed.
End with_cpp.

(**
[wp_dtor tu dtor args Q] defines the semantics of the destructor
[dtor] when applied to [args] with post-condition [Q].

Note that destructors are not always syntactically distinguished from
function calls (e.g. in the case of [c.~C()]). Therefore, in order to
have a uniform specification, they need to return the underlying
memory (i.e. a [this |-> tblockR (Tnamed cls) 1]) to the caller. When
the program is destroying this object, e.g. due to stack allocation,
this resource will be consumed immediately.
*)
Definition wp_dtor `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (dtor : Dtor) (args : list ptr) (Q : ptr -> epred) : mpred :=
  match dtor.(d_body) with
  | None => ERROR "wp_dtor: no body"
  | Some body =>
    let epilog :=
      match tu !! dtor.(d_class) with
      | Some (Gstruct s) => Some $ fun (thisp : ptr) =>
        thisp |-> structR dtor.(d_class) (cQp.mut 1) **
        (** Destroy fields *)
        let* := wpd_members tu dtor.(d_class) thisp s.(s_fields) in
        (** Destroy identity of the object *)
        thisp |-> wp_revert_identity tu dtor.(d_class) (
          (** Destroy base classes (reverse order) *)
          let* := wpd_bases tu dtor.(d_class) thisp (List.map fst s.(s_bases)) in
          (**
          Destroy each object returning its memory to the abstract
          machine. Then the abstract machine gives this memory back to
          the program.

          NOTE the [|>] here is for the function epilog.
          *)
          thisp |-> tblockR (Tnamed dtor.(d_class)) (cQp.mut 1) -*
          |={⊤}=> |> Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p
        )
      | Some (Gunion u) => Some $ fun (thisp : ptr) =>
        (*
        the function epilog of a union destructor doesn't actually
        destroy anything because it isn't clear what to destroy (this
        is dictated by the C++ standard). Instead, the epilog provides
        a fancy update to destroy things.

        In practice, this means that programs can only destroy unions
        automatically where they can prove the active entry has a
        trivial destructor or is already destroyed.
        *)
        |={⊤}=> thisp |-> tblockR (Tnamed dtor.(d_class)) (cQp.mut 1) **
        (
          thisp |-> tblockR (Tnamed dtor.(d_class)) (cQp.mut 1) -*
          |={⊤}=> |> Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p
        )
      | _ => None
      end
    in
    match epilog , args with
    | Some epilog , thisp :: nil =>
      (**
      The function consumes a step
      *)
      |>
      let* :=
        match body return Kpred -> mpred with
        | Defaulted => fun k => |={top}=> k Normal
        | UserDefined body => wp tu (Remp (Some thisp) None Tvoid) body
        end
      in
      Kreturn_void (epilog thisp)
    | None , _ => ERROR "wp_dtor: not a structure or union"
    | Some _ , _ => ERROR "wp_dtor: expected one argument"
    end
  end%I.

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

Definition dtor_ok `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (dtor : Dtor) (spec : function_spec) : mpred :=
  [| type_of_spec spec = type_of_value (Odestructor dtor) |] **
  □ Forall (Q : ptr -> mpred) vals,
  spec.(fs_spec) vals Q -* wp_dtor tu dtor vals Q.
