(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Util Logic PLogic Semantics Wp Typing Init Deinit.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

(* note: only used for demonstration purposes. *)
From Cpp.Auto Require Import Discharge.

Local Ltac t :=
  discharge fail fail fail ltac:(canceler fail auto) auto.

Fixpoint is_void (t : type) : bool :=
  match t with
  | Tqualified _ t => is_void t
  | Tvoid => true
  | _ => false
  end.

Lemma wandSP_only_provableL : forall (P : Prop) Q R,
    P ->
    Q |-- R ->
    [| P |] -* Q |-- R.
Proof.
  intros.
  rewrite <- H0; clear H0.
  etransitivity.
  2: eapply sepSPAdj; reflexivity.
  t.
Qed.


Lemma wandSP_only_provableR : forall (A : Prop) B C,
    (A -> B |-- C) ->
    B |-- [| A |] -* C.
Proof.
  intros.
  unfold only_provable.
  eapply wandSPI.
  rewrite <- embedPropExists'.
  specialize (landexistsDL1 (fun _: A => ltrue) (@empSP mpred _)). simpl.
  intros. rewrite H0.
  setoid_rewrite landtrueL.
  rewrite <- bilexistssc.
  eapply lexistsL.
  intros.
  etransitivity; [ | eapply H ]; auto.
  t.
Qed.

Lemma forallEach_primes:
  forall (ts : list type)
    (fs' : arrowFrom val ts ((val -> mpred) -> mpred)) Z,
    Forall vs : list val,
  [| Datatypes.length vs = Datatypes.length ts |] -*
  (Forall Q : val -> mpred,
     applyEach ts vs fs'
               (fun (k : (val -> mpred) -> mpred) (_ : list (type * val)) => k Q) -*
               Z vs Q) -|-
  ForallEach ts fs'
  (fun (PQ : (val -> mpred) -> mpred) (args : list (type * val)) =>
     Forall Q : val -> mpred, PQ Q -* Z (map snd args) Q).
Proof.
  induction ts.
  { simpl. intros.
    split.
    { eapply lforallR; intro Q.
      eapply (lforallL nil).
      eapply wandSP_only_provableL; [ reflexivity | ].
      eapply lforallL. reflexivity. }
    { eapply lforallR. intros.
      destruct x.
      { eapply wandSP_only_provableR. reflexivity. }
      { eapply wandSP_only_provableR. intros.
        inversion H. } } }
  { simpl. intros.
    split.
    { eapply lforallR.
      intros.
      rewrite <- (IHts (fs' x) (fun a b => Z (x :: a) b)).
      eapply lforallR. intros.
      eapply (lforallL (x :: x0)).
      eapply wandSP_only_provableR; intros.
      eapply wandSP_only_provableL; [ simpl; f_equal; eassumption | ].
      reflexivity. }
    { eapply lforallR; intros.
      eapply wandSP_only_provableR; intros.
      destruct x.
      { eapply lforallR; intro.
        eapply wandSPAdj'.
        rewrite sepSP_falseL.
        eapply lfalseL. }
      { eapply (lforallL v).
        destruct (IHts (fs' v) (fun xs => Z (v :: xs))).
        rewrite H1; clear H0 H1.
        eapply (lforallL x).
        eapply wandSP_only_provableL.
        simpl in H.
        inversion H. reflexivity. reflexivity. } } }
Qed.

Arguments ForallEach {_ _ _ _ _} [_] _ _.

Lemma lexists_known : forall t a P,
    Exists x : t, [| x = a |] ** P x -|- P a.
Proof.
  split; intros; t. subst; reflexivity.
Qed.


(* above are candidates for removal *)



Module Type Func.

  (* function specifications written in weakest pre-condition style.
   *
   * note(gmm): it might be better to make the `list val` into a
   * `vector val (length fs_arguments)`.
   *)
  Record function_spec' : Type :=
  { fs'_return : type
  ; fs'_arguments : list type
  ; fs'_spec : thread_info -> list val -> (val -> mpred) -> mpred
  }.

  (* this is the core definition that everything will be based on. *)
  Definition cptr' {resolve} ti (fs : function_spec') : Rep :=
    {| repr p :=
         Forall vs,
         [| List.length vs = List.length fs.(fs'_arguments) |] -*
         Forall Q, (fs.(fs'_spec) ti) vs Q -* fspec (resolve:=resolve) p vs ti Q |}.

  (* function specifications written in weakest pre-condition style.
   *
   * the motivation for `function_spec` is to avoid having to destruct things
   * repeatedly; however, they are more difficult to prove things about, so
   * it might be better to do this reasoning post-facto.
   *)
  Record function_spec : Type :=
  { fs_return : type
  ; fs_arguments : list type
  ; fs_spec : thread_info -> arrowFrom val fs_arguments ((val -> mpred) -> mpred)
  }.

  (* this is the core definition that everything will be based on. *)
  Definition cptr {resolve} ti (fs : function_spec) : Rep :=
    {| repr p :=
         ForallEach (fs.(fs_spec) ti) (fun PQ args =>
            Forall Q, PQ Q -* fspec (resolve:=resolve) p (List.map snd args) ti Q) |}.

  Record WithPrePost : Type :=
    { wpp_with : tele
    ; wpp_pre : teleF mpred wpp_with
    ; wpp_post : teleF (val -> mpred) wpp_with }.

  Fixpoint WppD' {t : tele}
  : forall (P : teleF mpred t) (Q : teleF (val -> mpred) t), (val -> mpred) -> mpred :=
    match t as t
          return forall (P : teleF mpred t) (Q : teleF (val -> mpred) t),
                 (val -> mpred) -> mpred
    with
    | tdone => fun P Q Q' => P ** (Forall result, Q result -* Q' result)
    | tcons ts => fun P Q Q' => Exists x, @WppD' (ts x) (P x) (Q x) Q'
    end.

  Definition WppD (wpp : WithPrePost) : (val -> mpred) -> mpred :=
    WppD' wpp.(wpp_pre) wpp.(wpp_post).
  Arguments WppD !_ / .

  Section with_resolve.
    Context {resolve : genv}.

  (* Hoare triple for a function.
   * note(gmm): these should include linkage specifications.
   *)
  Definition TSFunction (ret : type) (targs : list type)
             (PQ : thread_info -> arrowFrom val targs WithPrePost)
  : function_spec :=
    {| fs_return := ret
     ; fs_arguments := targs
     ; fs_spec ti := arrowFrom_map WppD (PQ ti) |}.


  Definition SFunction (ret : type) (targs : list type)
             (PQ : arrowFrom val targs WithPrePost)
  : function_spec :=
    TSFunction ret targs (fun _ => PQ).

  (* Hoare triple for a constructor.
   *)
  Definition TSConstructor (class : globname)
             (targs : list type)
             (PQ : thread_info -> val -> arrowFrom val targs WithPrePost)
  : function_spec :=
    let this_type := Qmut (Tref class) in
    TSFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
              (fun ti this => arrowFrom_map (fun wpp =>
                 {| wpp_with := wpp.(wpp_with)
                  ; wpp_pre :=
                    teleF_map (fun P => _at (_eq this) (uninit (Tref class)) ** P) wpp.(wpp_pre)
                  ; wpp_post := wpp.(wpp_post)
                  |}) (PQ ti this)).

  Definition SConstructor (class : globname) (targs : list type)
             (PQ : val -> arrowFrom val targs WithPrePost)
  : function_spec := TSConstructor class targs (fun _ => PQ).

  (* Hoare triple for a destructor.
   *)
  Definition TSDestructor (class : globname) (PQ : thread_info -> val -> WithPrePost)
  : function_spec :=
    let this_type := Qmut (Tref class) in
    TSFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
               (fun ti this =>
                  let PQ := PQ ti this in
                 {| wpp_with := PQ.(wpp_with)
                  ; wpp_pre := PQ.(wpp_pre)
                  ; wpp_post := teleF_map (fun Q res => _at (_eq this) (tany (Tref class)) ** Q res) PQ.(wpp_post)
                  |}).

  Definition SDestructor (class : globname) (PQ : val -> WithPrePost)
  : function_spec := TSDestructor class (fun _ => PQ).

  (* Hoare triple for a method.
   *)
  Definition TSMethod (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : thread_info -> val -> arrowFrom val targs WithPrePost)
  : function_spec :=
    let class_type := Tref class in
    let this_type := Tqualified qual class_type in
    TSFunction ret (Qconst (Tpointer this_type) :: targs) PQ.
      (* ^ todo(gmm): this looks wrong. something isn't going
       * to fit together with respect to calling conventions and
       * specifications.
       *)

  Definition SMethod (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : val -> arrowFrom val targs WithPrePost)
  : function_spec := TSMethod class qual ret targs (fun _ => PQ).

  Lemma cptr_cptr' : forall ti fs fs',
      fs'.(fs'_arguments) = fs.(fs_arguments) ->
      fs'.(fs'_return) = fs.(fs_return) ->
      (forall Q vs,
          (fs'.(fs'_spec) ti) vs Q -|-
          applyEach fs.(fs_arguments) vs (fs.(fs_spec) ti) (fun k _ => k Q)) ->
      cptr (resolve:=resolve) ti fs -|- cptr' (resolve:=resolve) ti fs'.
  Proof.
    unfold cptr'. intros.
    destruct fs, fs'. simpl in *. subst.
    eapply Rep_equiv_ext_equiv. simpl; intros.
    setoid_rewrite H1; clear H1.
    rewrite <- forallEach_primes with (Z:=fun a b => fspec x a ti b).
    reflexivity.
  Qed.

(*
  Theorem triple_sound : forall p r ts ti PQ vs,
      List.length vs = List.length ts ->
      forall g : (PQ vs).(wpp_with),
        cptr p ti (ht r ts PQ) ** (PQ vs).(wpp_pre) g
        |-- fspec p vs ti ((PQ vs).(wpp_post) g).
  Proof.
    unfold ht, cptr.
    intros.
    eapply sepSPAdj.
    eapply (lforallL vs).
    simpl.
    eapply wandSP_only_provableL. auto.
    eapply (lforallL (wpp_post (PQ vs) g)).
    eapply wandSP_lentails_m; try reflexivity.
    red.
    t.
  Qed.

    Theorem triple_apply : forall p r ts F F' vs (PQ : list val -> WithPrePost) K,
        List.length vs = List.length ts -> (* trivial *)
        forall g : (PQ vs).(wpp_with), (* existential quantifier *)
          F |-- (PQ vs).(wpp_pre) g ** F' -> (* pre-condition *)
          (forall r, (PQ vs).(wpp_post) g r |-- K r) ->
          cptr p ti (ht r ts PQ) ** F |-- fspec p vs ti K ** F'.
    Proof.
      intros.
      specialize (triple_sound p r ts ti PQ vs H).
      unfold ht in *.
      rewrite H0 in *; clear H0.
      intros.
      specialize (H0 g).
      rewrite <- sepSPA.
      rewrite H0.
      t.
      eapply fspec_conseq. assumption.
    Qed.
*)

  Theorem triple'_apply
  : forall ti p r ts F F' vs (PQ : arrowFrom val ts WithPrePost) K,
      List.length vs = List.length ts ->
      F |-- applyEach ts vs PQ (fun wpp _ => WppD wpp) K ** F' ->
      _at (_eq p) (cptr (resolve:=resolve) ti (SFunction r ts PQ)) ** F
      |-- fspec (resolve:=resolve) p vs ti K ** F'.
  Proof.
    intros.
    rewrite cptr_cptr'.
    instantiate (1:=
      {| fs'_return := r
       ; fs'_arguments := ts
       ; fs'_spec ti vs0 Q :=
         applyEach ts vs0 ((SFunction r ts PQ).(fs_spec) ti)
                   (fun (k : (val -> mpred) -> mpred) _ => k Q) |}).
    2,3,4: reflexivity.
    Transparent _at _eq. unfold _at, _eq. simpl. Opaque _at _eq.
    rewrite lexists_known.
    eapply sepSPAdj.
    eapply (lforallL vs).
    eapply wandSP_only_provableL; eauto.
    eapply (lforallL K).
    eapply wandSPAdj.
    eapply wandSP_cancel.
    rewrite H0; clear H0.
    t.
    clear.
    revert vs. induction ts; destruct vs; simpl; try reflexivity.
    { rewrite IHts. t. }
  Qed.

  Definition cglob (gn : globname) ti (spec : function_spec)
  : mpred :=
    _at (_global gn) (cptr (resolve:=resolve) ti spec).

  Axiom cglob_dup : forall p ti fs,
      cglob p ti fs -|- cglob p ti fs ** cglob p ti fs.
  (* i was thinking that i could store static variables in invariants.
   * i'm not sure how this works with function pointer weakening.
   *)
  Axiom cglob_weaken : forall a b c, cglob a b c |-- empSP.

  (* this is problematic because if `thread_info` was empty, then
   * the left hand side woudl be ltrue, not empSP
   *)
  Lemma cglob_weaken_any_ti :
    forall (a : globname) (c : function_spec),
      (Forall ti, cglob a ti c) |-- empSP.
  Proof.
    intros.
    etransitivity.
    eapply lforall_lentails_m.
    red. intros. instantiate (1:=fun _ => empSP).
    eapply cglob_weaken.
    eapply use_forall_unused.
    admit.
  Admitted.

  Lemma cglob_weaken_any_ti_later :
    forall (a : globname) (c : function_spec),
      (Forall ti, |> cglob a ti c) |-- empSP.
  Proof.
    intros.
    rewrite <- spec_later_forall.
    rewrite cglob_weaken_any_ti.
    admit.
  Admitted.


  End with_resolve.

    Fixpoint bind_type ρ (t : type) (x : ident) (v : val) : mpred :=
      match t with
      | Tqualified _ t => bind_type ρ t x v
      | Treference ref => _local ρ x &~ v
      | Tref _         => _local ρ x &~ v
      | _              => tlocal ρ x (tprim t v)
      end.

    Fixpoint bind_type_free ρ (t : type) (x : ident) (v : val) : mpred :=
      match t with
      | Tqualified _ t => bind_type_free ρ t x v
      | Treference ref => _local ρ x &~ v
      | Tref cls       => _local ρ x &~ v
      | _              => tlocal ρ x (tany t)
      end.
    (* todo(gmm): c++ guarantees the order of destruction *)


    (* the proof obligation for a function
     *)
    Definition func_ok {resolve:genv} (ret : type) (params : list (ident * type))
               (body : Stmt)
               (ti : thread_info) (spec : function_spec)
    : mpred :=
      [| ret = spec.(fs_return) |] **
      [| spec.(fs_arguments) = List.map snd params |] **
      ForallEach (spec.(fs_spec) ti) (fun PQ args =>
        Forall ρ : region,
        let vals := List.map snd args in

        (* this is what is created from the parameters *)
        let binds :=
            sepSPs (zip (fun '(x, t) 'v => bind_type ρ t x v) params vals) in
        (* this is what is freed on return *)
        let frees :=
            sepSPs (zip (fun '(x, t) 'v =>
                           bind_type_free ρ t x v)
                   (rev params) (rev vals)) in
        if is_void ret
        then
          Forall Q : mpred,
          (binds ** PQ (fun _ => Q)) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (void_return Q)))
        else
          Forall Q : val -> mpred,
          (binds ** PQ Q) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (val_return Q)))).



    Definition method_ok {resolve} (meth : Method) (ti : thread_info) (spec : function_spec)
      : mpred :=
      match meth.(m_body) with
      | None => lfalse
      | Some body =>
        let this_type :=
            Qconst (Tpointer (Tqualified meth.(m_this_qual) (Tref meth.(m_class))))
        in
        [| spec.(fs_return) = meth.(m_return) |] **
        [| spec.(fs_arguments) = this_type :: List.map snd meth.(m_params) |] **
        ForallEach (spec.(fs_spec) ti) (fun PQ args =>
          Forall ρ : region,
          let vals := List.map snd args in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds :=
                _local ρ "#this" &~ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type ρ t x v) meth.(m_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                _local ρ "#this" &~ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type_free ρ t x v) (rev meth.(m_params))
                       (rev rest_vals))
            in
            if is_void meth.(m_return)
            then
              Forall Q : mpred,
              (binds ** PQ (fun _ => Q)) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (void_return Q)))
            else
              Forall Q : val -> mpred,
              (binds ** PQ Q) -* (wp (resolve:=resolve) ti ρ body (Kfree frees (val_return Q)))
          end)
      end.

    Definition wp_ctor {resolve : genv} (cls : globname) (ti : thread_info) (ρ : region)
               (this_val : val)
               (inits : list (FieldOrBase * Expr)) (body : Stmt)
               (Q : Kpreds)
    : mpred :=
      wpis (resolve:=resolve) ti ρ cls this_val inits
           (wp (resolve:=resolve) ti ρ body Q).


    Definition ctor_ok {resolve} (ctor : Ctor) ti (spec : function_spec)
    : mpred :=
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
        ForallEach (spec.(fs_spec) ti) (fun PQ args =>
          Forall ρ,
          let vals := List.map snd args in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds :=
                _local ρ "#this" &~ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type ρ t x v) ctor.(c_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                _local ρ "#this" &~ this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type_free ρ t x v) (rev ctor.(c_params)) (rev rest_vals))
            in
            Forall Q : mpred,
            (binds ** PQ (fun _ => Q)) -*
            (wp_ctor (resolve:=resolve) ctor.(c_class) ti ρ this_val init body
                     (Kfree frees (void_return Q)))
          end)
      end.

    Definition wp_dtor {resolve : genv} (cls : globname) (ti : thread_info) (ρ : region)
               (this_val : val)
               (body : Stmt) (dtors : list (FieldOrBase * globname))
               (frees : mpred) (Q : mpred)
    : mpred :=
      wp (resolve:=resolve) ti ρ body
         (Kfree frees (void_return (wpds (resolve:=resolve) ti ρ cls this_val dtors Q))).

    Definition dtor_ok {resolve: genv}(dtor : Dtor) ti (spec : function_spec)
    : mpred :=
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
        ForallEach (spec.(fs_spec) ti) (fun PQ args =>
          Forall ρ,
          let vals := List.map snd args in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds := _local ρ "#this" &~ this_val in
            (* this is what is freed on return *)
            let frees := _local ρ "#this" &~ this_val in
            Forall Q : mpred,
              (binds ** PQ (fun _ => Q)) -*
              (wp_dtor (resolve:=resolve) dtor.(d_class) ti ρ this_val body deinit frees Q)
          end)
      end.

End Func.

Declare Module F : Func.

Export F.
