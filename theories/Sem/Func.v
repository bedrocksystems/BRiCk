Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Util Logic Expr Stmt Semantics.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

(* note: only used for demonstration purposes. *)
From auto.Tactics Require Import Discharge.


Fixpoint sepSPs (ls : list mpred) : mpred :=
  match ls with
  | nil => empSP
  | l :: ls => l ** sepSPs ls
  end.

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
  2: eapply sepSPAdj.
  2: reflexivity.
  rewrite <- empSPR at 1.
  eapply scME. reflexivity.
  discharge auto auto.
Qed.


Lemma wandSP_only_provableR : forall (A : Prop) B C,
    (A -> B |-- C) ->
    B |-- [| A |] -* C.
Proof.
  intros.
  unfold only_provable.
  eapply wandSPI.
  rewrite <- embedPropExists'.
  specialize (landexistsDL1 (fun _: A => ltrue) empSP). simpl.
  intros. rewrite H0.
  setoid_rewrite landtrueL.
  rewrite <- bilexistssc.
  eapply lexistsL.
  intros.
  etransitivity; [ | eapply H ]; auto.
  discharge fail auto.
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

Fixpoint ForallEach' {t u T} (ls : list t)
  : forall (v : arrowFrom u ls T)
      (P : T ->  list (t * u) -> mpred), mpred :=
  match ls with
  | nil => fun v P => P v nil
  | l :: ls => fun v P => Forall x,
                     ForallEach' ls (v x) (fun z xs => P z (cons (l, x) xs))
  end.

(* above are candidates for removal *)


Module Type Func.

  (* the guiding principle for a hoare triple is the following.
    { P } - { Q } = [] (P -* wp code Q)
   *)


  (* the pointer contains the code *)
  Parameter code_at : ptr -> Func -> mpred.
  (* code_at is freely duplicable *)
  Axiom code_at_dup : forall p f, code_at p f -|- code_at p f ** code_at p f.
  Axiom code_at_drop : forall p f, code_at p f |-- empSP.

  Parameter ctor_at : ptr -> Ctor -> mpred.
  Parameter dtor_at : ptr -> Dtor -> mpred.

  Parameter func_ok_raw : Func -> list val -> (val -> mpred) -> mpred.
  (* this assserts the frame axiom for function specifications
   *)
  Axiom func_ok_frame : forall v vs Q F,
      func_ok_raw v vs Q ** F |-- func_ok_raw v vs (fun res => Q res ** F).

  Definition fspec (n : val) (ls : list val) (Q : val -> mpred) : mpred :=
    Exists f, [| n = Vptr f |] **
    Exists func, code_at f func ** func_ok_raw func ls Q.

  (* todo(gmm): this is because func_ok is implemented using wp. *)
  Axiom fspec_conseq:
    forall (p : val) (vs : list val) (K m : val -> mpred),
      (forall r : val, m r |-- K r) -> fspec p vs m |-- fspec p vs K.

  Fixpoint uninitializedN (size : nat) (a : val) : mpred :=
    match size with
    | 0 => empSP
    | S size => (Exists x, ptsto a x) ** uninitializedN size (offset_ptr a 1)
    end.
  Definition uninitialized (size : N) : val -> mpred :=
    uninitializedN (BinNatDef.N.to_nat size).

  Definition uninitialized_ty (tn : type) (p : val) : mpred :=
    Exists sz, with_genv (fun g => [| @size_of g tn sz |]) **
                         uninitialized sz p.


  (** initialization lists
   *)
  Parameter wpi
  : forall {resolve : genv}
      (cls : globname) (this : val) (init : FieldOrBase ident globname * Expr)
      (Q : mpred), mpred.

  Fixpoint wpis {resolve : genv} (cls : globname) (this : val)
           (inits : list (FieldOrBase ident globname * Expr))
           (Q : mpred) : mpred :=
    match inits with
    | nil => Q
    | i :: is => @wpi resolve cls this i (@wpis resolve cls this is Q)
    end.

  (** destructor lists
   *
   *  the opposite of initializer lists, this is just a call to the
   *  destructors *in the right order*
   *)
  Parameter wpd
    : forall {resolve : genv} (cls : globname) (this : val)
        (init : FieldOrBase ident globname * globname)
        (Q : mpred), mpred.

  Fixpoint wpds {resolve : genv} (cls : globname) (this : val)
           (dests : list (FieldOrBase ident globname * globname))
           (Q : mpred) : mpred :=
    match dests with
    | nil => Q
    | d :: ds => @wpd resolve cls this d (@wpds resolve cls this ds Q)
    end.

  (* function specifications written in weakest pre-condition style.
   *
   * note(gmm): it might be better to make the `list val` into a
   * `vector val (length fs_arguments)`.
   *)
  Record function_spec : Type :=
  { fs_return : type
  ; fs_arguments : list type
  ; fs_specification : list val -> (val -> mpred) -> mpred
  }.


  (* todo(gmm): this might need to make some additional assumptions in
   * C/C++, e.g. the arguments are typed appropriately (in addition to being
   * the right length).
   *)
  Definition cptr (p : val) (PQ : function_spec) : mpred :=
    Forall vs,
    [| List.length vs = List.length PQ.(fs_arguments) |] -*
    Forall Q, PQ.(fs_specification) vs Q -* fspec p vs Q.


  (* function specifications written in weakest pre-condition style.
   *
   * the motivation for `function_spec'` is to avoid having to destruct things
   * repeatedly; however, they are more difficult to prove things about, so
   * it might be better to do this reasoning post-facto.
   *)
  Record function_spec' : Type :=
  { fs'_return : type
  ; fs'_arguments : list type
  ; fs'_specification : arrowFrom val fs'_arguments ((val -> mpred) -> mpred)
  }.

  (* this is the core definition that everything will be based on. *)
  Definition cptr' (p : val) (fs : function_spec') : mpred :=
    ForallEach _ fs.(fs'_specification) (fun PQ args =>
       Forall Q, PQ Q -* fspec p (List.map snd args) Q).

(*
    Axiom cptr'_dup : forall p fs, cptr' p fs -|- cptr' p fs ** cptr' p fs.
*)




    Record WithPrePost : Type :=
    { wpp_with : Type
    ; wpp_pre  : wpp_with -> mpred
    ; wpp_post : wpp_with -> val -> mpred
    }.

    Definition ht (ret : type) (targs : list type)
               (PQ : list val -> WithPrePost)
      : function_spec.
      refine (
          {| fs_return := ret
           ; fs_arguments := targs
           ; fs_specification := fun args Q =>
                Exists g : (PQ args).(wpp_with),
                           (Forall res, (PQ args).(wpp_post) g res -* Q res)
                             ** (PQ args).(wpp_pre) g |}).
    Defined.

    (* Hoare triple for a function.
     *)
    Definition SFunction (ret : type) (targs : list type)
               (PQ : arrowFrom val targs WithPrePost)
    : function_spec' :=
      {| fs'_return := ret
       ; fs'_arguments := targs
       ; fs'_specification := arrowFrom_map
            (fun wpp (Q : val -> mpred) =>
               Exists g : wpp.(wpp_with),
                          (Forall res : val, wpp.(wpp_post) g res -* Q res) **
                          wpp.(wpp_pre) g) PQ |}.

    (* Hoare triple for a constructor.
     *)
    Definition SConstructor (class : globname)
               (targs : list type)
               (PQ : val -> arrowFrom val targs WithPrePost)
    : function_spec' :=
      let this_type := Qmut (Tref class) in
      SFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
          (fun this => arrowFrom_map (fun wpp =>
             {| wpp_with := wpp.(wpp_with)
              ; wpp_pre  := fun m =>
                  uninitialized_ty this_type this ** wpp.(wpp_pre) m
              ; wpp_post := wpp.(wpp_post)
              |}) (PQ this)).

    (* Hoare triple for a destructor.
     *)
    Definition SDestructor (class : globname)
               (PQ : val -> WithPrePost)
    : function_spec' :=
      let this_type := Qmut (Tref class) in
      SFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
          (fun this =>
             {| wpp_with := (PQ this).(wpp_with)
              ; wpp_pre := (PQ this).(wpp_pre)
              ; wpp_post := fun m res =>
                  uninitialized_ty this_type this ** (PQ this).(wpp_post) m res
              |}).

    (* Hoare triple for a method.
     *)
    Definition SMethod (class : globname) (qual : type_qualifiers)
               (ret : type) (targs : list type)
               (PQ : val -> arrowFrom val targs WithPrePost)
    : function_spec' :=
      let class_type := Tref class in
      let this_type := Tqualified qual class_type in
      SFunction ret (Qconst (Tpointer this_type) :: targs) PQ.
      (* ^ todo(gmm): this looks wrong. something isn't going
       * to fit together with respect to calling conventions and
       * specifications.
       *)




    Lemma cptr_cptr' : forall p fs fs',
        fs.(fs_arguments) = fs'.(fs'_arguments) ->
        fs.(fs_return) = fs'.(fs'_return) ->
        (forall Q vs,
            fs.(fs_specification) vs Q -|- applyEach fs'.(fs'_arguments) vs fs'.(fs'_specification) (fun k _ => k Q)) ->
        cptr p fs -|- cptr' p fs'.
    Proof.
      unfold cptr. intros.
      destruct fs, fs'. simpl in *. subst.
      setoid_rewrite H1; clear H1.
      unfold cptr'.
      rewrite <- forallEach_primes. reflexivity.
    Qed.



    Theorem triple_sound : forall p r ts PQ vs,
        List.length vs = List.length ts ->
        forall g : (PQ vs).(wpp_with),
          cptr p (ht r ts PQ) ** (PQ vs).(wpp_pre) g
          |-- fspec p vs ((PQ vs).(wpp_post) g).
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
      discharge ltac:(canceler fail auto) auto.
    Qed.

    Theorem triple_apply : forall p r ts F F' vs (PQ : list val -> WithPrePost) K,
        List.length vs = List.length ts -> (* trivial *)
        forall g : (PQ vs).(wpp_with), (* existential quantifier *)
          F |-- (PQ vs).(wpp_pre) g ** F' -> (* pre-condition *)
          (forall r, (PQ vs).(wpp_post) g r |-- K r) ->
          cptr p (ht r ts PQ) ** F |-- fspec p vs K ** F'.
    Proof.
      intros.
      specialize (triple_sound p r ts PQ vs H).
      unfold ht in *.
      rewrite H0 in *; clear H0.
      intros.
      specialize (H0 g).
      rewrite <- sepSPA.
      rewrite H0.
      discharge ltac:(canceler fail auto) auto.
      eapply fspec_conseq. assumption.
    Qed.

    Theorem triple'_apply
    : forall p r ts F F' vs (PQ : arrowFrom val ts WithPrePost) K,
        List.length vs = List.length ts ->
        F |-- applyEach ts vs PQ (fun wpp _ =>
                 Exists g : wpp.(wpp_with),
                 wpp.(wpp_pre) g **
                 (Forall r, wpp.(wpp_post) g r -* K r)) ** F' ->
        cptr' p (SFunction r ts PQ) ** F |-- fspec p vs K ** F'.
    Proof.
      intros.
      rewrite <- cptr_cptr'.
      instantiate (1:=
        {| fs_return := r
         ; fs_arguments := ts
         ; fs_specification := fun vs0 Q =>
              applyEach ts vs0 (SFunction r ts PQ).(fs'_specification)
              (fun (k : (val -> mpred) -> mpred) _ => k Q) |}).
      2,3,4: reflexivity.
      unfold cptr. simpl.
      eapply sepSPAdj.
      eapply (lforallL vs).
      eapply wandSP_only_provableL; eauto.
      eapply (lforallL K).
      eapply wandSPAdj.
      eapply wandSP_cancel.
      rewrite H0; clear H0.
      discharge ltac:(canceler fail auto) auto.
      clear.
      revert vs. induction ts; destruct vs; simpl; try reflexivity.
      { discharge ltac:(canceler fail auto) auto. }
      { rewrite IHts. discharge ltac:(canceler fail auto) auto. }
    Qed.

    Section with_resolver.
      Context {resolve : genv}.


    Fixpoint bind_type (t : type) (x : ident) (v : val) : mpred :=
      match t with
      | Tqualified _ t => bind_type t x v
      | Treference ref => addr_of x v
      | _ => tlocal t x v
      end.

(*
    Definition func_ok (ret : type) (params : list (ident * type))
               (body : Stmt)
               (spec : function_spec)
    : mpred :=
      [| ret = spec.(fs_return) |] **
      [| List.map snd params = spec.(fs_arguments) |] **
      Forall args, Forall Q : val -> mpred,
        (* this is what is created from the parameters *)
        let binds := sepSPs (zip (fun '(x, t) 'v => tlocal t x v) params args) in
        (* this is what is freed on return *)
        let frees := sepSPs (map (fun '(x, t) => Exists v, tlocal t x v) params) in
        (binds ** spec.(fs_specification) args Q) -* (wp resolve body (Kfree frees (val_return Q))).
*)

    (* the proof obligation for a function
     *)
    Definition func_ok' (ret : type) (params : list (ident * type))
               (body : Stmt)
               (spec : function_spec')
    : mpred :=
      [| ret = spec.(fs'_return) |] **
      [| spec.(fs'_arguments) = List.map snd params |] **
      ForallEach' _ spec.(fs'_specification) (fun PQ args =>
        let vals := List.map snd args in

        (* this is what is created from the parameters *)
        let binds := sepSPs (zip (fun '(x, t) 'v => bind_type t x v) params vals) in
        (* this is what is freed on return *)
        let frees := sepSPs (map (fun '(x, t) => Exists v, bind_type t x v) params) in
        if is_void ret
        then
          Forall Q : mpred,
          (binds ** PQ (fun _ => Q)) -* (wp resolve body (Kfree frees (void_return Q)))
        else
          Forall Q : val -> mpred,
          (binds ** PQ Q) -* (wp resolve body (Kfree frees (val_return Q)))).

    Definition method_ok' (resolve : genv)
               (meth : Method) (spec : function_spec')
      : mpred :=
      match meth.(m_body) with
      | None => lfalse
      | Some body =>
        let this_type :=
            Qconst (Tpointer (Tqualified meth.(m_this_qual) (Tref meth.(m_class))))
        in
        [| spec.(fs'_return) = meth.(m_return) |] **
        [| spec.(fs'_arguments) = this_type :: List.map snd meth.(m_params) |] **
        ForallEach' _ spec.(fs'_specification) (fun PQ args =>
          let vals := List.map snd args in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds :=
                addr_of "#this" this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type t x v) meth.(m_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                addr_of "#this" this_val **
                sepSPs (map (fun '(x, t) => Exists v, bind_type t x v) meth.(m_params))
            in
            if is_void meth.(m_return)
            then
              Forall Q : mpred,
              (binds ** PQ (fun _ => Q)) -* (wp resolve body (Kfree frees (void_return Q)))
            else
              Forall Q : val -> mpred,
              (binds ** PQ Q) -* (wp resolve body (Kfree frees (val_return Q)))
          end)
      end.


    (* todo(gmm): should the `uninitialized` be part of the this, rather than
     * part of the specification?
     *)
    Definition ctor_ok' (resolve : genv)
               (ctor : Ctor) (spec : function_spec')
      : mpred :=
      match ctor.(c_body) with
      | None => lfalse
      | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
      | Some (UserDefined (init, body)) =>
        let this_type :=
            Qconst (Tpointer (Qmut (Tref ctor.(c_class))))
        in
        [| spec.(fs'_return) = Qmut Tvoid |] **
        [| spec.(fs'_arguments) = this_type :: List.map snd ctor.(c_params) |] **
        ForallEach' _ spec.(fs'_specification) (fun PQ args =>
          let vals := List.map snd args in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds :=
                addr_of "#this" this_val **
                sepSPs (zip (fun '(x, t) 'v => bind_type t x v) ctor.(c_params) rest_vals)
            in
            (* this is what is freed on return *)
            let frees :=
                addr_of "#this" this_val **
                sepSPs (map (fun '(x, t) => Exists v, bind_type t x v) ctor.(c_params))
            in
            Forall Q : mpred,
            (binds ** PQ (fun _ => Q)) -*
            (wpis (resolve:=resolve) ctor.(c_class) this_val init (wp resolve body (Kfree frees (void_return Q))))
          end)
      end.


    (* todo(gmm): should the `uninitialized` be part of the this, rather than
     * part of the specification?
     *)
    Definition dtor_ok' (resolve : genv)
               (dtor : Dtor) (spec : function_spec')
      : mpred :=
      match dtor.(d_body) with
      | None => lfalse
      | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
      | Some (UserDefined (body, deinit)) =>
        let this_type :=
            Qconst (Tpointer (Qmut (Tref dtor.(d_class))))
        in
        [| spec.(fs'_return) = Qmut Tvoid |] **
        [| spec.(fs'_arguments) = this_type :: nil |] **
        ForallEach' _ spec.(fs'_specification) (fun PQ args =>
          let vals := List.map snd args in
          match vals with
          | nil => lfalse
          | this_val :: rest_vals =>
            (* this is what is created from the parameters *)
            let binds := addr_of "#this" this_val in
            (* this is what is freed on return *)
            let frees := addr_of "#this" this_val in
            Forall Q : mpred,
           (binds ** PQ (fun _ => Q)) -*
           (wp resolve body (Kfree frees (void_return (wpds (resolve:=resolve) dtor.(d_class) this_val deinit Q))))
          end)
      end.

    Definition cglob' (gn : globname) (spec : function_spec')
    : mpred :=
      Exists a, [| glob_addr resolve gn a |] ** cptr' (Vptr a) spec.

    Axiom cglob'_dup : forall p fs,
        cglob' p fs -|- cglob' p fs ** cglob' p fs.
    (* i was thinking that i could store static variables in invariants.
     * i'm not sure how this works with function pointer weakening.
     *)
    Axiom cglob'_weaken : forall a b, cglob' a b |-- empSP.

    Axiom wpe_frame : forall resolve m e k F,
        wpe m resolve e k ** F -|- wpe m resolve e (fun x => k x ** F).

(*
    Axiom Proper_wpe_equiv
    : Proper (eq ==> eq ==> eq ==> pointwise_relation _ lequiv ==> lequiv) wpe.
    Axiom Proper_wpe_entails
    : Proper (eq ==> eq ==> eq ==> pointwise_relation _ lentails ==> lentails) wpe.


    Lemma wps_frame : forall es k F,
        wps es k ** F -|- wps es (fun x => k x ** F).
    Proof.
      induction es; simpl; intros.
      { reflexivity. }
      { unfold wp_rhs. rewrite wpe_frame.
        eapply Proper_wpe_equiv; eauto.
        red. intros. rewrite IHes. reflexivity. }
    Qed.

    Lemma Proper_wps_entails
    : Proper (eq ==> pointwise_relation _ lentails ==> lentails)
             wps.
    Proof.
      do 3 red. intros. subst.
      generalize dependent x0; revert y0.
      induction y; simpl; intros.
      { eapply H0. }
      { simpl. eapply Proper_wpe_entails; eauto.
        red. intros.
        eapply IHy. red.
        eauto. }
    Qed.
*)
    Theorem wp_call_glob : forall f ret ts es K PQ F F' ty ty' ty'',
        F (* ** cglob' f ret ts (ht' ret ts PQ) *)
        |-- wps (wp_rhs (resolve:=resolve)) es (fun vs => applyEach ts vs PQ (fun wpp _ =>
                Exists g : wpp.(wpp_with),
                  wpp.(wpp_pre) g ** F' **
                  (Forall r, wpp.(wpp_post) g r -* K r))) ->
        (|> cglob' f (SFunction ret ts PQ)) ** F
        |-- wp_rhs (resolve:=resolve)
                   (Ecall (Ecast Cfunction2pointer (Evar (Gname f) ty) ty') es ty'')
                   K ** F'.
    Proof.
(*
      intros.
      rewrite H; clear H.
      rewrite <- wp_call.
      rewrite <- wp_rhs_cast_function2pointer.
      simplify_wp.
      unfold cglob'.
      discharge ltac:(canceler fail eauto) eauto.
      rewrite wps_frame.
      rewrite sepSPC.
      rewrite wps_frame.
      eapply Proper_wps_entails; eauto.
      red. intros.
      rewrite sepSPC.
      etransitivity.
      eapply triple'_apply with (vs:=a).
      reflexivity.
      discharge auto.
      eapply spec_later_weaken.
*)
    Admitted.

(*
    Ltac simplifying :=
      repeat first [ progress simplify_wp
                   | progress simpl wps
                   | rewrite <- wp_seq; simpl wp_block; simpl wp_decls
                   | rewrite <- wp_return_val
                   | rewrite <- wp_return_void
                   | rewrite <- wp_if
                   | rewrite <- wp_continue
                   | rewrite <- wp_break
                   | rewrite <- wp_rhs_binop
                   | rewrite <- wp_rhs_cast_function2pointer
                   ].
*)

    Definition A__bar := "_Z1A3bar".


(*
    Goal |> cglob' A__bar
         (ht' T_int32 (T_int32 :: nil)
              (fun x => {| wpp_with := _
                       ; wpp_pre v := [| x = Vint v |]
                       ; wpp_post v res := [| res = Vint (Z.add v 1) |] |}))
         |--
         func_ok' (Qmut T_int32)
         (("x",(Qmut T_int32)) :: nil)
         (Sseq (
              (Sreturn (Some
                          (Ebinop Badd
                                  (Ecall
                                     (Ecast Cfunction2pointer
                                            (Evar
                                               (Gname A__bar))) (
                                       (Ebinop Badd
                                               (Ecast Cl2r
                                                      (Evar
                                                         (Lname  "x")))
                                               (Eint 5
                                                     (Qmut T_int))) :: nil))
                                  (Eint 1
                                        (Qmut T_int))))) :: nil))
         (ht' (Qmut T_int32) (Qmut T_int32 :: nil) (fun x =>
              {| wpp_with := Z
               ; wpp_pre v := [| x = Vint v |] ** [| -100 < v < 100 |]%Z
               ; wpp_post v res := [| res = Vint (Z.add v 7) |] |})).
    Proof.
      Opaque cglob' ht'.
      unfold func_ok'. simpl.
      Transparent ht'.
      simpl. Opaque ht'.
      simpl.
      t. subst.
      simplifying.
      repeat perm_left ltac:(idtac; perm_right ltac:(eapply wp_call_glob)).
      simplifying.
      unfold tlocal, tptsto.
      t.
      simplify_wps. t.
      simplify_wps.
      t.
    Qed.
*)

  End with_resolver.

End Func.

Declare Module F : Func.

Export F.
