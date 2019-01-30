From Coq.Classes Require Import
     RelationClasses Morphisms.

Require Import Coq.Lists.List.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Ast Parser.
Import Cpp.Parser.
Require Import  Cpp.Sem.Util.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

From auto.Tactics Require Import Discharge.

Module Type logic.

  Parameter mpred : Type.

  Parameter ILogicOps_mpred : ILogicOps mpred.
  Global Existing Instance ILogicOps_mpred.
  Parameter ILogic_mpred : ILogic mpred.
  Global Existing Instance ILogic_mpred.

  Parameter BILogicOps_mpred : BILogicOps mpred.
  Global Existing Instance BILogicOps_mpred.
  Parameter BILogic_mpred : BILogic mpred.
  Global Existing Instance BILogic_mpred.

  Parameter EmbedOp_Prop_mpred : EmbedOp Prop mpred.
  Global Existing Instance EmbedOp_Prop_mpred.
  Parameter Embed_Prop_mpred : Embed Prop mpred.
  Global Existing Instance Embed_Prop_mpred.

  Parameter ILLOperators_mpred : ILLOperators mpred.
  Global Existing Instance ILLOperators_mpred.
  Parameter ILLater_mpred : ILLater mpred.
  Global Existing Instance ILLater_mpred.

  (** the semantics, axiomatically *)
  Parameter ptr : Type.
  Parameter val : Type.
  Parameter Vptr : ptr -> val.
  Parameter Vint : Z -> val.

  Parameter eval_unop : UnOp -> type -> val -> val -> Prop.
  Parameter eval_binop : BinOp -> type -> val -> val -> val -> Prop.

  Parameter offset_ptr : val -> Z -> val.

  Parameter is_true : val -> bool.

  Parameter genv : Type.


  (** core assertions
   * note that the resource algebra contains the code memory as well as
   * the heap.
   *)
  Notation "'[|'  P  '|]'" := (only_provable P).

  (* heap points to *)
  Parameter ptsto : val -> val -> mpred.

  (* todo(gmm): this is thread local *)
  (* address of a local variable *)
  Parameter addr_of : ident -> val -> mpred.

  (* the pointer contains the code *)
  Parameter code_at : ptr -> Func -> mpred.
  (* code_at is freely duplicable *)
  Axiom code_at_dup : forall p f, code_at p f -|- code_at p f ** code_at p f.
  Axiom code_at_drop : forall p f, code_at p f |-- empSP.

  Parameter ctor_at : ptr -> Ctor -> mpred.
  Parameter dtor_at : ptr -> Dtor -> mpred.

  (* it might be more uniform to have this be an `mpred` *)
  Parameter glob_addr : genv -> obj_name -> ptr -> Prop.

  Parameter offset_of : forall {c : genv} (t : type) (f : ident) (e : Z), Prop.

  Parameter size_of : forall {c : genv} (t : type) (e : N), Prop.

  Parameter align_of : forall {c : genv} (t : type) (e : N), Prop.

  Parameter with_genv : (genv -> mpred) -> mpred.
  Axiom with_genv_single : forall f g,
      with_genv f //\\ with_genv g -|- with_genv (fun r => f r //\\ g r).

  (* todo(gmm): maintain stack variables through regions
   *)
  Parameter has_type : val -> type -> Prop.

  Definition tptsto (ty : type) (p : val) (v : val) : mpred :=
    ptsto p v ** (embed (has_type v ty) //\\ empSP).


  Definition local (x : ident) (v : val) : mpred :=
    Exists a, addr_of x a ** ptsto a v.
  Definition tlocal (ty : type) (x : ident) (v : val) : mpred :=
    Exists a, addr_of x a ** tptsto ty a v.


  (* this is the denotation of modules *)
  Fixpoint sepSPs (ls : list mpred) : mpred :=
    match ls with
    | nil => empSP
    | l :: ls => l ** sepSPs ls
    end.

  (* note(gmm): two ways to support initializer lists.
   * 1/ add them to all functions (they are almost always empty
   * 2/ make a `ctor_at` (similar to `code_at`) that handles
   *    constructors.
   * ===
   * 2 seems like the more natural way to go.
   *)

  (* note(gmm): the denotation of modules should be moved to another module.
   *)
  Fixpoint denoteDecl (d : Decl) : mpred :=
    match d with
    | Dvar n _ _ =>
      Exists a, with_genv (fun resolve => [| glob_addr resolve n a |])
    | Dtypedef gn _ => empSP
                       (* note(gmm): this is compile time, and shouldn't be a
                        * problem.
                        *)
    | Dfunction n f =>
      match f.(f_body) return mpred with
      | None =>
        Exists a, with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\
                  code_at a f
      end
    | Dmethod n m =>
      match m.(m_body) return mpred with
      | None =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\
                  code_at a {| f_return := m.(m_return)
                             ; f_params := ("#this"%string, Tqualified m.(m_this_qual) (Tref m.(m_class))) :: m.(m_params)
                             ; f_body := m.(m_body) |}
      end
    | Dconstructor n m =>
      match m.(c_body) return mpred with
      | None =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\ ctor_at a m
      end
    | Ddestructor n m =>
      match m.(d_body) return mpred with
      | None =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\ dtor_at a m
      end
    | Dstruct gn _ => empSP
      (* ^ this should record size and offset information
       *)
    | Denum gn _ _ => empSP
      (* ^ this should record enumeration information
       *)
    | Dnamespace ds =>
      sepSPs (map denoteDecl ds)
    | Dextern ds =>
      sepSPs (map denoteDecl ds)
    end.

  Fixpoint denoteModule (d : list Decl) : mpred :=
    match d with
    | nil => empSP
    | d :: ds => denoteDecl d ** denoteModule ds
    end.


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

  (** Weakest pre-condition for expressions
   *)
  Variant mode : Set := Lvalue | Rvalue.

  (* todo(gmm): `wpe` should be indexed by types
   * question(gmm): are lvalues just references? or is there something
   * else to it?
   *)
  Parameter wpe
  : forall (resolve : genv), mode -> Expr -> (val -> mpred) -> mpred.

  (* note(gmm): the handling variables wrt lvalue and rvalues isn't correct
   * right now.
   *
   * primitives, e.g. int, int*:
   *    local x val ~ (Ex a, addr_of x a ** ptsto a val)
   * references, int&:
   *    ref x a'     ~ (Ex a, addr_of x a ** ptsto a a')
   *    (references are modeled as pointers)
   *    -- if this is true, then i can simplify things a little bit.
   * structures, T:
   *    local x (Inv y)
   *)


  (* the biggest question in these semantics is how types fit into things.
   * > C semantics doesn't use a lot of implicit casts.
   *)
  Section with_resolver.
    Context {resolve : genv}.

    Definition wp_rhs : Expr -> (val -> mpred) -> mpred :=
      wpe resolve Rvalue.
    Definition wp_lhs : Expr -> (val -> mpred) -> mpred :=
      wpe resolve Lvalue.

    Fixpoint wps (es : list Expr) (Q : list val -> mpred) : mpred :=
      match es with
      | nil => Q nil
      | e :: es => wp_rhs e (fun v => wps es (fun vs => Q (cons v vs)))
      end.


    Axiom wp_rhs_int : forall n ty Q,
        embed (has_type (Vint n) ty) //\\ Q (Vint n)
        |-- wp_rhs (Eint n ty) Q.

    Axiom wp_rhs_bool : forall (b : bool) Q,
        (if b
         then Q (Vint 1)
         else Q (Vint 0))
        |-- wp_rhs (Ebool b) Q.

    (* todo(gmm): what about the type? *)
    Axiom wp_rhs_this : forall Q,
      Exists a, (addr_of "#this"%string a ** ltrue) //\\ Q a
      |-- wp_rhs Ethis Q.

    Axiom wp_lhs_lvar : forall x Q,
      Exists a, (addr_of x a ** ltrue) //\\ Q a
      |-- wp_lhs (Evar (Lname x)) Q.

    (* what about the type? if it exists *)
    Axiom wp_lhs_gvar : forall x Q,
      Exists a, [| glob_addr resolve x a |] ** Q (Vptr a)
      |-- wp_lhs (Evar (Gname x)) Q.

    Axiom wp_lhs_member : forall e f Q,
      wp_rhs e (fun base =>
         Exists offset,
                [| @offset_of resolve (Tref f.(f_type)) f.(f_name) offset |]
           ** Q (offset_ptr base offset))
      |-- wp_lhs (Emember e f) Q.

    (* y = *x; *)
    Axiom wp_rhs_deref : forall e ty Q,
        wp_rhs e (fun a => Exists v, (tptsto ty a v ** ltrue) -* Q v)
        |-- wp_rhs (Ederef e) Q.

    (* *x = 3; *)
    Axiom wp_lhs_deref : forall e (Q : val -> mpred),
        wp_rhs e Q
        |-- wp_lhs (Ederef e) Q.

    Axiom wp_rhs_addrof : forall e Q,
        wp_lhs e Q
        |-- wp_rhs (Eaddrof e) Q.

    Axiom wp_rhs_unop : forall o e ty Q,
        wp_rhs e (fun v => Exists v', embed (eval_unop o ty v v') //\\ Q v')
        |-- wp_rhs (Eunop o e) Q.

    Axiom wp_rhs_binop : forall o e1 e2 ty Q,
        wp_rhs e1 (fun v1 => wp_rhs e2 (fun v2 =>
            Exists v', embed (eval_binop o ty v1 v2 v') //\\ Q v'))
        |-- wp_rhs (Ebinop o e1 e2) Q.

    Axiom wp_rhs_cast_l2r : forall e Q,
        wp_lhs e (fun a => Exists v, (ptsto a v ** ltrue) //\\ Q v)
        |-- wp_rhs (Ecast Cl2r e) Q.

    Axiom wp_rhs_cast_noop : forall m e Q,
        wpe resolve m e Q
        |-- wpe resolve m (Ecast Cnoop e) Q.

    Axiom wp_rhs_cast_int2bool : forall m e Q,
        wpe resolve m e Q
        |-- wpe resolve m (Ecast Cint2bool e) Q.

    Axiom wp_rhs_seqand : forall e1 e2 Q,
        wp_rhs e1 (fun v1 =>
           if is_true v1
           then wp_rhs e2 (fun v2 =>
                                     if is_true v2
                                     then Q (Vint 1)
                                     else Q (Vint 0))
           else Q (Vint 0))
        |-- wp_rhs (Eseqand e1 e2) Q.

    Axiom wp_rhs_seqor : forall e1 e2 Q,
        wp_rhs e1 (fun v1 =>
           if is_true v1
           then Q (Vint 1)
           else wp_rhs e2 (fun v2 =>
                                     if is_true v2
                                     then Q (Vint 1)
                                     else Q (Vint 0)))
        |-- wp_rhs (Eseqor e1 e2) Q.

    Axiom wpe_comma : forall {m} e1 e2 Q,
        wpe resolve m e1 (fun _ => wpe resolve m e2 Q)
        |-- wpe resolve m (Ecomma e1 e2) Q.

    Axiom wp_rhs_condition : forall m tst th el Q,
        wp_rhs tst (fun v1 =>
           if is_true v1
           then wpe resolve m th Q
           else wpe resolve m el Q)
        |-- wpe resolve m (Eif tst th el) Q.

    Axiom wp_rhs_sizeof : forall ty Q,
        Exists sz, [| @size_of resolve ty sz |] ** Q (Vint (Z.of_N sz))
        |-- wp_rhs (Esize_of (inl ty)) Q.

    Axiom wp_lhs_assign : forall l r Q,
        wp_lhs l (fun la => wp_rhs r (fun rv =>
           (Exists v, ptsto la v) ** (ptsto la rv -* Q la)))
        |-- wp_lhs (Eassign l r) Q.

(*
    Axiom wp_rhs_postincr : forall inc_or_dec l ty Q,
        wp_lhs resolve l (fun a =>
          Exists v, Exists v', (tptsto ty a v ** embed _) -* tptsto ty a v' ** Q v)
        |-- wp_rhs resolve (Epostincr inc_or_dec l ty) Q.
*)

    Axiom wp_rhs_cast_function2pointer : forall g Q,
        wp_lhs (Evar (Gname g)) Q
        |-- wp_rhs (Ecast Cfunction2pointer (Evar (Gname g))) Q.

    Axiom wp_call : forall f es Q,
        wp_rhs f (fun f => wps es (fun vs => |> fspec f vs Q))
        |-- wp_rhs (Ecall f es) Q.

    Axiom wp_member_call : forall f obj es Q,
        Exists fa, [| glob_addr resolve f fa |] **
        wp_rhs obj (fun this => wps es (fun vs =>
            |> fspec (Vptr fa) (this :: vs) Q))
        |-- wp_rhs (Emember_call false f obj es) Q.

    Local Open Scope string_scope.

    Ltac simplify_wp :=
      repeat first [ rewrite <- wp_lhs_assign
                   | rewrite <- wp_lhs_lvar
                   | rewrite <- wp_lhs_gvar
                   | rewrite <- wp_rhs_int
                   | rewrite <- wp_lhs_deref
                   | rewrite <- wp_rhs_addrof
                   | rewrite <- wp_rhs_cast_l2r
                   ].

    Coercion Vint : Z >-> val.
    Coercion Z.of_N : N >-> Z.
    Definition El2r := Ecast Cl2r.

    Parameter has_type_int : forall z,
        (-Z.pow 2 31 < z < Z.pow 2 31 - 1)%Z ->
        has_type z T_int.
    Parameter has_type_int32 : forall z,
        (-Z.pow 2 31 < z < Z.pow 2 31 - 1)%Z ->
        has_type z T_int32.
    Parameter has_type_qual : forall v q ty,
        has_type v ty -> has_type v (Tqualified q ty).

    Lemma eval_add : forall ty (a b c : Z),
        c = (Z.add a b) ->
        has_type (Vint c) ty ->
        eval_binop Badd ty (Vint a) (Vint b) (Vint c).
    Proof using.
      clear.
    Admitted.

    Ltac has_type :=
      first [ eapply has_type_int ; lia
            | eapply has_type_int32 ; lia
            | eapply has_type_qual ; has_type ].

    Ltac operator :=
      first [ subst ; eapply eval_add; [ first [ reflexivity | nia ] | has_type ] ].

    Ltac t :=
      let tac := try match goal with
            | |- @eq val _ _ => try f_equal
            end ;
        try solve [ eauto | reflexivity | has_type | operator | lia ] in
      discharge ltac:(canceler fail tac) tac.

    Parameter _x : ident.
    Parameter _y : ident.

    (* int x ; x = 0 ; *)
    Goal (tlocal T_int32 _x 3
         |-- wp_lhs (Eassign (Evar (Lname _x)) (Eint 0 T_int32)) (fun xa => addr_of _x xa ** tptsto T_int32 xa 0))%Z.
    Proof.
      unfold tlocal.
      repeat (t; simplify_wp).
      unfold tptsto.
      t.
    Qed.

    Definition local_at (l : ident) (a : val) (v : val) : mpred :=
      addr_of l a ** ptsto a v.

    (* int *x ; *x = 0 ; *)
    Goal local "x" 3%Z ** ptsto 3%Z 12%Z
         |-- wp_lhs
             (Eassign (Ederef (Ecast Cl2r (Evar (Lname "x")))) (Eint 0 T_int32))
             (fun x => embed (x = 3)%Z //\\ local "x" x ** ptsto x 0%Z).
    Proof.
      intros.
      unfold local, local_at.
      repeat (t; simplify_wp).
    Qed.

    (* int *x ; int y ; x = &y ; *)
    Goal local _x 3%Z ** local _y 12%Z
         |-- wp_lhs (Eassign (Evar (Lname _x)) (Eaddrof (Evar (Lname _y))))
         (fun xa => addr_of _x xa ** Exists ya, addr_of _y ya ** ptsto xa ya ** ptsto ya 12)%Z.
    Proof.
      unfold local.
      repeat (t; simplify_wp).
    Qed.

    (* int *x ; int y ; *(x = &y) = 3; *)
    Goal local _x 3%Z ** local _y 9%Z
      |-- wp_lhs (Eassign (Ederef (El2r (Eassign (Evar (Lname _x)) (Eaddrof (Evar (Lname _y)))))) (Eint 3 T_int32))%Z (fun ya => local _x ya ** ptsto ya 3%Z ** addr_of _y ya).
    Proof.
      unfold local.
      repeat (t; simplify_wp).
    Qed.

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


    (** statements *)
    Record Kpreds :=
    { k_normal : mpred
    ; k_return : option val -> mpred
    ; k_break  : mpred
    ; k_continue : mpred
    }.

    Definition void_return (P : mpred) : Kpreds :=
      {| k_normal := P
       ; k_return := fun r => match r with
                           | None => P
                           | Some _ => lfalse
                           end
       ; k_break := lfalse
       ; k_continue := lfalse
      |}.

    Definition val_return (P : val -> mpred) : Kpreds :=
      {| k_normal := lfalse
       ; k_return := fun r => match r with
                           | None => lfalse
                           | Some v => P v
                           end
       ; k_break := lfalse
       ; k_continue := lfalse
      |}.

    Definition Kseq_all (Q : mpred -> mpred) (k : Kpreds) : Kpreds :=
      {| k_normal   := Q k.(k_normal)
       ; k_return v := Q (k.(k_return) v)
       ; k_break    := Q k.(k_break)
       ; k_continue := Q k.(k_continue)
       |}.
    Definition Kfree (a : mpred) : Kpreds -> Kpreds :=
      Kseq_all (fun P => a ** P).


    (** weakest pre-condition for statements
     *)

    Parameter wp
    : forall (resolve : genv), Stmt -> Kpreds -> mpred.

    Axiom wp_skip : forall Q, Q.(k_normal) |-- wp resolve Sskip Q.

    Axiom wp_seq_nil : forall Q,
        Q.(k_normal) |-- wp resolve (Sseq nil) Q.

    Axiom wp_seq_cons : forall c cs Q,
        wp resolve c {| k_normal   := wp resolve (Sseq cs) Q
                      ; k_break    := Q.(k_break)
                      ; k_continue := Q.(k_continue)
                      ; k_return v := Q.(k_return) v |}
        |-- wp resolve (Sseq (c :: cs)) Q.


    Axiom wp_return_void : forall Q,
        Q.(k_return) None |-- wp resolve (Sreturn None) Q.
    Axiom wp_return_val : forall e Q,
        wp_rhs e (fun res => Q.(k_return) (Some res))
        |-- wp resolve (Sreturn (Some e)) Q.

    Axiom wp_break : forall Q,
        Q.(k_break) |-- wp resolve Sbreak Q.
    Axiom wp_continue : forall Q,
        Q.(k_continue) |-- wp resolve Scontinue Q.

    Axiom wp_do : forall e Q,
        wp_rhs e (fun _ => Q.(k_normal))
        |-- wp resolve (Sexpr e) Q.

    Axiom wp_if : forall e thn els Q,
        wp_rhs e (fun v =>
                    if is_true v then
                      wp resolve els Q
                    else
                      wp resolve thn Q)
        |-- wp resolve (Sif None e thn els) Q.

    (* note(gmm): this rule is not sound for a total hoare logic
     *)
    Axiom wp_while : forall t b Q,
        Exists I,
            (wp resolve (Sif None t (Sseq (b :: Scontinue :: nil)) Sskip)
                {| k_break    := Q.(k_normal)
                 ; k_continue := I
                 ; k_return v := Q.(k_return) v
                 ; k_normal   := Q.(k_normal) |})
        |-- wp resolve (Swhile t b) Q.

    (* note(gmm): this definition is crucial to everything going on.
     * 1. look at the type.
     *    > reference: if a is the lvalue of the rhs
     *      local x a
     *    > primitive: if v is the rvalue of the rhs
     *      local x v
     *    > class: allocate, initialize, bind name
     *      exists a, uninitialized (size_of t) a -*
     *        addr_of x a ** ctor(a, args...)
     *)
    Fixpoint wp_decl (x : ident) (ty : type) (init : option Expr)
               (k : Kpreds -> mpred) (Q : Kpreds)
    : mpred :=
      match ty with
      | Treference t =>
        match init with
        | None => lfalse
          (* ^ references must be initialized *)
        | Some init =>
          (* i should use the type here *)
          wp_lhs init (fun a => addr_of x a -* k (Kfree (addr_of x a) Q))
        end
      | Tfunction _ _ =>
        (* inline functions are not supported *)
        lfalse
      | Tvoid
      | Tunknown
      | Ttemplate _ => lfalse
      | Tqualified q ty =>
        wp_decl x ty init k Q
      | Tpointer _
      | Tbool
      | Tchar _ _
      | Tint _ _ =>
        match init with
        | None =>
          Exists v, tlocal ty x v -* k (Kfree (Exists v', tlocal ty x v') Q)
        | Some init =>
          wp_rhs init (fun v => tlocal ty x v -* k (Kfree (Exists v', tlocal ty x v') Q))
        end
      | Tarray _ _ => lfalse (* todo(gmm): arrays not yet supported *)
      | Tref gn =>
        match init with
        | Some (Econstructor cnd es) =>
          Exists sz, [| @size_of resolve (Tref gn) sz |] **
          Exists ctor, [| glob_addr resolve cnd ctor |] **
          (* we don't need the destructor until later, but if we prove it
           * early, then we don't need to resolve it over multiple paths.
           *)
          Exists dtor, [| glob_addr resolve (gn ++ "D1") dtor |] **
          wps es (fun vs =>
                 Exists a, uninitialized_ty (Tref gn) a
              -* |> fspec (Vptr ctor) (a :: vs) (fun _ =>
                 addr_of x a -*
                 k (Kseq_all (fun Q => |> fspec (Vptr dtor) (a :: nil)
                                   (fun _ => addr_of x a ** uninitialized_ty (Tref gn) a ** Q)) Q)))
        | _ => lfalse
          (* ^ all non-primitive declarations must have initializers *)
        end
      end.

    Axiom wp_decl_nil : forall Q, Q.(k_normal) |-- wp resolve (Sdecl nil) Q.

    Axiom wp_decl_cons : forall x ty init ds Q,
        wp_decl x ty init (wp resolve (Sdecl ds)) Q
        |-- wp resolve (Sdecl ((x,ty,init) :: ds)) Q.

    Import Cpp.Parser.
    Import ListNotations.

    Ltac simplify_wps :=
      repeat first [ progress simplify_wp
                   | progress simpl wps
                   | rewrite <- wp_skip
                   | rewrite <- wp_seq_nil
                   | rewrite <- wp_seq_cons
                   | rewrite <- wp_decl_nil
                   | rewrite <- wp_decl_cons
                   | rewrite <- wp_return_val
                   | rewrite <- wp_return_void
                   | rewrite <- wp_if
                   | rewrite <- wp_continue
                   | rewrite <- wp_break
                   | rewrite <- wp_rhs_binop
                   | rewrite <- wp_call
                   | rewrite <- wp_rhs_cast_function2pointer
                   ].

(*
    { P } - { Q } = [] (P -* wp code Q)
*)


    Record function_spec' : Type :=
    { fs'_return : type
    ; fs'_arguments : list type
    ; fs'_specification : arrowFrom val fs'_arguments ((val -> mpred) -> mpred)
    }.

    Record function_spec : Type :=
    { fs_return : type
    ; fs_arguments : list type
    ; fs_specification : list val -> (val -> mpred) -> mpred
    }.

    Definition cptr' (p : val) (fs : function_spec') : mpred.
    refine (ForallEach _ fs.(fs'_specification) (fun PQ args =>
              Forall Q, PQ Q -* fspec p (List.map snd args) Q)).
    Defined.

    Axiom cptr'_dup : forall p fs, cptr' p fs -|- cptr' p fs ** cptr' p fs.

    Definition cptr (p : val) (PQ : function_spec) : mpred.
      refine (
          Forall vs,
          [| List.length vs = List.length PQ.(fs_arguments) |] -*
          Forall Q, PQ.(fs_specification) vs Q -* fspec p vs Q).
    Defined.

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

    Definition ht' (ret : type) (targs : list type)
               (PQ : arrowFrom val targs WithPrePost)
      : function_spec'.
    refine {| fs'_return := ret
            ; fs'_arguments := targs
            ; fs'_specification := _ |}.
      induction targs.
      { simpl in *.
        refine (fun Q =>
                  Exists g : PQ.(wpp_with),
                             (Forall res, PQ.(wpp_post) g res -* Q res)
                               ** PQ.(wpp_pre) g). }
      { simpl in *.
        refine (fun x => IHtargs (PQ x)). }
    Defined.



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
        F |-- applyEach ts vs PQ (fun wpp _ =>
                 Exists g : wpp.(wpp_with),
                 wpp.(wpp_pre) g ** F' **
                 (Forall r, wpp.(wpp_post) g r -* K r)) ->
        cptr' p (ht' r ts PQ) ** F |-- fspec p vs K ** F'.
    Proof.
      intros.
      rewrite <- cptr_cptr'.
      instantiate (1:= {| fs_return := r
                         ; fs_arguments := ts
                         ; fs_specification := fun vs0 Q => applyEach ts vs0 (ht' r ts PQ).(fs'_specification)
                                            (fun (k : (val -> mpred) -> mpred) (_ : list (type * val)) => k Q) |}).
      2: intros; reflexivity.
    Admitted.

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

    Fixpoint ForallEach' {t u T} (ls : list t)
    : forall (v : arrowFrom u ls T)
        (P : T ->  list (t * u) -> mpred), mpred :=
      match ls with
      | nil => fun v P => P v nil
      | l :: ls => fun v P => Forall x,
                            ForallEach' ls (v x) (fun z xs => P z (cons (l, x) xs))
      end.

    Definition func_ok' (ret : type) (params : list (ident * type))
               (body : Stmt)
               (spec : function_spec')
    : mpred.
    refine (
      [| ret = spec.(fs'_return) |] **
      [| spec.(fs'_arguments) = List.map snd params |] **
      ForallEach' _ spec.(fs'_specification) (fun PQ args =>
        let vals := List.map snd args in

        (* this is what is created from the parameters *)
        let binds := sepSPs (zip (fun '(x, t) 'v => tlocal t x v) params vals) in
        (* this is what is freed on return *)
        let frees := sepSPs (map (fun '(x, t) => Exists v, tlocal t x v) params) in
        Forall Q : val -> mpred,
        (binds ** PQ Q) -* (wp resolve body (Kfree frees (val_return Q))))
      ).
    Defined.


    Definition method_ok' (ret : type)
               (this_type : type)
               (params : list (ident * type))
               (body : Stmt)
               (spec : function_spec')
    : mpred.
    refine (
      [| spec.(fs'_return) = ret |] **
      [| spec.(fs'_arguments) = this_type :: List.map snd params |] **
      ForallEach' _ spec.(fs'_specification) (fun PQ args =>
        let vals := List.map snd args in

        match vals with
        | nil => lfalse
        | this_val :: rest_vals =>
          (* this is what is created from the parameters *)
          let binds :=
              addr_of "#this" this_val **
              sepSPs (zip (fun '(x, t) 'v => tlocal t x v) params rest_vals) in
          (* this is what is freed on return *)
          let frees :=
              addr_of "#this" this_val **
              sepSPs (map (fun '(x, t) => Exists v, tlocal t x v) params) in
          Forall Q : val -> mpred,
          (binds ** PQ Q) -* (wp resolve body (Kfree frees (val_return Q)))
      end)
      ).
    Defined.

    Definition cglob' (gn : globname) (spec : function_spec')
    : mpred :=
      Exists a, [| glob_addr resolve gn a |] ** cptr' (Vptr a) spec.

    Axiom wpe_frame : forall resolve m e k F,
        wpe m resolve e k ** F -|- wpe m resolve e (fun x => k x ** F).

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

    Theorem wp_call_glob : forall f ret ts es K PQ F F',
        F (* ** cglob' f ret ts (ht' ret ts PQ) *)
        |-- wps es (fun vs => applyEach ts vs PQ (fun wpp _ =>
                Exists g : wpp.(wpp_with),
                  wpp.(wpp_pre) g ** F' **
                  (Forall r, wpp.(wpp_post) g r -* K r))) ->
        (|> cglob' f (ht' ret ts PQ)) ** F
        |-- wp_rhs (Ecall (Ecast Cfunction2pointer (Evar (Gname f))) es) K ** F'.
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

    Ltac simplifying :=
      repeat first [ progress simplify_wp
                   | progress simpl wps
                   | rewrite <- wp_skip
                   | rewrite <- wp_seq_nil
                   | rewrite <- wp_seq_cons
                   | rewrite <- wp_decl_nil
                   | rewrite <- wp_decl_cons
                   | rewrite <- wp_return_val
                   | rewrite <- wp_return_void
                   | rewrite <- wp_if
                   | rewrite <- wp_continue
                   | rewrite <- wp_break
                   | rewrite <- wp_rhs_binop
                   | rewrite <- wp_rhs_cast_function2pointer
                   ].

    Definition A__bar := "_Z1A3bar".


    Goal |> cglob' A__bar
         (ht' T_int32 (T_int32 :: nil)
              (fun x => {| wpp_with := _
                       ; wpp_pre v := [| x = Vint v |]
                       ; wpp_post v res := [| res = Vint (Z.add v 1) |] |}))
         |--
         func_ok' (Qmut T_int32)
         [("x",(Qmut T_int32))]
         (Sseq [
              (Sreturn (Some
                          (Ebinop Badd
                                  (Ecall
                                     (Ecast Cfunction2pointer
                                            (Evar
                                               (Gname A__bar))) [
                                       (Ebinop Badd
                                               (Ecast Cl2r
                                                      (Evar
                                                         (Lname  "x")))
                                               (Eint 5
                                                     (Qmut T_int)))])
                                  (Eint 1
                                        (Qmut T_int)))))])
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
      repeat perm_left ltac:(idtac; perm_right ltac:(eapply wp_call_glob)).        simplifying.
      unfold tlocal, tptsto.
      t.
      simplify_wps. t.
      simplify_wps.
      t.
    Qed.


    Inductive module_declares : list Decl -> obj_name -> Func -> Prop :=
    | MDfound {body nm f}
              (_ : f.(f_body) = Some body)
      : module_declares (Dfunction nm f :: nil)
                        nm
                        f
    | MDnamespace {ds nm f}
                  (_ : module_declares ds nm f)
      : module_declares (Dnamespace ds :: nil)
                        nm
                        f
    | MDskip {d ds nm f}
             (_ : module_declares ds nm f)
      : module_declares (d :: ds) nm f
    .


    Lemma verify_func : forall g s module retT params body (F : mpred),
        module_declares module g {| f_return := retT
                                  ; f_params := params
                                  ; f_body := Some body |} ->
        F (* ** denoteModule nil mod *)
        |-- func_ok' retT params body s ->
        denoteModule module ** F |-- cglob' g s.
    Proof.
      induction 1; simpl.
    Admitted.

  End with_resolver.

End logic.

Declare Module L : logic.

Export L.

Ltac simplify_wp :=
  repeat first [ rewrite <- wp_lhs_assign
               | rewrite <- wp_lhs_lvar
               | rewrite <- wp_lhs_gvar
               | rewrite <- wp_rhs_int
               | rewrite <- wp_lhs_deref
               | rewrite <- wp_rhs_addrof
               | rewrite <- wp_rhs_cast_l2r
               | rewrite <- wp_lhs_member
               | rewrite <- wp_rhs_this
               ].


Ltac simplifying :=
  repeat first [ progress simplify_wp
               | progress simpl wps
               | rewrite <- wp_skip
               | rewrite <- wp_seq_nil
               | rewrite <- wp_seq_cons
               | rewrite <- wp_decl_nil
               | rewrite <- wp_decl_cons
               | rewrite <- wp_return_val
               | rewrite <- wp_return_void
               | rewrite <- wp_if
               | rewrite <- wp_continue
               | rewrite <- wp_break
               | rewrite <- wp_rhs_binop
               | rewrite <- wp_rhs_cast_function2pointer
               ].

Ltac has_type :=
  first [ eapply has_type_int ; lia
        | eapply has_type_int32 ; lia
        | eapply has_type_qual ; has_type ].

Ltac operator :=
  first [ subst ; eapply eval_add; [ first [ reflexivity | nia ] | has_type ] ].

Ltac work :=
  let tac := try match goal with
                 | |- @eq val _ _ => try f_equal
                 end ;
             try solve [ eauto | reflexivity | has_type | operator | lia ] in
  discharge ltac:(canceler fail tac) tac.
