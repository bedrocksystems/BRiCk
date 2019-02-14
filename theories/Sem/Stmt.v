From Coq.Classes Require Import
     RelationClasses Morphisms.

From Coq Require Import
     Lists.List
     Strings.String.

From Cpp Require Import Ast.
From Cpp.Sem Require Import
        Util Semantics Logic Expr.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

(* note: this is only used for demonstration purposes *)
From Cpp.Auto Require Import Discharge.

Module Type Stmt.
  Local Open Scope string_scope.


  (** continuations
   * C++ statements can terminate in 4 ways.
   *
   * note(gmm): technically, they can also raise exceptions; however,
   * our current semantics doesn't capture this. if we want to support
   * exceptions, we should simply be able to add another case,
   * `k_throw : val -> mpred`.
   *)
  Record Kpreds :=
    { k_normal   : mpred
    ; k_return   : option val -> mpred
    ; k_break    : mpred
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
    : forall (resolve : genv), thread_info -> region -> Ast.Stmt -> Kpreds -> mpred.

  Section with_resolver.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Axiom wp_return_void : forall Q,
        Q.(k_return) None |-- wp resolve ti ρ (Sreturn None) Q.
    Axiom wp_return_val : forall e Q,
        wp_rhs (resolve:=resolve) ti ρ e (finish (fun res => Q.(k_return) (Some res)))
        |-- wp resolve ti ρ (Sreturn (Some e)) Q.

    Axiom wp_break : forall Q,
        Q.(k_break) |-- wp resolve ti ρ Sbreak Q.
    Axiom wp_continue : forall Q,
        Q.(k_continue) |-- wp resolve ti ρ Scontinue Q.

    (* todo(gmm): the expression can be any value category.
     *)
    Axiom wp_expr : forall vc e Q,
        wpAny (resolve:=resolve) ti ρ (vc,e) (finish (fun _ => Q.(k_normal)))
        |-- wp resolve ti ρ (Sexpr vc e) Q.

    Axiom wp_if : forall e thn els Q,
        wp_rhs (resolve:=resolve) ti ρ e (fun v free =>
            free ** if is_true v then
                      wp resolve ti ρ els Q
                    else
                      wp resolve ti ρ thn Q)
        |-- wp resolve ti ρ (Sif None e thn els) Q.

    (* note(gmm): this rule is not sound for a total hoare logic
     *)
    Axiom wp_while : forall t b Q {T : Type} I,
        I |-- wp resolve ti ρ (Sif None t (Sseq (b :: Scontinue :: nil)) Sskip)
                {| k_break    := Q.(k_normal)
                 ; k_continue := I
                 ; k_return v := Q.(k_return) v
                 ; k_normal   := Q.(k_normal) |} ->
        I |-- wp resolve ti ρ (Swhile t b) Q.

    (* note(gmm): this rule is not sound for a total hoare logic
     *)
    Axiom wp_for : forall init test incr b Q Inv,
        match test with
        | None =>
          Inv |-- wp resolve ti ρ (Sseq (b :: Scontinue :: nil))
                {| k_break    := Q.(k_normal)
                 ; k_continue :=
                     match incr with
                     | None => Inv
                     | Some incr => wpAny (resolve:=resolve) ti ρ incr (fun _ _ => Inv)
                     end
                 ; k_return v := Q.(k_return) v
                 ; k_normal   := Q.(k_normal) |}
        | Some test =>
          Inv |-- wp resolve ti ρ (Sif None test (Sseq (b :: Scontinue :: nil)) Sskip)
                {| k_break    := Q.(k_normal)
                 ; k_continue :=
                     match incr with
                     | None => Inv
                     | Some incr => wpAny (resolve:=resolve) ti ρ incr (fun _ _ => Inv)
                     end
                 ; k_return v := Q.(k_return) v
                 ; k_normal   := Q.(k_normal) |}
        end ->
        Inv |-- wp resolve ti ρ (Sfor init test incr b) Q.

    Axiom wp_do : forall t b Q {T : Type} I,
        I |-- wp resolve ti ρ (Sseq (b :: (Sif None t Scontinue Sskip) :: nil))
                {| k_break    := Q.(k_normal)
                 ; k_continue := I
                 ; k_return v := Q.(k_return) v
                 ; k_normal   := Q.(k_normal) |} ->
        I |-- wp resolve ti ρ (Sdo b t) Q.

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
               (* ^ Q is the continuation for after the entire declaration
                *     is complete
                * ^ k is the rest of the declaration
                *)
    : mpred :=
      match ty with
      | Trv_reference t
      | Treference t =>
        match init with
        | None => lfalse
          (* ^ references must be initialized *)
        | Some init =>
          (* i should use the type here *)
          wp_lhs (resolve:=resolve) ti ρ init (fun a free =>
             addr_of ρ x a -* (free ** k (Kfree (addr_of ρ x a) Q)))
        end
      | Tfunction _ _ =>
        (* inline functions are not supported *)
        lfalse
      | Tvoid => lfalse
      | Tpointer _
      | Tbool
      | Tchar _ _
      | Tint _ _ =>
        match init with
        | None =>
          Forall v, tlocal ρ ty x v -* k (Kfree (Exists v', tlocal ρ ty x v') Q)
        | Some init =>
          wp_rhs (resolve:=resolve) ti ρ init (fun v free =>
                 tlocal ρ ty x v
              -* (free ** k (Kfree (Exists v', tlocal ρ ty x v') Q)))
        end
      | Tarray _ _ => lfalse (* todo(gmm): arrays not yet supported *)
      | Tref gn =>
        match init with
        | Some (Econstructor cnd es _) =>
          (* todo(gmm): constructors and destructors need to be handled through
           * `cglob`.
           *)
          Exists ctor, [| glob_addr resolve cnd ctor |] **
          (* we don't need the destructor until later, but if we prove it
           * early, then we don't need to resolve it over multiple paths.
           *)
          Exists dtor, [| glob_addr resolve (gn ++ "D1") dtor |] **
          (* todo(gmm): is there a better way to get the destructor? *)
          wps (wpAnys (resolve:=resolve) ti ρ) es (fun vs free =>
                 Forall a, uninitialized_ty (Tref gn) a
              -* |> fspec (Vptr ctor) (a :: vs) ti (fun _ =>
                 addr_of ρ x a -*
                 (free ** k (Kseq_all (fun Q => |> fspec (Vptr dtor) (a :: nil) ti
                                   (fun _ => addr_of ρ x a ** uninitialized_ty (Tref gn) a ** Q)) Q)))) empSP
        | _ => lfalse
          (* ^ all non-primitive declarations must have initializers *)
        end
      | Tqualified _ ty => wp_decl x ty init k Q
      end.

    Fixpoint wp_decls (ds : list (ident * type * option Expr))
             (k : Kpreds -> mpred) : Kpreds -> mpred :=
      match ds with
      | nil => k
      | (x, ty, init) :: ds =>
        wp_decl x ty init (wp_decls ds k)
      end.

    (* note(gmm): this rule is slightly non-compositional because
     * wp_decls requires the rest of the block computation
     * - i could fix this in the syntax tree if i split up Sseq
     *   and made Edecl take the continuation
     *)
    Fixpoint wp_block (ss : list Stmt) (Q : Kpreds) : mpred :=
      match ss with
      | nil => Q.(k_normal)
      | Sdecl ds :: ss =>
        wp_decls ds (wp_block ss) Q
      | s :: ss =>
        wp resolve ti ρ s
           {| k_normal   := wp_block ss Q
            ; k_break    := Q.(k_break)
            ; k_continue := Q.(k_continue)
            ; k_return v := Q.(k_return) v |}
      end.

    Axiom wp_seq : forall Q ss,
        wp_block ss Q |-- wp resolve ti ρ (Sseq ss) Q.

  End  with_resolver.

  Module example.

    (* Ltac simplify_wps := *)
    (*   repeat first [ progress simplify_wp *)
    (*                | progress simpl wps *)
    (*                | rewrite <- wp_seq; *)
    (*                  simpl wp_block *)
    (*                | rewrite <- wp_return_val *)
    (*                | rewrite <- wp_return_void *)
    (*                | rewrite <- wp_if *)
    (*                | rewrite <- wp_continue *)
    (*                | rewrite <- wp_break *)
    (*                | rewrite <- wp_rhs_binop *)
    (*                | rewrite <- wp_call *)
    (*                | rewrite <- wp_rhs_cast_function2pointer *)
    (*                ]. *)

(*
    Goal empSP
         |-- wp resolve (Sseq
                           ((Sdecl (("x", T_int, Some (Eint 1 T_int))
                                      :: nil))
                              :: Sdecl (("y", T_int, Some (Eint 12 T_int)) :: nil)
                              :: Sreturn (Some (El2r (Evar (Lname "x"))))
                              :: nil))
         (val_return (fun x => [| x = Vint 1 |])).
    Proof.
      simplify_wps. simpl.
      unfold tlocal, tptsto.
      t.
    Qed.
*)

  End example.

End Stmt.

Declare Module S : Stmt.

Export S.