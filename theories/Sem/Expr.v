(**
 * (Axiomatic) Expression semantics
 *
 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Cpp Require Ast Parser.
Import Cpp.Parser.
From Cpp.Sem Require Import
     Util Logic Semantics.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

(* note: this is used only for testing purposes.
 *)
Require auto.Tactics.Discharge.

Module Type Expr.

  Definition tptsto (ty : type) (p : val) (v : val) : mpred :=
    ptsto p v ** [| has_type v ty |].


  Definition local (x : ident) (v : val) : mpred :=
    Exists a, addr_of x a ** ptsto a v.
  Definition tlocal (ty : type) (x : ident) (v : val) : mpred :=
    Exists a, addr_of x a ** tptsto ty a v.

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

  (* this just applies `wp` across a list *)
  Section wps.
    Context {T U V : Type}.
    Variable wp : T -> (U -> V) -> V.

    Fixpoint wps (es : list T) (Q : list U -> V) : V :=
      match es with
      | nil => Q nil
      | e :: es => wp e (fun v => wps es (fun vs => Q (cons v vs)))
      end.
  End wps.


  Coercion Vint : Z >-> val.
  Coercion Z.of_N : N >-> Z.
  Definition El2r := Ecast Cl2r.

  (**
   * Weakest pre-condition for expressions
   *)
  Variant mode : Set := Lvalue | Rvalue.
  (* ^ this is not complete with respect to the latest versions of C++ *)

  (* todo(gmm): `wpe` should be indexed by types
   *)
  Parameter wpe : forall (resolve : genv), mode -> Expr -> (val -> mpred) -> mpred.

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
  Section with_resolve.
    Context {resolve : genv}.


    (* the biggest question in these semantics is how types fit into things.
     * > C semantics doesn't use a lot of implicit casts.
     *)
    Definition wp_rhs : Expr -> (val -> mpred) -> mpred :=
      wpe resolve Rvalue.
    Definition wp_lhs : Expr -> (val -> mpred) -> mpred :=
      wpe resolve Lvalue.


    Notation "[! P !]" := (embed P).

    (* integer literals are rvalues *)
    Axiom wp_rhs_int : forall n ty Q,
      [! has_type (Vint n) ty !] //\\ Q (Vint n)
      |-- wp_rhs (Eint n ty) Q.

    (* boolean literals are rvalues *)
    Axiom wp_rhs_bool : forall (b : bool) Q,
      (if b
       then Q (Vint 1)
       else Q (Vint 0))
      |-- wp_rhs (Ebool b) Q.

    (* `this` is an rvalue *)
    Axiom wp_rhs_this : forall ty Q,
      Exists a, (addr_of "#this"%string a ** ltrue) //\\ Q a
      |-- wp_rhs (Ethis ty) Q.

    (* variables are lvalues *)
    Axiom wp_lhs_lvar : forall ty x Q,
      Exists a, (addr_of x a ** ltrue) //\\ Q a
      |-- wp_lhs (Evar (Lname x) ty) Q.

    (* what about the type? if it exists *)
    Axiom wp_lhs_gvar : forall ty x Q,
        Exists a, [! glob_addr resolve x a !]//\\ Q (Vptr a)
        |-- wp_lhs (Evar (Gname x) ty) Q.

    (* this is a "prvalue" if
     * - `e` is a member enumerator or non-static member function
     * - `e` is an rvalue and `m` is non-static data of non-reference type
     *)
    Axiom wp_lhs_member : forall ty e f Q,
      wp_lhs e (fun base =>
         Exists offset,
                [| @offset_of resolve (Tref f.(f_type)) f.(f_name) offset |]
           ** Q (offset_ptr base offset))
      |-- wp_lhs (Emember e f ty) Q.

(*
    Axiom wp_lhs_subscript : forall e n Q,
        wp_rhs e (fun base => wp_rhs n (fun i => _))
        |-- wp_lhs (Esubscript e n) Q.
*)

    (* the `*` operator is an lvalue *)
    Axiom wp_lhs_deref : forall ty e (Q : val -> mpred),
        wp_rhs e Q
        |-- wp_lhs (Ederef e ty) Q.

    (* the `&` operator is a prvalue *)
    Axiom wp_rhs_addrof : forall ty e Q,
        wp_lhs e Q
        |-- wp_rhs (Eaddrof e ty) Q.

    (* unary operators *)
    Axiom wp_rhs_unop : forall o e ty Q,
        wp_rhs e (fun v => Exists v', embed (eval_unop o ty v v') //\\ Q v')
        |-- wp_rhs (Eunop o e ty) Q.

    (* note(gmm): operators need types! *)
    Axiom wp_lhs_preinc : forall e ty Q,
        wp_lhs e (fun a => Exists v', Exists v'',
              ptsto a v' ** [| eval_binop Badd ty v' (Vint 1) v'' |] **
              (ptsto a v'' -* Q a))
        |-- wp_lhs (Epreinc e ty) Q.

    Axiom wp_lhs_predec : forall e ty Q,
        wp_lhs e (fun a => Exists v', Exists v'',
              tptsto ty a v' ** [| eval_binop Bsub ty v' (Vint 1) v'' |] **
              (tptsto ty a v'' -* Q a))
        |-- wp_lhs (Epredec e ty) Q.

    Axiom wp_rhs_postinc : forall e ty Q,
        wp_lhs e (fun a => Exists v', Exists v'',
              tptsto ty a v' ** [| eval_binop Badd ty v' (Vint 1) v'' |] **
              (tptsto ty a v'' -* Q v'))
        |-- wp_rhs (Epostinc e ty) Q.

    Axiom wp_rhs_postdec : forall e ty Q,
        wp_lhs e (fun a => Exists v', Exists v'',
              tptsto ty a v' ** [| eval_binop Bsub ty v' (Vint 1) v'' |] **
              (tptsto ty a v'' -* Q v'))
        |-- wp_lhs (Epostdec e ty) Q.

    (** binary operators *)
    Axiom wp_rhs_binop : forall o e1 e2 ty Q,
        wp_rhs e1 (fun v1 => wp_rhs e2 (fun v2 =>
            Exists v', embed (eval_binop o ty v1 v2 v') //\\ Q v'))
        |-- wp_rhs (Ebinop o e1 e2 ty) Q.

    Axiom wp_lhs_assign : forall ty l r Q,
        wp_lhs l (fun la => wp_rhs r (fun rv =>
           (Exists v, ptsto la v) ** (ptsto la rv -* Q la)))
        |-- wp_lhs (Eassign l r ty) Q.

(*
    Axiom wp_lhs_bop_assign : forall ty o l r Q,
        wp_lhs (Eassign l (Ebinop o (Ecast Cl2r l _) r ty) ty) Q
        |-- wp_lhs (Eassign_op o l r ty) Q.
*)

    (* note: the comma operator can be both an lvalue and a prvalue
     * depending on what the second expression is.
     * todo(gmm): the first expression can be any value category.
     *)
    Axiom wpe_comma : forall {m} ty e1 e2 Q,
        wpe resolve m e1 (fun _ => wpe resolve m e2 Q)
        |-- wpe resolve m (Ecomma e1 e2 ty) Q.

    (** short-circuting operators *)
    Axiom wp_rhs_seqand : forall ty e1 e2 Q,
        wp_rhs e1 (fun v1 =>
           if is_true v1
           then wp_rhs e2 (fun v2 =>
                                     if is_true v2
                                     then Q (Vint 1)
                                     else Q (Vint 0))
           else Q (Vint 0))
        |-- wp_rhs (Eseqand e1 e2 ty) Q.

    Axiom wp_rhs_seqor : forall ty e1 e2 Q,
        wp_rhs e1 (fun v1 =>
           if is_true v1
           then Q (Vint 1)
           else wp_rhs e2 (fun v2 =>
                                     if is_true v2
                                     then Q (Vint 1)
                                     else Q (Vint 0)))
        |-- wp_rhs (Eseqor e1 e2 ty) Q.

    (** casts *)
    Axiom wp_rhs_cast_l2r : forall ty e Q,
        wp_lhs e (fun a => Exists v, (tptsto ty a v ** ltrue) //\\ Q v)
        |-- wp_rhs (Ecast Cl2r e ty) Q.

    Axiom wp_rhs_cast_noop : forall ty m e Q,
        wpe resolve m e Q
        |-- wpe resolve m (Ecast Cnoop e ty) Q.

    Axiom wp_rhs_cast_int2bool : forall ty m e Q,
        wpe resolve m e Q
        |-- wpe resolve m (Ecast Cint2bool e ty) Q.

    Axiom wp_rhs_cast_function2pointer : forall ty ty' g Q,
        wp_lhs (Evar (Gname g) ty') Q
        |-- wp_rhs (Ecast Cfunction2pointer (Evar (Gname g) ty') ty) Q.

    (** the ternary operator `_ ? _ : _` *)
    Axiom wp_rhs_condition : forall ty m tst th el Q,
        wp_rhs tst (fun v1 =>
           if is_true v1
           then wpe resolve m th Q
           else wpe resolve m el Q)
        |-- wpe resolve m (Eif tst th el ty) Q.

    (** `sizeof` and `alignof` *)
    Axiom wp_rhs_sizeof : forall ty' ty Q,
        Exists sz, [| @size_of resolve ty sz |] ** Q (Vint (Z.of_N sz))
        |-- wp_rhs (Esize_of (inl ty) ty') Q.

(*
    Axiom wp_rhs_alignof : forall ty Q,
        Exists sz, [| @align_of resolve ty sz |] ** Q (Vint (Z.of_N sz))
        |-- wp_rhs (Ealign_of (inl ty)) Q.
*)

    (** function calls *)
    (* todo(gmm): the evaluation mode for the arguments depends on the
     * function being called.
     *)
    Axiom wp_call : forall ty f es Q,
        wp_rhs f (fun f => wps wp_rhs es (fun vs => |> fspec f vs Q))
        |-- wp_rhs (Ecall f es ty) Q.

    (* todo(gmm): the evaluation mode for the arguments depends on the
     * function being called.
     *)
    Axiom wp_member_call : forall ty f obj es Q,
        Exists fa, [| glob_addr resolve f fa |] **
        wp_lhs obj (fun this => wps wp_rhs es (fun vs =>
            |> fspec (Vptr fa) (this :: vs) Q))
        |-- wp_rhs (Emember_call false f obj es ty) Q.

  End with_resolve.

  Module examples.
    Import auto.Tactics.Discharge.

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

    Section with_resolve.
      Context {resolve : genv}.
      Local Open Scope Z_scope.

      (* int x ; x = 0 ; *)
      Goal
        tlocal T_int32 "x" 3
        |-- wp_lhs (resolve:=resolve)
                   (Eassign (Evar (Lname "x") T_int32) (Eint 0 T_int32) (Treference T_int32))
                   (fun xa => addr_of "x" xa ** tptsto T_int32 xa 0).
      Proof.
        unfold tlocal.
        repeat (t; simplify_wp).
        unfold tptsto.
        t.
      Qed.

(*
      Definition local_at (l : ident) (a : val) (v : val) : mpred :=
        addr_of l a ** ptsto a v.

      (* int *x ; *x = 0 ; *)
      Goal forall addr,
        tlocal T_int "x" addr ** tptsto T_int addr 12%Z
        |-- wp_lhs (resolve:=resolve)
        (Eassign
           (Ederef
              (Ecast (CCcast Cl2r)
                     (Evar
                        (Lname  "x")
                        (Qmut
                           (Tpointer
                              (Qmut T_int))))
                     (Qmut
                        (Tpointer
                           (Qmut T_int))))
              (Qmut T_int))
           (Eint 0
                 (Qmut T_int))
           (Qmut T_int))
                   (fun x => embed (x = addr) //\\ tlocal T_int "x" x ** tptsto T_int x 0%Z).
      Proof.
        intros.
        repeat (t; simplify_wp).
      Qed.

      (* int *x ; int y ; x = &y ; *)
      Goal
        local "x" 3%Z ** local "y" 12%Z
        |-- wp_lhs (resolve:=resolve)
                   (Eassign (Evar (Lname "x")) (Eaddrof (Evar (Lname "y"))))
                   (fun xa => Exists ya, local "x" ya ** addr_of "y" ya ** ptsto ya 12).
      Proof.
        unfold local.
        repeat (t; simplify_wp).
      Qed.

      (* int *x ; int y ; *(x = &y) = 3; *)
      Goal
        local "x" 3%Z ** local "y" 9%Z
        |-- wp_lhs (resolve:=resolve)
                   (Eassign
                      (Ederef (El2r (Eassign (Evar (Lname "x"))
                                             (Eaddrof (Evar (Lname "y"))))))
                      (Eint 3 T_int32))%Z
                   (fun ya => local "x" ya ** ptsto ya 3%Z ** addr_of "y" ya).
      Proof.
        unfold local.
        repeat (t; simplify_wp).
      Qed.
*)
    End with_resolve.

  End examples.

End Expr.

Declare Module E : Expr.

Export E.