(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * (Axiomatic) Expression semantics
 *
 *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Util Logic Semantics PLogic Wp Typing.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

(* note: this is used only for testing purposes.
 *)
Require Cpp.Auto.Discharge.

Module Type Expr.

  Coercion Vint : Z >-> val.
  Coercion Z.of_N : N >-> Z.
  Definition El2r := Ecast Cl2r.

  (**
   * Weakest pre-condition for expressions
   *)

  Section with_resolve.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp_lhs := (wp_lhs (resolve:=resolve) ti ρ).
    Local Notation wp_rhs := (wp_rhs (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (resolve:=resolve) ti ρ).
    Local Notation wpe := (wpe (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (resolve:=resolve) ti ρ).

    Notation "[! P !]" := (embed P).

    (* integer literals are rvalues *)
    Axiom wp_rhs_int : forall n ty Q,
      [! has_type (Vint n) (drop_qualifiers ty) !] //\\ Q (Vint n) empSP
      |-- wp_rhs (Eint n ty) Q.

    (* note that `char` is actually `byte` *)
    Axiom wp_rhs_char : forall c ty Q,
      let n := Ascii.N_of_ascii c in
      [! has_type (Vint n) (drop_qualifiers ty) !] //\\ Q (Vint n) empSP
      |-- wp_rhs (Echar c ty) Q.

    (* boolean literals are rvalues *)
    Axiom wp_rhs_bool : forall (b : bool) Q,
      Q (Vint (if b then 1 else 0)) empSP
      |-- wp_rhs (Ebool b) Q.

    (* `this` is an rvalue *)
    Axiom wp_rhs_this : forall ty Q,
      Exists a, (_this ρ &~ a ** ltrue) //\\ Q a empSP
      |-- wp_rhs (Ethis ty) Q.


    (* variables are lvalues *)
    Axiom wp_lhs_lvar : forall ty x Q,
        Exists a, (_local ρ x &~ a ** ltrue) //\\ Q a empSP
        |-- wp_lhs (Evar (Lname x) ty) Q.

    (* what about the type? if it exists *)
    Axiom wp_lhs_gvar : forall ty x Q,
        Exists a, [! glob_addr resolve x a !] //\\ Q (Vptr a) empSP
        |-- wp_lhs (Evar (Gname x) ty) Q.

    (* this is a "prvalue" if
     * - `e` is a member enumerator or non-static member function
     * - `e` is an rvalue and `m` is non-static data of non-reference type
     *)
    Axiom wp_lhs_member : forall ty e f Q,
      wp_lhs e (fun base free =>
                  Exists addr, (_offsetL (_field f) (_eq base) &~ addr ** ltrue) //\\ Q addr free)
      |-- wp_lhs (Emember e f ty) Q.

    Axiom wp_lhs_subscript : forall e i t Q,
      wp_rhs e (fun base free =>
        wp_rhs i (fun idx free' =>
          Exists addr,
          (Exists i, [| idx = Vint i |] **
          _offsetL (_sub (drop_qualifiers t) i) (_eq base) &~ addr ** ltrue) //\\
          Q addr (free' ** free)))
      |-- wp_lhs (Esubscript e i t) Q.

    (* the `*` operator is an lvalue *)
    Axiom wp_lhs_deref : forall ty e Q,
        wp_rhs e Q
        |-- wp_lhs (Ederef e ty) Q.

    (* the `&` operator is a prvalue *)
    Axiom wp_rhs_addrof : forall ty e Q,
        wp_lhs e Q
        |-- wp_rhs (Eaddrof e ty) Q.

    (* unary operators *)
    Axiom wp_rhs_unop : forall o e ty Q,
        wp_rhs e (fun v free =>
          Exists v',
          embed (eval_unop o (drop_qualifiers ty) (drop_qualifiers ty) v v') //\\ Q v' free)
        |-- wp_rhs (Eunop o e ty) Q.

    (* note(gmm): operators need types! *)
    Axiom wp_lhs_preinc : forall e ty Q,
        wp_lhs e (fun a free => Exists v', Exists v'',
              _at (_eq a) (tprim (drop_qualifiers ty) v') **
              [| eval_binop Badd (drop_qualifiers (type_of e)) (drop_qualifiers (type_of e)) (drop_qualifiers ty) v' (Vint 1) v'' |] **
              (_at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q a free))
        |-- wp_lhs (Epreinc e ty) Q.

    Axiom wp_lhs_predec : forall e ty Q,
        wp_lhs e (fun a free => Exists v', Exists v'',
              _at (_eq a) (tprim (drop_qualifiers ty) v') **
              [| eval_binop Bsub (drop_qualifiers (type_of e)) (drop_qualifiers (type_of e)) (drop_qualifiers ty) v' (Vint 1) v'' |] **
              (_at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q a free))
        |-- wp_lhs (Epredec e ty) Q.

    Axiom wp_rhs_postinc : forall e ty Q,
        wp_lhs e (fun a free => Exists v', Exists v'',
              _at (_eq a) (tprim (drop_qualifiers ty) v') **
              [| eval_binop Badd (drop_qualifiers (type_of e)) (drop_qualifiers (type_of e)) (drop_qualifiers ty) v' (Vint 1) v'' |] **
              (_at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q v' free))
        |-- wp_rhs (Epostinc e ty) Q.

    Axiom wp_rhs_postdec : forall e ty Q,
        wp_lhs e (fun a free => Exists v', Exists v'',
              _at (_eq a) (tprim (drop_qualifiers ty) v') **
              [| eval_binop Bsub (drop_qualifiers (type_of e)) (drop_qualifiers (type_of e)) (drop_qualifiers ty) v' (Vint 1) v'' |] **
              (_at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q v' free))
        |-- wp_rhs (Epostdec e ty) Q.

    (** binary operators *)
    Axiom wp_rhs_binop : forall o e1 e2 ty Q,
        wp_rhs e1 (fun v1 free1 => wp_rhs e2 (fun v2 free2 =>
            Exists v', embed (eval_binop o (drop_qualifiers (type_of e1)) (drop_qualifiers (type_of e2)) (drop_qualifiers ty) v1 v2 v') //\\ Q v' (free1 ** free2)))
        |-- wp_rhs (Ebinop o e1 e2 ty) Q.

    Axiom wp_lhs_assign : forall ty l r Q,
        wp_lhs l (fun la free1 => wp_rhs r (fun rv free2 =>
            _at (_eq la) (tany (drop_qualifiers ty)) **
           (_at (_eq la) (tprim (drop_qualifiers ty) rv) -* Q la (free1 ** free2))))
        |-- wp_lhs (Eassign l r ty) Q.

    Axiom wp_lhs_bop_assign : forall ty o l r Q,
        wp_lhs (Eassign l (Ebinop o (Ecast Cl2r l (type_of l)) r ty) ty) Q
        |-- wp_lhs (Eassign_op o l r ty) Q.

    (* note: the comma operator can be both an lvalue and a prvalue
     * depending on what the second expression is.
     * todo(gmm): the first expression can be any value category.
     *)
    Axiom wpe_comma : forall {m vc} ty e1 e2 Q,
        wpAny (vc, e1) (fun _ free1 => wpe m e2 (fun val free2 => Q val (free1 ** free2)))
        |-- wpe m (Ecomma vc e1 e2 ty) Q.

    (** short-circuting operators *)
    Axiom wp_rhs_seqand : forall ty e1 e2 Q,
        wp_rhs e1 (fun v1 free1 =>
           if is_true v1
           then wp_rhs e2 (fun v2 free2 =>
                                     if is_true v2
                                     then Q (Vint 1) (free1 ** free2)
                                     else Q (Vint 0) (free1 ** free2))
           else Q (Vint 0) free1)
        |-- wp_rhs (Eseqand e1 e2 ty) Q.

    Axiom wp_rhs_seqor : forall ty e1 e2 Q,
        wp_rhs e1 (fun v1 free1 =>
           if is_true v1
           then Q (Vint 1) free1
           else wp_rhs e2 (fun v2 free2 =>
                                     if is_true v2
                                     then Q (Vint 1) (free1 ** free2)
                                     else Q (Vint 0) (free1 ** free2)))
        |-- wp_rhs (Eseqor e1 e2 ty) Q.

    (** casts *)
    Axiom wp_rhs_cast_l2r : forall ty e Q,
        wp_lhs e (fun a free =>
          Exists v, (_at (_eq a) (tprim (drop_qualifiers ty) v) ** ltrue) //\\ Q v free)
        |-- wp_rhs (Ecast Cl2r e ty) Q.

    Axiom wpe_cast_noop : forall ty m e Q,
        wpe m e Q
        |-- wpe m (Ecast Cnoop e ty) Q.

    Axiom wp_rhs_cast_int2bool : forall ty e Q,
        wp_rhs e Q
        |-- wp_rhs (Ecast Cint2bool e ty) Q.
    (* ^ todo(gmm): confirm that this doesn't change the value *)

    Axiom wp_rhs_cast_ptr2bool : forall ty e Q,
        wp_rhs e Q
        |-- wp_rhs (Ecast Cptr2bool e ty) Q.
    (* ^ todo(gmm): confirm that this doesn't change the value *)

    Axiom wp_rhs_cast_function2pointer : forall ty ty' g Q,
        wp_lhs (Evar (Gname g) ty') Q
        |-- wp_rhs (Ecast Cfunction2pointer (Evar (Gname g) ty') ty) Q.

    Axiom wp_rhs_cast_bitcast : forall e t Q,
        wp_rhs e Q
        |-- wp_rhs (Ecast Cbitcast e t) Q.

    Axiom wp_rhs_cast_integral : forall e t Q,
        wp_rhs e (fun v free => [| has_type v t |] ** Q v free)
        |-- wp_rhs (Ecast Cintegral e t) Q.

    (** the ternary operator `_ ? _ : _` *)
    Axiom wp_condition : forall ty m tst th el Q,
        wp_rhs tst (fun v1 free =>
           if is_true v1
           then wpe m th (fun v free' => Q v (free ** free'))
           else wpe m el (fun v free' => Q v (free ** free')))
        |-- wpe m (Eif tst th el ty) Q.
    (* ^ todo(gmm): it would be sound for `free` to occur in the branches *)

    (** `sizeof` and `alignof` *)
    Axiom wp_rhs_sizeof : forall ty' ty Q,
        Exists sz, [| @size_of resolve ty sz |] ** Q (Vint (Z.of_N sz)) empSP
        |-- wp_rhs (Esize_of (inl ty) ty') Q.

    Axiom wp_rhs_alignof : forall ty' ty Q,
        Exists sz, [| @align_of resolve ty sz |] ** Q (Vint (Z.of_N sz)) empSP
        |-- wp_rhs (Ealign_of (inl ty) ty') Q.

    (** constructors (these should probably get moved) *)
    Axiom wp_rhs_constructor
    : forall cls cname (es : list (ValCat * Expr)) (ty : type) (Q : val -> FreeTemps -> mpred),
     (Exists ctor, [| glob_addr resolve cname ctor |] **
      (* todo(gmm): is there a better way to get the destructor? *)
      wps wpAnys es (fun vs free => Exists a, _at (_eq a) (uninit (Tref cls))
          -* |> fspec (resolve:=resolve) (Vptr ctor) (a :: vs) ti (fun _ =>
                   (* note(gmm): constructors are rvalues but my semantics actually
                    * treats them like lvalues. *)
                   Q a free)) empSP)
      |-- wp_rhs (Econstructor cname es (Tref cls)) Q.

    (** function calls *)
    Axiom wp_call : forall ty f es Q,
        wp_rhs f (fun f => wps wpAnys es (fun vs free =>
            |> fspec (resolve:=resolve) f vs ti (fun v => Q v free)))
        |-- wp_rhs (Ecall f es ty) Q.

    Axiom wp_member_call : forall ty f obj es Q,
        Exists fa, [| glob_addr resolve f fa |] **
        wp_lhs obj (fun this => wps wpAnys es (fun vs free =>
            |> fspec (resolve:=resolve) (Vptr fa) (this :: vs) ti (fun v => Q v free)))
        |-- wp_rhs (Emember_call false f obj es ty) Q.

  End with_resolve.

  Module examples.
    Import Cpp.Auto.Discharge.

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
      first [ eapply has_int_type ; unfold bound; simpl; lia ].

    Ltac operator :=
      first [ subst ; eapply eval_add; [ first [ reflexivity | nia ] | has_type ] ].

    Opaque _local.

    Section with_resolve.
      Context {resolve : genv}.
      Variable ti : thread_info.
      Variable ρ : region.
      Local Open Scope Z_scope.

      Definition wp_ok e Q := wp_lhs (resolve:=resolve) ti ρ e (finish Q).

      Definition is_pointer (t : type) : bool :=
        match t with
        | Tpointer _ => true
        | _ => false
        end.

      Ltac t :=
        let fwd :=
            idtac;
            lazymatch goal with
            | |- _at _ (tprim ?X ?V) ** _ |-- _ =>
              lazymatch eval compute in (is_pointer X) with
              | true =>
                lazymatch V with
                | Vptr _ => fail
                | _ => eapply refine_tprim_ptr; let H := fresh in intros ? H; destruct H
                end
              end
            end
        in
        let bwd := idtac; fail in
        let ctac :=
            idtac;
            first [ simple eapply _at_cancel; [ solve [ reflexivity
                                                      | eapply tprim_tptr
                                                      | eapply tprim_tint
                                                      | eapply tprim_tuint
                                                      | simple eapply tprim_any
                                                      | simple eapply tptr_any
                                                      | simple eapply tint_any
                                                      | simple eapply tuint_any
                                                      ] | ] ]
        in
        let tac :=
            idtac;
            try match goal with
                | |- @eq val _ _ => try f_equal
                end ;
            try solve [ eauto | reflexivity | has_type | operator | lia ] in
        discharge ltac:(fwd) idtac ltac:(bwd) ltac:(canceler ctac tac) ltac:(tac).

      (* int x ; x = 0 ; *)
      Goal
        tlocal ρ "x" (tint 32 3)
        |-- wp_ok (Eassign (Evar (Lname "x") (Qmut T_int32)) (Eint 0 (Qmut T_int32)) (Qmut T_int32))
                  (fun xa => tlocal_at ρ "x" xa (tint 32 0)).
      Proof.
        unfold wp_ok.
        unfold tlocal, tlocal_at.
        repeat (t; simplify_wp; unfold wp_ok, finish).
      Qed.

      (* note(gmm):
       * having two layers of logic makes sense.
       * - layer 1 is static choices  (class layout, glob_addr, code_at, etc)
       * - layer 2 is dynamic choices (ptsto, etc)
       *)

      (* int *x ; *x = 0 ; *)
      Goal forall addr,
        tlocal ρ "x" (tptr (Qmut T_int) addr) **
        _at (_eq (Vptr addr)) (tprim T_int 12%Z)
        |-- wp_ok
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
                   (fun x => embed (x = Vptr addr) //\\
                          tlocal ρ "x" (tptr T_int addr) **
                          _at (_eq x) (tprim T_int 0%Z)).
      Proof.
        intros.
        unfold tlocal, tlocal_at.
        repeat (t; simplify_wp; unfold wp_ok, finish).
      Qed.

      (* int *x ; int y ; x = &y ; *)
      Goal forall p,
        tlocal ρ "x" (tptr (Qmut T_int) p) **
        tlocal ρ "y" (tint 32 12)
        |-- wp_ok
                   (Eassign (Evar (Lname "x") (Qmut (Tpointer (Qmut T_int))))
                            (Eaddrof (Evar (Lname "y") (Qmut T_int)) (Qconst (Tpointer (Qmut T_int))))
                            (Qmut (Tpointer (Qmut T_int))))
                   (fun xa => Exists ya,
                           tlocal_at ρ "x" xa (tptr (Qmut T_int) ya) **
                           tlocal_at ρ "y" (Vptr ya) (tint int_bits 12)).
      Proof.
        intros.
        unfold tlocal, tlocal_at.
        repeat (t; simplify_wp; unfold wp_ok, finish).
      Qed.

      (* int *x ; int y ; *(x = &y) = 3; *)
      Goal forall p,
        tlocal ρ "x" (tptr (Qmut T_int) p) **
        tlocal ρ "y" (tint 32 9%Z)
        |-- wp_ok
                   (Eassign
                (Ederef
                  (Ecast (CCcast Cl2r)
                    (Eassign
                      (Evar
                        (Lname  "x")
                        (Qmut
                          (Tpointer
                            (Qmut T_int))))
                      (Eaddrof
                        (Evar
                          (Lname  "y")
                          (Qmut T_int))
                        (Qmut
                          (Tpointer
                            (Qmut T_int))))
                      (Qmut
                        (Tpointer
                          (Qmut T_int))))
                    (Qmut
                      (Tpointer
                        (Qmut T_int))))
                  (Qmut T_int))
                (Eint 3
                  (Qmut T_int))
                (Qmut T_int))
                   (fun ya => Exists pp, [| ya = Vptr pp |] **
                            tlocal ρ "x" (tptr T_int pp) **
                            tlocal_at ρ "y" ya (tint 32 3%Z)).
      Proof.
        intros.
        unfold tlocal, tlocal_at.
        repeat (t; simplify_wp; unfold wp_ok, finish; simpl).
      Qed.

    End with_resolve.

  End examples.

End Expr.

Declare Module E : Expr.

Export E.