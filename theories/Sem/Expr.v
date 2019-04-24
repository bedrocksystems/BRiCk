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
     Util Logic Semantics PLogic.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

(* note: this is used only for testing purposes.
 *)
Require Cpp.Auto.Discharge.

Module Type Expr.

  Fixpoint type_of (e : Expr) : type :=
    match e with
    | Econst_ref _ t
    | Evar _ t
    | Echar _ t
    | Estring _ t
    | Eint _ t => t
    | Ebool _ => Tbool
    | Eunop _ _ t
    | Ebinop _ _ _ t
    | Ederef _ t
    | Eaddrof _ t
    | Eassign _ _ t
    | Eassign_op _ _ _ t
    | Epreinc _ t
    | Epostinc _ t
    | Epredec _ t
    | Epostdec _ t
    | Eseqand _ _ t
    | Eseqor _ _ t
    | Ecomma _ _ _ t
    | Ecall _ _ t
    | Ecast _ _ t
    | Emember _ _ t
    | Emember_call _ _ _ _ t
    | Esubscript _ _ t
    | Esize_of _ t
    | Ealign_of _ t
    | Econstructor _ _ t
    | Eimplicit _ t
    | Eif _ _ _ t
    | Ethis t => t
    | Enull => Tpointer Tvoid
      (* todo(gmm): c++ seems to have a special nullptr type *)
    | Einitlist _ t => t
    | Enew _ _ _ t
    | Edelete _ _ _ t
    | Eandclean _ t
    | Etemp _ t => t
    | Eatomic _ _ t => t
    end.


  Parameter func_ok_raw : Func -> list val -> thread_info -> (val -> mpred) -> mpred.
  (* this assserts the frame axiom for function specifications
   *)
  Axiom func_ok_frame : forall v vs ti Q F,
      func_ok_raw v vs ti Q ** F |-- func_ok_raw v vs ti (fun res => Q res ** F).

  Definition fspec (n : val) (ls : list val) (ti : thread_info) (Q : val -> mpred) : mpred :=
    Exists f, [| n = Vptr f |] **
    Exists func, code_at func f ** func_ok_raw func ls ti Q.

  (* todo(gmm): this is because func_ok is implemented using wp. *)
  Axiom fspec_conseq:
    forall (p : val) (vs : list val) ti (K m : val -> mpred),
      (forall r : val, m r |-- K r) -> fspec p vs ti m |-- fspec p vs ti K.

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

  Definition FreeTemps := mpred.

  Definition finish (Q : val -> mpred) (v : val) (free : FreeTemps) : mpred :=
    free ** Q v.

  (* todo(gmm): `wpe` should be indexed by types
   * - this might not be strictly necessary if all of the expressions
   *   are annotated.
   *)
  Parameter wpe
  : forall (resolve : genv),
      thread_info -> region ->
      ValCat -> Expr ->
      (val -> FreeTemps -> mpred) -> (* result -> free -> post *)
      mpred. (* pre-condition *)

  Axiom Proper_wpe : forall resolve ti r c e,
      Proper ((pointwise_relation _ (pointwise_relation _ lentails)) ==> lentails)
             (wpe resolve ti r c e).
  Global Existing Instance Proper_wpe.


  Section with_resolve.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    (* the biggest question in these semantics is how types fit into things.
     * > C semantics doesn't use a lot of implicit casts.
     *)
    Definition wp_rhs : Expr -> (val -> FreeTemps -> mpred) -> mpred :=
      wpe resolve ti ρ Rvalue.
    Definition wp_lhs : Expr -> (val -> FreeTemps -> mpred) -> mpred :=
      wpe resolve ti ρ Lvalue.

    Definition wpAny (vce : ValCat * Expr)
    : (val -> FreeTemps -> mpred) -> mpred :=
      match vce with
      | (Lvalue,e) => wp_lhs e
      | (Rvalue,e) => wp_rhs e
      | (Xvalue,e) => wp_lhs e
      end.

    Notation "[! P !]" := (embed P).

    (* integer literals are rvalues *)
    Axiom wp_rhs_int : forall n ty Q,
      [! has_type (Vint n) (drop_qualifiers ty) !] //\\ Q (Vint n) empSP
      |-- wp_rhs (Eint n ty) Q.

    (* note that `char` is acutally `byte` *)
    Axiom wp_rhs_char : forall c ty Q,
      let n := Ascii.N_of_ascii c in
      [! has_type (Vint n) (drop_qualifiers ty) !] //\\ Q (Vint n) empSP
      |-- wp_rhs (Echar c ty) Q.

    (* boolean literals are rvalues *)
    Axiom wp_rhs_bool : forall (b : bool) Q,
      (if b
       then Q (Vint 1) empSP
       else Q (Vint 0) empSP)
      |-- wp_rhs (Ebool b) Q.

    (* `this` is an rvalue *)
    Axiom wp_rhs_this : forall ty Q,
      Exists a, ((_local ρ "#this"%string) @@ a ** ltrue) //\\ Q a empSP
      |-- wp_rhs (Ethis ty) Q.


    (* variables are lvalues *)
    Axiom wp_lhs_lvar : forall ty x Q,
      Exists a, (_local ρ x @@ a ** ltrue) //\\ Q a empSP
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
                  Exists addr, _addr base (p_dot f p_done) @@ addr ** Q addr free)
      |-- wp_lhs (Emember e f ty) Q.

    Axiom wp_lhs_subscript : forall e i t Q,
      wp_rhs e (fun base free =>
        wp_rhs i (fun idx free' =>
          Exists i, [| idx = Vint i |] **
          Exists addr, _addr base (p_sub t i p_done) @@ addr **
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


    Section wpsk.
      Context {T U V : Type}.
      Variable wp : T -> (U -> mpred -> V) -> V.

      Fixpoint wpsk (es : list T) (Q : list U -> mpred -> V) {struct es} : V.
      refine
        match es with
        | nil => Q nil empSP
        | e :: es => wp e (fun v free => wpsk es (fun vs free' => Q (cons v vs) (free ** free')))
        end.
      Defined.
    End wpsk.

    (** binary operators *)
    Axiom wp_rhs_binop : forall o e1 e2 ty Q,
        wp_rhs e1 (fun v1 free1 => wp_rhs e2 (fun v2 free2 =>
            Exists v', embed (eval_binop o (drop_qualifiers (type_of e1)) (drop_qualifiers (type_of e2)) (drop_qualifiers ty) v1 v2 v') //\\ Q v' (free1 ** free2)))
        |-- wp_rhs (Ebinop o e1 e2 ty) Q.

    Axiom wp_lhs_assign : forall ty l r Q,
        wp_lhs l (fun la free1 => wp_rhs r (fun rv free2 =>
           _at (_eq la) (uninit (drop_qualifiers ty)) **
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
        wpAny (vc, e1) (fun _ free1 => wpe resolve ti ρ m e2 (fun val free2 => Q val (free1 ** free2)))
        |-- wpe resolve ti ρ m (Ecomma vc e1 e2 ty) Q.

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
        wpe resolve ti ρ m e Q
        |-- wpe resolve ti ρ m (Ecast Cnoop e ty) Q.

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
           then wpe resolve ti ρ m th (fun v free' => Q v (free ** free'))
           else wpe resolve ti ρ m el (fun v free' => Q v (free ** free')))
        |-- wpe resolve ti ρ m (Eif tst th el ty) Q.
    (* ^ todo(gmm): it would be sound for `free` to occur in the branches *)

    (** `sizeof` and `alignof` *)
    Axiom wp_rhs_sizeof : forall ty' ty Q,
        Exists sz, [| @size_of resolve ty sz |] ** Q (Vint (Z.of_N sz)) empSP
        |-- wp_rhs (Esize_of (inl ty) ty') Q.

    Axiom wp_rhs_alignof : forall ty' ty Q,
        Exists sz, [| @align_of resolve ty sz |] ** Q (Vint (Z.of_N sz)) empSP
        |-- wp_rhs (Ealign_of (inl ty) ty') Q.

    Definition wpAnys := fun ve Q free => wpAny ve (fun v f => Q v (f ** free)).

    (** function calls *)
    Axiom wp_call : forall ty f es Q,
        wp_rhs f (fun f => wps wpAnys es (fun vs free => |> fspec f vs ti (fun v => Q v free)))
        |-- wp_rhs (Ecall f es ty) Q.

    Axiom wp_member_call : forall ty f obj es Q,
        Exists fa, [| glob_addr resolve f fa |] **
        wp_lhs obj (fun this => wps wpAnys es (fun vs free =>
            |> fspec (Vptr fa) (this :: vs) ti (fun v => Q v free)))
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


    Section with_resolve.
      Context {resolve : genv}.
      Variable ti : thread_info.
      Variable ρ : region.
      Local Open Scope Z_scope.

      Definition wp_ok e Q := wp_lhs (resolve:=resolve) ti ρ e (finish Q).

      Ltac t :=
        let ctac :=
            idtac;
            first [ eapply _at_cancel; [ solve [ reflexivity | eapply val_uninit ] | ] ]
        in
        let tac := try match goal with
                       | |- @eq val _ _ => try f_equal
                       end ;
                   try solve [ eauto | reflexivity | has_type | operator | lia ] in
        discharge ltac:(canceler ctac tac) tac.

      (* int x ; x = 0 ; *)
      Goal
        tlocal ρ T_int32 "x" 3
        |-- wp_ok (Eassign (Evar (Lname "x") (Qmut T_int32)) (Eint 0 (Qmut T_int32)) (Qmut T_int32))
                  (fun xa => tlocal_at ρ T_int32 "x" xa 0).
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
        tlocal ρ (Qmut (Tpointer (Qmut T_int))) "x" addr **
        _at (_eq addr) (tprim T_int 12%Z)
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
                   (fun x => embed (x = addr) //\\ tlocal ρ (Qmut (Tpointer (Qmut T_int))) "x" x ** _at (_eq x) (tprim T_int 0%Z)).
      Proof.
        intros.
        unfold tlocal, tlocal_at.
        repeat (t; simplify_wp; unfold wp_ok, finish).
      Qed.

      (* int *x ; int y ; x = &y ; *)
      Goal
        tlocal ρ (Tpointer (Qmut T_int)) "x" 3%Z **
        tlocal ρ T_int "y" 12%Z
        |-- wp_ok
                   (Eassign (Evar (Lname "x") (Qmut (Tpointer (Qmut T_int))))
                            (Eaddrof (Evar (Lname "y") (Qmut T_int)) (Qconst (Tpointer (Qmut T_int))))
                            (Qmut (Tpointer (Qmut T_int))))
                   (fun xa => Exists ya,
                           tlocal_at ρ (Tpointer (Qmut (T_int))) "x" xa ya **
                           tlocal_at ρ T_int "y" ya 12%Z).
      Proof.
        unfold tlocal, tlocal_at.
        repeat (t; simplify_wp; unfold wp_ok, finish).
      Qed.

      (* int *x ; int y ; *(x = &y) = 3; *)
      Goal
        tlocal ρ (Tpointer (Qmut T_int)) "x" 3%Z **
        tlocal ρ T_int "y" 9%Z
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
                   (fun ya => tlocal ρ (Tpointer (Qmut T_int)) "x" ya **
                            tlocal_at ρ T_int "y" ya 3%Z).
      Proof.
        unfold tlocal, tlocal_at.
        repeat (t; simplify_wp; unfold wp_ok, finish; simpl).
      Qed.

    End with_resolve.

  End examples.

End Expr.

Declare Module E : Expr.

Export E.