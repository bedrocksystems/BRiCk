(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * Program logic for expressions
 *
 *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNatDef.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred
     heap_pred destroy
     wp call intensional
     compilation_unit.

Module Type Expr.

  Coercion Vint : Z >-> val.
  Coercion Z.of_N : N >-> Z.
  Definition El2r := Ecast Cl2r.

  (**
   * Weakest pre-condition for expressions
   *)

  Section with_resolve.
    Context {Σ:gFunctors} {resolve:genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp_lval := (wp_lval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_prval := (wp_prval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_xval := (wp_xval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_glval := (wp_glval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_rval := (wp_rval (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_init := (wp_init (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_args := (wp_args (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wpe := (wpe (Σ:=Σ) (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (Σ:=Σ) (resolve:=resolve) ti ρ).

    Local Notation mpred := (mpred Σ) (only parsing).
    Local Notation FreeTemps := (FreeTemps Σ) (only parsing).

    Local Notation glob_def := (glob_def resolve) (only parsing).
    Local Notation _global := (@_global resolve) (only parsing).
    Local Notation _field := (@_field resolve) (only parsing).
    Local Notation _sub := (@_sub resolve) (only parsing).
    Local Notation _super := (@_super resolve) (only parsing).
    Local Notation eval_unop := (@eval_unop resolve) (only parsing).
    Local Notation eval_binop := (@eval_binop resolve) (only parsing).
    Local Notation size_of := (@size_of resolve) (only parsing).
    Local Notation align_of := (@align_of resolve) (only parsing).
    Local Notation mdestroy := (@mdestroy Σ resolve) (only parsing).
    Local Notation primR := (@primR Σ resolve) (only parsing).
    Local Notation anyR := (@anyR Σ resolve) (only parsing).
    Local Notation uninitR := (@uninitR Σ resolve) (only parsing).

    Notation "[! P !]" := (embed P).

    (* constants are rvalues *)
    Axiom wp_prval_constant : forall ty cnst e Q,
      glob_def cnst = Some (Gconstant ty (Some e)) ->
      wp_prval e Q
      |-- wp_prval (Econst_ref (Gname cnst) ty) Q.

    (* integer literals are prvalues *)
    Axiom wp_prval_int : forall n ty Q,
      [! has_type (Vint n) (drop_qualifiers ty) !] //\\ Q (Vint n) empSP
      |-- wp_prval (Eint n ty) Q.

    (* note that `char` is actually `byte` *)
    Axiom wp_prval_char : forall c ty Q,
      let n := Ascii.N_of_ascii c in
      [! has_type (Vint n) (drop_qualifiers ty) !] //\\ Q (Vint n) empSP
      |-- wp_prval (Echar c ty) Q.

    (* boolean literals are prvalues *)
    Axiom wp_prval_bool : forall (b : bool) Q,
      Q (Vint (if b then 1 else 0)) empSP
      |-- wp_prval (Ebool b) Q.

    (* `this` is a prvalue *)
    Axiom wp_prval_this : forall ty Q,
      Exists a, (this_addr ρ a ** ltrue) //\\ Q (Vptr a) empSP
      |-- wp_prval (Ethis ty) Q.


    (* variables are lvalues *)
    Axiom wp_lval_lvar : forall ty x Q,
        Exists a, (local_addr ρ x a ** ltrue) //\\ Q (Vptr a) empSP
        |-- wp_lval (Evar (Lname x) ty) Q.

    (* what about the type? if it exists *)
    Axiom wp_lval_gvar : forall ty x Q,
        Exists a, _global x &~ a ** Q (Vptr a) empSP
        |-- wp_lval (Evar (Gname x) ty) Q.

    (* [Emember e f ty] is an lvalue by default except when
     * - where m is a member enumerator or a non-static member function, or
     * - where a is an rvalue and m is a non-static data member of non-reference type
     *)
    Axiom wp_lval_member : forall ty a m Q,
      wp_lval a (fun base free =>
                  Exists addr, (_offsetL (_field m) (_eqv base) &~ addr ** ltrue) //\\ Q (Vptr addr) free)
      |-- wp_lval (Emember a m ty) Q.


    (* [Emember a m ty] is a prvalue if
     * - [a] is a member enumerator or non-static member function, or
     * - [a] is an rvalue and [m] is non-static data of non-reference type
     *)
    Axiom wp_prval_member : forall ty a m Q,
      wp_rval a (fun base free =>
                  Exists addr, (_offsetL (_field m) (_eqv base) &~ addr ** ltrue) //\\ Q (Vptr addr) free)
      |-- wp_prval (Emember a m ty) Q.

    (* [Emember a m ty] is an xvalue if
     * - [a] is an rvalue and [m] is a non-static data member of non-reference type
     *)
    Axiom wp_xval_member : forall ty a m Q,
      wp_rval a (fun base free =>
                  Exists addr, (_offsetL (_field m) (_eqv base) &~ addr ** ltrue) //\\ Q (Vptr addr) free)
      |-- wp_xval (Emember a m ty) Q.

    Fixpoint is_pointer (ty : type) : bool :=
      match ty with
      | Tpointer _
      | Tarray _ _ => true
      | Tqualified _ t => is_pointer t
      | _ => false
      end.

    (* [Esubscript a n ty] is an lvalue if
     * - one operand is an lvalue array
     *   (in clang's syntax tree, this value is converted to an rvalue via
     *    an array2pointer cast)
     *)
    Axiom wp_lval_subscript : forall e i t Q,
      (if is_pointer (type_of e) then
      wp_prval e (fun base free => (* todo: rval? *)
        wp_prval i (fun idx free' =>
          Exists addr,
          (Exists i, [| idx = Vint i |] **
          _offsetL (_sub (erase_qualifiers t) i) (_eqv base) &~ addr ** ltrue) //\\
          Q (Vptr addr) (free' ** free)))
      else
      wp_prval e (fun idx free => (* todo: rval? *)
        wp_prval i (fun base free' =>
          Exists addr,
          (Exists i, [| idx = Vint i |] **
          _offsetL (_sub (erase_qualifiers t) i) (_eqv base) &~ addr ** ltrue) //\\
          Q (Vptr addr) (free' ** free))))
      |-- wp_lval (Esubscript e i t) Q.

    (* [Esubscript e i t]
     * - where one operand is an array rvalue
     *)
    Axiom wp_xval_subscript : forall e i t Q,
      (if is_pointer (type_of e) then
      wp_prval e (fun base free => (* todo: rval? *)
        wp_prval i (fun idx free' =>
          Exists addr,
          (Exists i, [| idx = Vint i |] **
          _offsetL (_sub (erase_qualifiers t) i) (_eqv base) &~ addr ** ltrue) //\\
          Q (Vptr addr) (free' ** free)))
      else
      wp_prval e (fun idx free => (* todo: rval? *)
        wp_prval i (fun base free' =>
          Exists addr,
          (Exists i, [| idx = Vint i |] **
          _offsetL (_sub (erase_qualifiers t) i) (_eqv base) &~ addr ** ltrue) //\\
          Q (Vptr addr) (free' ** free))))
      |-- wp_xval (Esubscript e i t) Q.


    (* the `*` operator is an lvalue *)
    Axiom wp_lval_deref : forall ty e Q,
        wp_prval e Q (* todo: rval? *)
        |-- wp_lval (Ederef e ty) Q.

    (* the `&` operator is a prvalue *)
    Axiom wp_prval_addrof : forall ty e Q,
        wp_lval e Q
        |-- wp_prval (Eaddrof e ty) Q.

    (* unary operators *)
    Axiom wp_prval_unop : forall o e ty Q,
        wp_prval e (fun v free => (* todo: rval? *)
          Exists v',
          [| eval_unop o (erase_qualifiers (type_of e)) (erase_qualifiers ty) v v' |] **
          Q v' free)
        |-- wp_prval (Eunop o e ty) Q.

    (* note(gmm): operators need types! *)
    Fixpoint companion_type (t : type) : option type :=
      match t with
      | Tpointer _ => Some (Tint int_bits Signed)
      | Tint _ _ => Some t
      | Tchar _ _ => Some t
      | Tqualified _ t => companion_type t
      | _ => None
      end.

    Axiom wp_lval_preinc : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              _at (_eqv a) (primR (erase_qualifiers ty) 1 v') **
              ( [| eval_binop Badd (erase_qualifiers (type_of e)) cty (erase_qualifiers ty) v' (Vint 1) v'' |] **
               (_at (_eqv a) (primR (erase_qualifiers ty) 1 v'') -* Q a free)))
        | None => lfalse
        end
        |-- wp_lval (Epreinc e ty) Q.

    Axiom wp_lval_predec : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              _at (_eqv a) (primR (erase_qualifiers ty) 1 v') **
              ([| eval_binop Bsub (erase_qualifiers (type_of e)) cty (erase_qualifiers ty) v' (Vint 1) v'' |] **
               (_at (_eqv a) (primR (erase_qualifiers ty) 1 v'') -* Q a free)))
        | None => lfalse
        end
        |-- wp_lval (Epredec e ty) Q.

    Axiom wp_prval_postinc : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              _at (_eqv a) (primR (erase_qualifiers ty) 1 v') **
              ([| eval_binop Badd (erase_qualifiers (type_of e)) cty (erase_qualifiers ty) v' (Vint 1) v'' |] **
              (_at (_eqv a) (primR (erase_qualifiers ty) 1 v'') -* Q v' free)))
        | None => lfalse
        end
        |-- wp_prval (Epostinc e ty) Q.

    Axiom wp_prval_postdec : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              _at (_eqv a) (primR (erase_qualifiers ty) 1 v') **
              ([| eval_binop Bsub (erase_qualifiers (type_of e)) cty (erase_qualifiers ty) v' (Vint 1) v'' |] **
               (_at (_eqv a) (primR (erase_qualifiers ty) 1 v'') -* Q v' free)))
        | None => lfalse
        end
        |-- wp_prval (Epostdec e ty) Q.

    (** binary operators *)
    Axiom wp_prval_binop : forall o e1 e2 ty Q,
        wp_prval e1 (fun v1 free1 => wp_prval e2 (fun v2 free2 =>
            Exists v',
            ([| eval_binop o (erase_qualifiers (type_of e1)) (erase_qualifiers (type_of e2)) (erase_qualifiers ty) v1 v2 v' |] ** Q v' (free1 ** free2))))
        |-- wp_prval (Ebinop o e1 e2 ty) Q.

    Axiom wp_lval_assign : forall ty l r Q,
        wp_lval l (fun la free1 => wp_prval r (fun rv free2 =>
            _at (_eqv la) (anyR (erase_qualifiers ty) 1) **
           (_at (_eqv la) (primR (erase_qualifiers ty) 1 rv) -* Q la (free1 ** free2))))
        |-- wp_lval (Eassign l r ty) Q.

    Axiom wp_lval_bop_assign : forall ty o l r Q,
        wp_lval (Eassign l (Ebinop o (Ecast Cl2r (Lvalue, l) (type_of l)) r ty) ty) Q
        |-- wp_lval (Eassign_op o l r ty) Q.

    (* note: the comma operator can be both an lvalue and a prvalue
     * depending on what the second expression is.
     * todo(gmm): the first expression can be any value category.
     *)
    Axiom wpe_comma : forall {m vc} ty e1 e2 Q,
        wpAny (vc, e1) (fun _ free1 => wpe m e2 (fun val free2 => Q val (free1 ** free2)))
        |-- wpe m (Ecomma vc e1 e2 ty) Q.

    (** short-circuting operators *)
    Axiom wp_prval_seqand : forall ty e1 e2 Q,
        wp_prval e1 (fun v1 free1 => (* todo: rval? *)
           Exists c : bool, [| is_true v1 = Some c |] **
           if c
           then wp_prval e2 (fun v2 free2 => (* todo: rval? *)
                                     Exists c : bool, [| is_true v2 = Some c |] **
                                     if c
                                     then Q (Vint 1) (free1 ** free2)
                                     else Q (Vint 0) (free1 ** free2))
           else Q (Vint 0) free1)
        |-- wp_prval (Eseqand e1 e2 ty) Q.

    Axiom wp_prval_seqor : forall ty e1 e2 Q,
        wp_prval e1 (fun v1 free1 => (* todo: rval? *)
           Exists c : bool, [| is_true v1 = Some c |] **
           if c
           then Q (Vint 1) free1
           else wp_prval e2 (fun v2 free2 => (* todo: rval? *)
                                     Exists c : bool, [| is_true v2 = Some c |] **
                                     if c
                                     then Q (Vint 1) (free1 ** free2)
                                     else Q (Vint 0) (free1 ** free2)))
        |-- wp_prval (Eseqor e1 e2 ty) Q.

    (** casts *)
    Axiom wp_prval_cast_l2r_l : forall ty e Q,
        wp_lval e (fun a free => Exists q, Exists v,
           (_at (_eqv a) (primR (erase_qualifiers ty) q v) ** ltrue) //\\
                    Q v free)
        |-- wp_prval (Ecast Cl2r (Lvalue, e) ty) Q.

    Axiom wp_prval_cast_l2r_x : forall ty e Q,
        wp_xval e (fun a free => Exists q, Exists v, (* was wp_lval *)
          (_at (_eqv a) (primR (erase_qualifiers ty) q v) ** ltrue) //\\
                    Q v free)
        |-- wp_prval (Ecast Cl2r (Xvalue, e) ty) Q.

    Axiom wp_prval_cast_noop : forall ty e Q,
        wp_prval e Q
        |-- wp_prval (Ecast Cnoop (Rvalue, e) ty) Q.
    Axiom wp_lval_cast_noop : forall ty e Q,
        wp_lval e Q
        |-- wp_lval (Ecast Cnoop (Lvalue, e) ty) Q.
    Axiom wp_xval_cast_noop : forall ty e Q,
        wp_xval e Q
        |-- wp_xval (Ecast Cnoop (Xvalue, e) ty) Q.
    Axiom wp_lval_xval_cast_noop : forall ty e Q,
        wp_xval e Q
        |-- wp_lval (Ecast Cnoop (Xvalue, e) ty) Q.
    Axiom wp_xval_lval_cast_noop : forall ty e Q,
        wp_lval e Q
        |-- wp_xval (Ecast Cnoop (Lvalue, e) ty) Q.

    Axiom wp_prval_cast_int2bool : forall ty e Q,
        wp_prval e Q
        |-- wp_prval (Ecast Cint2bool (Rvalue, e) ty) Q.
    (* ^ todo(gmm): confirm that this doesn't change the value *)

    Axiom wp_prval_cast_ptr2bool : forall ty e Q,
        wp_prval e Q
        |-- wp_prval (Ecast Cptr2bool (Rvalue, e) ty) Q.
    (* ^ todo(gmm): confirm that this doesn't change the value *)

    Axiom wp_prval_cast_function2pointer_c : forall ty ty' g Q,
        wp_lval (Evar (Gname g) ty') Q
        |-- wp_prval (Ecast Cfunction2pointer (Rvalue, Evar (Gname g) ty') ty) Q.
    Axiom wp_prval_cast_function2pointer_cpp : forall ty ty' g Q,
        wp_lval (Evar (Gname g) ty') Q
        |-- wp_prval (Ecast Cfunction2pointer (Lvalue, Evar (Gname g) ty') ty) Q.
    (* ^ note(gmm): C and C++ classify function names differently
     * - in C, function names are Rvalues, and
     * - in C++, function names are Lvalues
     *)

    Axiom wp_prval_cast_bitcast : forall e t Q,
        wp_prval e Q
        |-- wp_prval (Ecast Cbitcast (Rvalue, e) t) Q.

    Axiom wp_prval_cast_integral : forall e t Q,
        wp_prval e (fun v free => [| has_type v t |] ** Q v free)
        |-- wp_prval (Ecast Cintegral (Rvalue, e) t) Q.

    Axiom wp_prval_cast_null : forall e t Q,
        wp_prval e Q
        |-- wp_prval (Ecast Cnull2ptr (Rvalue, e) t) Q.
    (* ^ todo(jmgrosen): confirm that this doesn't change the value *)

    (* note(gmm): in the clang AST, the subexpression is the call.
     * in essence, `Ecast (Cuser ..)` is a syntax annotation.
     *)
    Axiom wp_prval_cast_user : forall e ty Z Q,
        wp_prval e Q
        |-- wp_prval (Ecast (Cuser Z) (Rvalue, e) ty) Q.

    Axiom wp_prval_cast_reinterpret : forall q e ty Q,
        wp_prval e Q
        |-- wp_prval (Ecast (Creinterpret q) (Rvalue, e) ty) Q.

    Axiom wp_lval_static_cast : forall vc from to e ty Q,
      wpe vc e (fun addr free => Exists addr',
                  (_offsetL (_super from to) (_eqv addr) &~ addr' ** ltrue) //\\
                           (* ^ this is a down-cast *)
                  Q (Vptr addr') free)
      |-- wp_lval (Ecast (Cstatic from to) (vc, e) ty) Q.

    Axiom wpe_cast_tovoid : forall vc' vc e ty Q,
      wpe vc e (fun _ free => Q (Vint 0) free)
      |-- wpe vc' (Ecast C2void (vc, e) ty) Q.

    Axiom wp_prval_cast_array2pointer : forall e t Q,
        wp_lval e Q
        |-- wp_prval (Ecast Carray2pointer (Lvalue, e) t) Q.

    Axiom wp_lval_cast_derived2base : forall e ty Q,
      wp_lval e (fun addr free => Exists addr',
        match erase_qualifiers (type_of e), erase_qualifiers ty with
          | Tnamed from, Tnamed to => (*<-- is this the only case here?*)
                  (_offsetL (_super from to) (_eqv addr) &~ addr' ** ltrue) //\\
                  Q (Vptr addr') free
          | _, _ => lfalse
        end)
        |-- wp_lval (Ecast Cderived2base (Rvalue, e) ty) Q.

    Axiom wp_prval_cast_derived2base : forall e ty Q,
      wp_prval e (fun addr free => Exists addr',
        match erase_qualifiers (type_of e), erase_qualifiers ty with
          | Tnamed from, Tnamed to
          | Tpointer (Tnamed from), Tpointer (Tnamed to) =>
                  (_offsetL (_super from to) (_eqv addr) &~ addr' ** ltrue) //\\
                  Q (Vptr addr') free
          | _, _ => lfalse
        end)
        |-- wp_prval (Ecast Cderived2base (Rvalue, e) ty) Q.

    (** the ternary operator `_ ? _ : _` *)
    Axiom wp_condition : forall ty m tst th el Q,
        wp_prval tst (fun v1 free => (* todo: rval? *)
           Exists c : bool, [| is_true v1 = Some c |] **
           if c
           then wpe m th (fun v free' => free ** Q v free')
           else wpe m el (fun v free' => free ** Q v free'))
        |-- wpe m (Eif tst th el ty) Q.

    Axiom wp_prval_implicit: forall  e Q ty,
        wp_prval e Q |-- wp_prval (Eimplicit e ty) Q.

    (** `sizeof` and `alignof` *)
    Axiom wp_prval_sizeof : forall ty' ty Q,
        Exists sz, [| size_of ty = Some sz |]  ** Q (Vint (Z.of_N sz)) empSP
        |-- wp_prval (Esize_of (inl ty) ty') Q.

    Axiom wp_prval_sizeof_e : forall ty' e Q,
        wp_prval (Esize_of (inl (type_of e)) ty') Q
        |-- wp_prval (Esize_of (inr e) ty') Q.

    Axiom wp_prval_alignof : forall ty' ty Q,
        Exists align, [| align_of ty = Some align |] ** Q (Vint (Z.of_N align)) empSP
        |-- wp_prval (Ealign_of (inl ty) ty') Q.

    Axiom wp_prval_alignof_e : forall ty' e Q,
        wp_prval (Ealign_of (inl (type_of e)) ty') Q
        |-- wp_prval (Ealign_of (inr e) ty') Q.

    (** function calls *)
    Axiom wp_prval_call : forall ty f es Q,
        (if is_aggregate ty then
          Forall addr, wp_init ty addr (Ecall f es ty) (fun free =>
            Q addr (free ** _at (_eqv addr) (anyR (erase_qualifiers ty) 1)))
        else
          wp_prval f (fun f free => wp_args es (fun vs free' =>
            |> fspec f ti vs (fun v => Q v (free ** free')))))
        |-- wp_prval (Ecall f es ty) Q.

    Axiom wp_lval_call :
      forall f (es : list (ValCat * Expr))
        Q addr (ty : type),
        wp_prval f (fun f free_f => wp_args es (fun vs free_args =>
             |> fspec f ti vs (fun res =>
                      [| res = addr |] -* Q res (free_f ** free_args))))
        |-- wp_lval (Ecall f es ty) Q.

    Axiom wp_xval_call : forall ty f es Q,
        wp_prval f (fun f free => wp_args es (fun vs free' =>
            |> fspec f ti vs (fun v => Q v (free ** free'))))
        |-- wp_xval (Ecall f es ty) Q.
    Axiom wp_init_call :
      forall f (es : list (ValCat * Expr))
        (Q : FreeTemps -> mpred) addr (ty : type),
        wp_prval f (fun f free_f => wp_args es (fun vs free_args =>
             |> fspec f ti vs (fun res =>
                      [| res = addr |] -* Q (free_f ** free_args))))
        |-- wp_init ty addr (Ecall f es ty) Q.

    Axiom wp_prval_member_call : forall ty f obj es Q,
        Exists fa, _global f &~ fa **
        wp_lval obj (fun this free => wp_args es (fun vs free' =>
            |> fspec (Vptr fa) ti (this :: vs) (fun v => Q v (free ** free'))))
        |-- wp_prval (Emember_call (inl (f, false)) obj es ty) Q.
    Axiom wp_xval_member_call : forall ty f obj es Q,
        Exists fa, _global f &~ fa **
        wp_lval obj (fun this free => wp_args es (fun vs free' =>
            |> fspec (Vptr fa) ti (this :: vs) (fun v => Q v (free ** free'))))
        |-- wp_xval (Emember_call (inl (f, false)) obj es ty) Q.
    Axiom wp_init_member_call :
      forall f (es : list (ValCat * Expr))
        (Q : FreeTemps -> mpred) addr (ty : type) obj,
        Exists fa, _global f &~ fa **
        wp_prval obj (fun this free_o => wp_args es (fun vs free_args =>
             |> fspec (Vptr fa) ti (this :: vs) (fun res =>
                      [| res = addr |] -* Q (free_o ** free_args))))
        |-- wp_init ty addr (Emember_call (inl (f, false)) obj es ty) Q.

    (* null *)
    Axiom wp_null : forall Q,
        Q (Vptr nullptr) empSP
        |-- wp_prval Enull Q.

    (* temporary expressions
     * note(gmm): these axioms should be reviewed thoroughly
     *)
    Axiom wp_lval_clean : forall e ty Q,
        wp_lval e Q |-- wp_lval (Eandclean e ty) Q.
    Axiom wp_prval_clean : forall e ty Q,
        wp_prval e Q |-- wp_prval (Eandclean e ty) Q.
    Axiom wp_xval_clean : forall e ty Q,
        wp_xval e Q |-- wp_xval (Eandclean e ty) Q.

    (* [Ematerialize_temp e ty] is an xvalue
     *)
    Axiom wp_xval_temp : forall e ty Q,
        (Forall a, _at (_eqv a) (uninitR (erase_qualifiers ty) 1) -*
                  let '(e,dt) := destructor_for e in
                  wp_init ty a e
                          (fun free => Q a (mdestroy ti ty a dt free)))
        |-- wp_xval (Ematerialize_temp e ty) Q.

    (* [Ematerialize_temp e ty] is an xvalue
     *)
    Axiom wp_lval_temp : forall e ty Q,
        (Forall a,
           _at (_eqv a) (uninitR (erase_qualifiers ty) 1) -*
           let '(e,dt) := destructor_for e in
           wp_init ty a e
                   (fun free => Q a (mdestroy ti ty a dt free)))
        |-- wp_lval (Ematerialize_temp e ty) Q.

    (* temporary materialization only occurs when the resulting value is used.
     * if the value is ignored, e.g. in `go();` (when the result of `go` is an
     * aggregate) we introduce an implicit materialization and then immediately
     * free the result.
     *)
    Axiom wp_prval_implicit_materialize : forall e Q,
        is_aggregate (type_of e) = true ->
        (let ty := erase_qualifiers (type_of e) in
         Forall a, _at (_eqv a) (uninitR ty 1) -*
                   let '(e,dt) := destructor_for e in
                   wp_init ty a e (fun free =>
                                     Q a (mdestroy ti ty a dt free)))
        |-- wp_prval e Q.


    (* [Ebind_temp e dtor ty] is an initialization expression that ensures
     * that the destructor is called.
     *
     * this aspect of the AST is non-compositional, so we handle it in another
     * way
     *)
    Axiom wp_init_bind_temp : forall e ty a dtor Q,
        lfalse (*
        wp_init ty a e (fun free =>
                     Exists fa, [| glob_addr resolve dtor fa |] **
                     |> fspec (Vptr fa) (a :: nil) ti (fun _ => Q free)) *)
        |-- wp_init ty a (Ebind_temp e dtor ty) Q.

    Axiom wp_prval_materialize : forall ty e dtor Q,
      Forall a : val,
      _at (_eqv a) (uninitR (erase_qualifiers ty) 1) -*
          wp_init ty a e (fun free =>
                            Q a (mdestroy ti ty a (Some dtor) free))
      |-- wp_prval (Ebind_temp e dtor ty) Q.

    Axiom wp_pseudo_destructor : forall e ty Q,
        wp_prval e Q
        |-- wp_prval (Epseudo_destructor ty e) Q.

  End with_resolve.

End Expr.

Declare Module E : Expr.

Export E.
