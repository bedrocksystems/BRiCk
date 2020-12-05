(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
(**
 * Semantics of expressions
 * (expressed in weakest pre-condition style)
 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNatDef.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred
     operator
     destroy
     wp call
     translation_unit
     dispatch.

Module Type Expr.

  Coercion Vint : Z >-> val.
  Coercion Z.of_N : N >-> Z.
  Definition El2r := Ecast Cl2r.

  (**
   * Weakest pre-condition for expressions
   *)

  Section with_resolve.
    Context `{Σ : cpp_logic thread_info} {resolve:genv}.
    Variables (M : coPset) (ti : thread_info) (ρ : region).

    Local Notation wp_lval := (wp_lval (resolve:=resolve) M ti ρ).
    Local Notation wp_prval := (wp_prval (resolve:=resolve) M ti ρ).
    Local Notation wp_xval := (wp_xval (resolve:=resolve) M ti ρ).
    Local Notation wp_glval := (wp_glval (resolve:=resolve) M ti ρ).
    Local Notation wp_rval := (wp_rval (resolve:=resolve) M ti ρ).
    Local Notation wp_init := (wp_init (resolve:=resolve) M ti ρ).
    Local Notation wp_args := (wp_args (σ:=resolve) M ti ρ).
    Local Notation fspec := (fspec resolve.(genv_tu).(globals)).
    Local Notation destruct_val := (destruct_val (σ:=resolve) ti) (only parsing).

    Local Notation glob_def := (glob_def resolve) (only parsing).
    Local Notation _global := (_global (resolve:=resolve)) (only parsing).
    Local Notation _field := (_field (resolve:=resolve)) (only parsing).
    Local Notation _base := (_base (resolve:=resolve)) (only parsing).
    Local Notation _derived := (_derived (resolve:=resolve)) (only parsing).
    Local Notation _sub := (_sub (resolve:=resolve)) (only parsing).
    Local Notation eval_unop := (@eval_unop resolve) (only parsing).
    Local Notation eval_binop := (eval_binop (resolve := resolve)) (only parsing).
    Local Notation size_of := (@size_of resolve) (only parsing).
    Local Notation align_of := (@align_of resolve) (only parsing).
    Local Notation primR := (primR (resolve:=resolve)) (only parsing).
    Local Notation anyR := (anyR (resolve:=resolve)) (only parsing).
    Local Notation tblockR := (tblockR (σ:=resolve)) (only parsing).
    Local Notation uninitR := (uninitR (resolve:=resolve)) (only parsing).
    Local Notation blockR := (blockR (σ:=resolve)) (only parsing).

    (* constants are rvalues *)
    Axiom wp_prval_constant : forall ty cnst e Q,
      glob_def cnst = Some (Gconstant ty (Some e)) ->
      wp_prval e Q
      |-- wp_prval (Econst_ref (Gname cnst) ty) Q.

    (* integer literals are prvalues *)
    Axiom wp_prval_int : forall n ty Q,
      [! has_type (Vint n) (drop_qualifiers ty) !] //\\ Q (Vint n) emp
      |-- wp_prval (Eint n ty) Q.

    (* note that `char` is actually `byte` *)
    Axiom wp_prval_char : forall c ty Q,
      [! has_type (Vint c) (drop_qualifiers ty) !] //\\ Q (Vint c) emp
      |-- wp_prval (Echar c ty) Q.

    (* boolean literals are prvalues *)
    Axiom wp_prval_bool : forall (b : bool) Q,
      Q (Vbool b) emp
      |-- wp_prval (Ebool b) Q.

    (* `this` is a prvalue *)
    Axiom wp_prval_this : forall ty Q,
      Exists a, (_this ρ &~ a ** True) //\\ Q (Vptr a) emp
      |-- wp_prval (Ethis ty) Q.


    (* variables are lvalues *)
    Axiom wp_lval_lvar : forall ty x Q,
        Exists a, (_local ρ x &~ a ** True) //\\ Q a emp
        |-- wp_lval (Evar (Lname x) ty) Q.

    (* what about the type? if it exists *)
    Axiom wp_lval_gvar : forall ty x Q,
        Exists a, (_global x &~ a ** True) //\\ Q a emp
        |-- wp_lval (Evar (Gname x) ty) Q.

    (* [Emember a f ty] is an lvalue by default except when
     * - where [m] is a member enumerator or a non-static member function, or
     * - where [a] is an rvalue and [m] is a non-static data member of non-reference type
     *
     * note: we need [vc] in order to distinguish the two forms of [rvalue], [xvalue] and [prvalue]
     *)
    Axiom wp_lval_member : forall ty vc a m Q,
        match vc with
        | Prvalue => False
        | Lvalue =>
          wp_lval a (fun base free =>
                       Exists addr, (_offsetL (_field m) (_eq base) &~ addr ** True) //\\ Q addr free)
        | Xvalue => False
          (* NOTE If the object is a temporary, then the field access will also be a
             temporary. Being conservative is sensible in our semantic style.
          *)
        end
      |-- wp_lval (Emember vc a m ty) Q.


    (* [Emember a m ty] is a prvalue if
     * - [a] is a member enumerator or non-static member function, or
     * - [a] is an rvalue and [m] is non-static data of non-reference type
     TODO: consider requiring (1) [type_ptr] (2) [valid_live_ptr], here and
     elsewhere; most operations in the standard are described in terms of
     objects, which restricts them to _live_ objects.
     *)
    Axiom wp_prval_member : forall ty vc a m Q,
        match vc with
        | Prvalue => False
          (* As above, this doesn't seem to exist because our AST explicitly contains
             [Cl2r] casts.
           *)
        | _ => False
        end
      |-- wp_prval (Emember vc a m ty) Q.

    (* [Emember a m ty] is an xvalue if
     * - [a] is an rvalue and [m] is a non-static data member of non-reference type
     *)
    Axiom wp_xval_member : forall ty vc a m Q,
        match vc with
        | Prvalue => False
          (* As above, this doesn't exist because our AST explicitly contains [Cl2r] casts.
           *)
        | Xvalue =>
          wp_xval a (fun base free =>
            Exists addr, (_offsetL (_field m) (_eq base) &~ addr ** True) //\\ Q addr free)
        | _ => False
        end%I
      |-- wp_xval (Emember vc a m ty) Q.

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
      (Exists Qbase Qidx,
       (if is_pointer (type_of e) then
         wp_prval e Qbase ** wp_prval i Qidx
       else
         wp_prval e Qidx ** wp_prval i Qbase) **
      Forall base free idx free',
         Qbase base free -* Qidx idx free' -*
         Exists addr,
          (Exists i, [| idx = Vint i |] **
          _offsetL (_sub (erase_qualifiers t) i) (_eqv base) &~ addr ** ltrue) //\\
          Q addr (free' ** free))
      |-- wp_lval (Esubscript e i t) Q.

    (* [Esubscript e i t]
     * - where one operand is an array rvalue
     *)
    Axiom wp_xval_subscript : forall e i t Q,
      (Exists Qbase Qidx,
       (if is_pointer (type_of e) then
         wp_prval e Qbase ** wp_prval i Qidx
       else
         wp_prval e Qidx ** wp_prval i Qbase) **
      Forall base free idx free',
         Qbase base free -* Qidx idx free' -*
          (* TODO: here and elsewhere, consider avoiding locations and switching to *)
          (* (Exists i basep, [| idx = Vint i /\ base = Vptr basep |] **
            ((valid_ptr (basep .., o_sub resolve (erase_qualifiers t) i) ** True) //\\
            Q (Vptr (basep .., o_sub resolve (erase_qualifiers t) i)) (free' ** free)))) *)
         Exists addr,
          (Exists i, [| idx = Vint i |] **
          _offsetL (_sub (erase_qualifiers t) i) (_eqv base) &~ addr ** ltrue) //\\
          Q addr (free' ** free))
      |-- wp_xval (Esubscript e i t) Q.

          (* valid_ptr base *)

    (* the `*` operator is an lvalue *)
    Axiom wp_lval_deref : forall ty e Q,
        wp_prval e (fun v free =>
                      match v with
                      | Vptr p => Q p free
                      | _ => False
                      end)
        |-- wp_lval (Ederef e ty) Q.

    (* the `&` operator is a prvalue *)
    Axiom wp_prval_addrof : forall ty e Q,
        wp_lval e (fun p free => Q (Vptr p) free)
        |-- wp_prval (Eaddrof e ty) Q.

    (* unary operators *)
    (* NOTE the following axioms assume that [eval_unop] is deterministic when it is defined *)
    Axiom wp_prval_unop : forall o e ty Q,
        wp_prval e (fun v free => (* todo: rval? *)
          Exists v',
          [| eval_unop o (erase_qualifiers (type_of e)) (erase_qualifiers ty) v v' |] **
          Q v' free)
        |-- wp_prval (Eunop o e ty) Q.

    Axiom wp_lval_preinc : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              (eval_binop Badd (erase_qualifiers (type_of e)) cty
                (erase_qualifiers ty) v' (Vint 1) v'' ** True) //\\
              (_at (_eq a) (primR (erase_qualifiers ty) 1 v') **
                (_at (_eq a) (primR (erase_qualifiers ty) 1 v'') -* Q a free)))
        | None => False
        end
        |-- wp_lval (Epreinc e ty) Q.

    Axiom wp_lval_predec : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              (eval_binop Bsub (erase_qualifiers (type_of e)) cty
                (erase_qualifiers ty) v' (Vint 1) v'' ** True) //\\
              (_at (_eq a) (primR (erase_qualifiers ty) 1 v') **
                (_at (_eq a) (primR (erase_qualifiers ty) 1 v'') -* Q a free)))
        | None => False
        end
        |-- wp_lval (Epredec e ty) Q.

    Axiom wp_prval_postinc : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              (eval_binop Badd (erase_qualifiers (type_of e)) cty
                (erase_qualifiers ty) v' (Vint 1) v'' ** True) //\\
              (_at (_eq a) (primR (erase_qualifiers ty) 1 v') **
                (_at (_eq a) (primR (erase_qualifiers ty) 1 v'') -* Q v' free)))
        | None => False
        end
        |-- wp_prval (Epostinc e ty) Q.

    Axiom wp_prval_postdec : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              (eval_binop Bsub (erase_qualifiers (type_of e)) cty
                (erase_qualifiers ty) v' (Vint 1) v'' ** True) //\\
              (_at (_eq a) (primR (erase_qualifiers ty) 1 v') **
                (_at (_eq a) (primR (erase_qualifiers ty) 1 v'') -* Q v' free)))
        | None => False
        end
        |-- wp_prval (Epostdec e ty) Q.

    (** binary operators *)
    (* NOTE the following axioms assume that [eval_binop] is deterministic *)
    Axiom wp_prval_binop : forall o e1 e2 ty Q,
        (Exists Ql Qr,
        wp_prval e1 Ql ** wp_prval e2 Qr **
            Forall v1 v2 free1 free2, Ql v1 free1 -* Qr v2 free2 -*
               Exists v',
                  (eval_binop o
                    (erase_qualifiers (type_of e1)) (erase_qualifiers (type_of e2))
                    (erase_qualifiers ty) v1 v2 v' ** True) //\\
                  Q v' (free1 ** free2))
        |-- wp_prval (Ebinop o e1 e2 ty) Q.

    (* NOTE the right operand is sequenced before the left operand in C++20,
       check when this started. (cppreference.com doesn't seem to have this information)
     *)
    Axiom wp_lval_assign : forall ty l r Q,
        (Exists Ql Qr,
         wp_lval l Ql ** wp_prval r Qr **
         Forall la free1 rv free2, Ql la free1 -* Qr rv free2 -*
            _at (_eq la) (anyR (erase_qualifiers ty) 1) **
           (_at (_eq la) (primR (erase_qualifiers ty) 1 rv) -* Q la (free1 ** free2)))
        |-- wp_lval (Eassign l r ty) Q.

    (* TODO this is wrong *)
    Axiom wp_lval_bop_assign : forall ty o l r Q,
        (Exists Ql Qr,
        wp_lval l Ql ** wp_prval r Qr **
        Forall la free1 rv free2, Ql la free1 -* Qr rv free2 -*
             (Exists v v', _at (_eq la) (primR (erase_qualifiers ty) 1 v) **
                 ((eval_binop o (erase_qualifiers (type_of l)) (erase_qualifiers (type_of r)) (erase_qualifiers (type_of l)) v rv v' ** True) //\\
                 (_at (_eq la) (primR (erase_qualifiers ty) 1 v') -* Q la (free1 ** free2)))))
        |-- wp_lval (Eassign_op o l r ty) Q.

    (* evaluate an expression but ignore the result

    XXX this is duplicated from stmt.v
     *)
    Definition wpAny_ignore (vc : ValCat) (e : Expr) (Q : FreeTemps -> mpred) : mpred :=
      match vc with
      | Prvalue => wp_prval e (fun _ => Q)
      | Lvalue => wp_lval e (fun _ => Q)
      | Xvalue => wp_xval e (fun _ => Q)
      end.

    (* The comma operator can be both an lvalue and a prvalue
     * depending on what the second expression is.
     *)
    Axiom wp_lval_comma : forall {vc} ty e1 e2 Q,
        wpAny_ignore vc e1 (fun free1 => wp_lval e2 (fun val free2 => Q val (free1 ** free2)))
        |-- wp_lval (Ecomma vc e1 e2 ty) Q.

    Axiom wp_xval_comma : forall {vc} ty e1 e2 Q,
        wpAny_ignore vc e1 (fun free1 => wp_xval e2 (fun val free2 => Q val (free1 ** free2)))
        |-- wp_xval (Ecomma vc e1 e2 ty) Q.

    Axiom wp_prval_comma : forall {vc} ty e1 e2 Q,
        wpAny_ignore vc e1 (fun free1 => wp_prval e2 (fun val free2 => Q val (free1 ** free2)))
        |-- wp_prval (Ecomma vc e1 e2 ty) Q.

    Axiom wp_init_comma : forall {vc} ty' ty p e1 e2 Q,
        wpAny_ignore vc e1 (fun free1 => wp_init ty' p e2 (fun free2 => Q (free1 ** free2)))
        |-- wp_init ty' p (Ecomma vc e1 e2 ty) Q.

    (** short-circuting operators *)
    Axiom wp_prval_seqand : forall ty e1 e2 Q,
        wp_prval e1 (fun v1 free1 =>
        (* ^ note: technically an rvalue, but it must be a primitive,
           otherwise there will be an implicit cast to bool, to it is
           always an rvalue *)
           Exists c : bool, [| is_true v1 = Some c |] **
           if c
           then wp_prval e2 (fun v2 free2 => (* see comment above *)
                                     Exists c : bool, [| is_true v2 = Some c |] **
                                     if c
                                     then Q (Vint 1) (free1 ** free2)
                                     else Q (Vint 0) (free1 ** free2))
           else Q (Vint 0) free1)
        |-- wp_prval (Eseqand e1 e2 ty) Q.

    Axiom wp_prval_seqor : forall ty e1 e2 Q,
        wp_prval e1 (fun v1 free1 =>
        (* ^ note: technically an rvalue, but it must be a primitive,
           otherwise there will be an implicit cast to bool, to it is
           always an rvalue *)
           Exists c : bool, [| is_true v1 = Some c |] **
           if c
           then Q (Vint 1) free1
           else wp_prval e2 (fun v2 free2 => (* see comment above *)
                                     Exists c : bool, [| is_true v2 = Some c |] **
                                     if c
                                     then Q (Vint 1) (free1 ** free2)
                                     else Q (Vint 0) (free1 ** free2)))
        |-- wp_prval (Eseqor e1 e2 ty) Q.

    (** casts *)
    Axiom wp_prval_cast_l2r_l : forall ty e Q,
        wp_lval e (fun a free => Exists q, Exists v,
           (_at (_eq a) (primR (erase_qualifiers ty) q v) ** True) //\\
                    Q v free)
        |-- wp_prval (Ecast Cl2r (Lvalue, e) ty) Q.

    Axiom wp_prval_cast_l2r_x : forall ty e Q,
        wp_xval e (fun a free => Exists q, Exists v, (* was wp_lval *)
          (_at (_eq a) (primR (erase_qualifiers ty) q v) ** True) //\\
                    Q v free)
        |-- wp_prval (Ecast Cl2r (Xvalue, e) ty) Q.

    (** [Cnoop] casts are no-op casts. *)
    Axiom wp_prval_cast_noop : forall ty e Q,
        wp_prval e Q
        |-- wp_prval (Ecast Cnoop (Prvalue, e) ty) Q.
    Axiom wp_lval_cast_noop : forall ty e Q,
        wp_lval e Q
        |-- wp_lval (Ecast Cnoop (Lvalue, e) ty) Q.
    Axiom wp_xval_cast_noop : forall ty e Q,
        wp_xval e Q
        |-- wp_xval (Ecast Cnoop (Xvalue, e) ty) Q.

    (* note: this is the cast that occurs for the implementation of
     * [std::move]
     *)
    Axiom wp_lval_xval_cast_noop : forall ty e Q,
        wp_xval e Q
        |-- wp_lval (Ecast Cnoop (Xvalue, e) ty) Q.
    Axiom wp_xval_lval_cast_noop : forall ty e Q,
        wp_lval e Q
        |-- wp_xval (Ecast Cnoop (Lvalue, e) ty) Q.

    Axiom wp_prval_cast_int2bool : forall ty e Q,
        wp_prval e (fun v free =>
                      match is_true v with
                      | None => False
                      | Some v => Q (Vbool v) free
                      end)
        |-- wp_prval (Ecast Cint2bool (Prvalue, e) ty) Q.

    Axiom wp_prval_cast_ptr2bool : forall ty e Q,
        wp_prval e (fun v free =>
                      match is_true v with
                      | None => False
                      | Some v => Q (Vbool v) free
                      end)
        |-- wp_prval (Ecast Cptr2bool (Prvalue, e) ty) Q.

    (* [Cfunction2pointer] is a cast from a function to a pointer.
     *
     * note that C and C++ classify function names differently, so we
     * end up with two cases
     * - in C, function names are Rvalues, and
     * - in C++, function names are Lvalues
     *)
    Axiom wp_prval_cast_function2pointer_c : forall ty ty' g Q,
        wp_lval (Evar (Gname g) ty') (fun v => Q (Vptr v))
        |-- wp_prval (Ecast Cfunction2pointer (Prvalue, Evar (Gname g) ty') ty) Q.
    Axiom wp_prval_cast_function2pointer_cpp : forall ty ty' g Q,
        wp_lval (Evar (Gname g) ty') (fun v => Q (Vptr v))
        |-- wp_prval (Ecast Cfunction2pointer (Lvalue, Evar (Gname g) ty') ty) Q.

    (** **)
    Axiom wp_prval_cast_bitcast : forall e t Q,
        wp_prval e Q
        |-- wp_prval (Ecast Cbitcast (Prvalue, e) t) Q.

    Axiom wp_prval_cast_integral : forall e t Q,
        wp_prval e (fun v free =>
           Exists v', [| conv_int (type_of e) t v v' |] ** Q v' free)
        |-- wp_prval (Ecast Cintegral (Prvalue, e) t) Q.

    Axiom wp_prval_cast_null : forall e t Q,
        wp_prval e Q
        |-- wp_prval (Ecast Cnull2ptr (Prvalue, e) t) Q.

    (* note(gmm): in the clang AST, the subexpression is the call.
     * in essence, [Ecast (Cuser ..)] is a syntax annotation.
     *)
    Axiom wp_prval_cast_user : forall e ty Z Q,
        wp_prval e Q
        |-- wp_prval (Ecast (Cuser Z) (Prvalue, e) ty) Q.


    (** TODO there is a lot of subtlety around [reinterpret_cast]
     *)
    Axiom wp_prval_cast_reinterpret : forall q e ty Q,
        wp_prval e Q
        |-- wp_prval (Ecast (Creinterpret q) (Prvalue, e) ty) Q.

    (* [Cstatic from to] represents a static cast from [from] to
     * [to].
     *
     * TODO this rule needs to be cleaned up a lot
     *)
    (*
    Axiom wp_lval_static_cast : forall vc from to e ty Q,
      wpe vc e (fun addr free => Exists addr',
                  (_offsetL (_base from to) (_eqv addr) &~ addr' ** ltrue) //\\
                           (* ^ this is a down-cast *)
                  Q (Vptr addr') free)
      |-- wp_lval (Ecast (Cstatic from to) (vc, e) ty) Q.
     *)

    (** You can cast anything to void, but an expression of type
     * [void] can only be a pr_value *)
    Axiom wpe_cast_tovoid : forall vc e Q,
        wpAny_ignore vc e (fun free => Q (Vint 0) free)
      |-- wp_prval (Ecast C2void (vc, e) Tvoid) Q.

    Axiom wp_prval_cast_array2pointer : forall e t Q,
        wp_lval e (fun p => Q (Vptr p))
        |-- wp_prval (Ecast Carray2pointer (Lvalue, e) t) Q.

    (** [Cint2pointer] exposes the pointer, which is expressed with [pinned_ptr]
     *)
    Axiom wp_prval_int2pointer : forall e ty Q,
        match drop_qualifiers ty with
        | Tptr _ =>
          wp_prval e (fun v free => Exists p, [| v = Vptr p |] **
                        (Forall va, pinned_ptr va p -* Q (Vint va) free))
        | _ => False
        end
        |-- wp_prval (Ecast Cint2pointer (Prvalue, e) ty) Q.

    (** [Cpointer2int] uses "angelic non-determinism" to allow the developer to
        pick any pointer that was previously exposed as the given integer.

        TODO the pointer that is picked *must* have the correct type, but this is
        currently not stated in the rule below.
     *)
    Axiom wp_prval_pointer2int : forall e ty Q,
        wp_prval e (fun v free => Exists va : N, [| v = Vint (Z.of_N va) |] **
           (([| (va > 0)%N |] ** Exists p, pinned_ptr va p ** Q (Vptr p) free) \\//
            ([| va = 0%N |] ** Q (Vptr nullptr) free)))
        |-- wp_prval (Ecast Cpointer2int (Prvalue, e) ty) Q.

    (** [Cderived2base] casts from a derived class to a base
     * class. Casting is only permitted on pointers and references
     * - references occur with lvalues and xvalues
     * - pointers occur with prvalues
     *
     * TODO [_base] only supports casting up a single level of the
     * heirarchy at a time, so we need to construct a full path.
     *)
    Axiom wp_lval_cast_derived2base : forall e ty Q,
      wp_lval e (fun addr free => Exists addr',
        match drop_qualifiers (type_of e), drop_qualifiers ty with
        | Tnamed from, Tnamed to => (*<-- is this the only case here?*)
          (_offsetL (_base from to) (_eq addr) &~ addr' ** True) //\\
          Q addr' free
        | _, _ => False
        end)
      |-- wp_lval (Ecast Cderived2base (Lvalue, e) ty) Q.

    Axiom wp_xval_cast_derived2base : forall e ty Q,
      wp_xval e (fun addr free => Exists addr',
        match drop_qualifiers (type_of e), drop_qualifiers ty with
        | Tnamed from, Tnamed to => (*<-- is this the only case here?*)
          (_offsetL (_base from to) (_eq addr) &~ addr' ** True) //\\
          Q addr' free
        | _, _ => False
        end)
      |-- wp_xval (Ecast Cderived2base (Xvalue, e) ty) Q.

    Axiom wp_prval_cast_derived2base : forall e ty Q,
      wp_prval e (fun addr free => Exists addr',
        match erase_qualifiers (type_of e), erase_qualifiers ty with
        | Tpointer (Tnamed from), Tpointer (Tnamed to) =>
          (_offsetL (_base from to) (_eqv addr) &~ addr' ** True) //\\
          Q (Vptr addr') free
        | _, _ => False
        end)
      |-- wp_prval (Ecast Cderived2base (Prvalue, e) ty) Q.

    (* [Cbase2derived] casts from a base class to a derived class.
     *)
    Axiom wp_lval_cast_base2derived : forall e ty Q,
      wp_lval e (fun addr free => Exists addr',
        match erase_qualifiers (type_of e), erase_qualifiers ty with
        | Tnamed from, Tnamed to => (*<-- is this the only case here?*)
          (_offsetL (_derived from to) (_eq addr) &~ addr' ** True) //\\
          Q addr' free
        | _, _ => False
        end)
      |-- wp_lval (Ecast Cbase2derived (Lvalue, e) ty) Q.

    Axiom wp_xval_cast_base2derived : forall e ty Q,
      wp_xval e (fun addr free => Exists addr',
        match erase_qualifiers (type_of e), erase_qualifiers ty with
        | Tnamed from, Tnamed to => (*<-- is this the only case here?*)
          (_offsetL (_derived from to) (_eq addr) &~ addr' ** True) //\\
          Q addr' free
        | _, _ => False
        end)
      |-- wp_xval (Ecast Cbase2derived (Xvalue, e) ty) Q.

    Axiom wp_prval_cast_base2derived : forall e ty Q,
      wp_prval e (fun addr free => Exists addr',
        match erase_qualifiers (type_of e), erase_qualifiers ty with
        | Tpointer (Tnamed from), Tpointer (Tnamed to) =>
          (_offsetL (_derived from to) (_eqv addr) &~ addr' ** True) //\\
          Q (Vptr addr') free
        | _, _ => False
        end)
      |-- wp_prval (Ecast Cbase2derived (Prvalue, e) ty) Q.

    (** the ternary operator [_ ? _ : _] has the value category
     * of the "then" and "else" expressions (which must be the same).
     * We express this with 4 rules, one for each of [wp_lval],
     * [wp_prval], [wp_xval], and [wp_init].
     *)
    Definition wp_cond {T} wp : Prop :=
      forall ty tst th el (Q : T -> FreeTemps -> mpred),
        wp_prval tst (fun v1 free =>
           Exists c : bool, [| is_true v1 = Some c |] **
           if c
           then wp th (fun v free' => free ** Q v free')
           else wp el (fun v free' => free ** Q v free'))
        |-- wp (Eif tst th el ty) Q.

    Axiom wp_lval_condition :
      ltac:(let v := eval unfold wp_cond in (wp_cond wp_lval) in
                exact v).
    Axiom wp_xval_condition :
      ltac:(let v := eval unfold wp_cond in (wp_cond wp_xval) in
            exact v).
    Axiom wp_prval_condition :
      ltac:(let v := eval unfold wp_cond in (wp_cond wp_prval) in
                exact v).
    Axiom wp_init_condition : forall ty ty' addr tst th el Q,
        wp_prval tst (fun v1 free =>
           Exists c : bool, [| is_true v1 = Some c |] **
           if c
           then wp_init ty addr th (fun free' => free ** Q free')
           else wp_init ty addr el (fun free' => free ** Q free'))
        |-- wp_init ty addr (Eif tst th el ty') Q.

    Axiom wp_prval_implicit: forall  e Q ty,
        wp_prval e Q |-- wp_prval (Eimplicit e ty) Q.

    (** [sizeof] and [alignof] do not evaluate their arguments *)
    Axiom wp_prval_sizeof : forall ty' ty Q,
        Exists sz, [| size_of ty = Some sz |]  ** Q (Vint (Z.of_N sz)) emp
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

    Definition unptr (t : type) : option type :=
      match drop_qualifiers t with
      | Tptr p => Some (drop_qualifiers p)
      | _ => None
      end.

    (** function calls *)
    (**
    The next few axioms rely on the evaluation order specified
    since C++17 (implemented in Clang >= 4):
    to evaluate [f(args)], [f] is evaluated before [args].

    Summary of the change: https://stackoverflow.com/a/38798487/53974.
    Official references (from http://clang.llvm.org/cxx_status.html):
    http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2016/p0400r0.html
    http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2016/p0145r3.pdf
    *)
    Axiom wp_prval_call : forall ty f es Q,
        (if is_aggregate ty then
           Forall addr, wp_init ty addr (Ecall f es ty) (fun free =>
                Q (Vptr addr) (free ** destruct_val (erase_qualifiers ty) addr None (_at (_eq addr) (tblockR ty))))
             (* XXX This use of [Vptr] represents an aggregate.
                XXX The destruction of the value isn't quite correct because we explicitly
                    generate the destructors.
              *)
         else
           match unptr (type_of f) with
           | Some fty =>
             wp_prval f (fun f free_f => wp_args es (fun vs free =>
                                                      |> fspec fty ti f vs (fun v => Q v (free ** free_f))))
           | _ => False
           end)
        |-- wp_prval (Ecall f es ty) Q.

    Axiom wp_lval_call : forall f (es : list (ValCat * Expr)) Q (ty : type),
        match unptr (type_of f) with
        | Some fty =>
          wp_prval f (fun f free_f => wp_args es (fun vs free =>
                        |> fspec fty ti f vs (fun res => Exists p, [| res = Vptr p |] ** Q p (free ** free_f))))
        | _ => False
        end
        |-- wp_lval (Ecall f es ty) Q.

    Axiom wp_xval_call : forall ty f es Q,
        match unptr (type_of f) with
        | Some fty =>
          wp_prval f (fun f free_f => wp_args es (fun vs free =>
                           |> fspec fty ti f vs (fun v => Exists p, [| v = Vptr p |] ** Q p (free ** free_f))))
        | _ => False
        end
      |-- wp_xval (Ecall f es ty) Q.

    Axiom wp_init_call : forall f es Q addr ty,
        match unptr (type_of f) with
        | Some fty =>
          wp_prval f (fun f free_f => wp_args es (fun vs free =>
                           |> fspec fty ti f vs (fun res => [| res = Vptr addr |] -* Q (free_f ** free))))
          (* NOTE We use the assumed equality to mean that the value was constructed immediately into
             the correct place *)
        | _ => False
        end
        |-- wp_init ty addr (Ecall f es ty) Q.

    Definition wp_specific_glval (vc : ValCat) (e : Expr) : (ptr -> FreeTemps -> mpred) -> mpred :=
      match vc with
      | Lvalue => wp_lval e
      | Xvalue => wp_xval e
      | _ => fun _ => False
      end%I.

    (** member call *)
    Axiom wp_lval_member_call : forall ty fty f vc obj es Q,
        Exists fa, _global f &~ fa **
        wp_specific_glval vc obj (fun this free_t => wp_args es (fun vs free =>
           |> fspec fty ti (Vptr fa) (Vptr this :: vs) (fun v =>
                    Exists p, [| v = Vptr p |] ** Q p (free_t ** free))))
        |-- wp_lval (Emember_call (inl (f, Direct, fty)) vc obj es ty) Q.

    Axiom wp_xval_member_call : forall ty fty f vc obj es Q,
        Exists fa, _global f &~ fa **
        wp_specific_glval vc obj (fun this free_t => wp_args es (fun vs free =>
           |> fspec fty ti (Vptr fa) (Vptr this :: vs) (fun v =>
                    Exists p, [| v = Vptr p |] ** Q p (free_t ** free))))
        |-- wp_xval (Emember_call (inl (f, Direct, fty)) vc obj es ty) Q.

    Axiom wp_prval_member_call : forall ty fty f vc obj es Q,
          Exists fa, _global f &~ fa **
          wp_specific_glval vc obj (fun this free_t => wp_args es (fun vs free =>
              |> fspec fty ti (Vptr fa) (Vptr this :: vs) (fun v => Q v (free_t ** free))))
        |-- wp_prval (Emember_call (inl (f, Direct, fty)) vc obj es ty) Q.

    Axiom wp_init_member_call : forall f fty es addr ty vc obj Q,
        Exists fa, _global f &~ fa **
        wp_specific_glval vc obj (fun this free_t => wp_args es (fun vs free =>
             |> fspec fty ti (Vptr fa) (Vptr this :: vs) (fun res =>
                      [| res = Vptr addr |] -* Q (free_t ** free))))
        (* NOTE as with regular function calls, we use an assumed equation to unify the address
           of the returned object with the location that we are initializing.
         *)
        |-- wp_init ty addr (Emember_call (inl (f, Direct, fty)) vc obj es ty) Q.

    (** TODO move this *)
    Fixpoint class_type (t : type) : option globname :=
      match t with
      | Tnamed gn => Some gn
      | Tpointer t
      | Treference t
      | Trv_reference t => class_type t
      | Tqualified _ t => class_type t
      | _ => None
      end.

    (** virtual functions
        these are slightly more complex because we need to compute the address of the function
        using the most-derived-class of the [this] object. This is done using [resolve_virtual].

        NOTE The [resolve_virtual] below means that caller justifies the cast to the dynamic type.
             This is necessary because the function is expecting the correct [this] pointer.
     *)
    Axiom wp_xval_virtual_call : forall ty fty f vc obj es Q, 
      wp_specific_glval vc obj (fun this free => wp_args es (fun vs free' =>
          match class_type (type_of obj) with
          | Some cls =>
            resolve_virtual (σ:=resolve) (_eq this) cls f (fun fimpl_addr thisp =>
              |> fspec fty ti (Vptr fimpl_addr) (Vptr thisp :: vs) (fun v =>
                       Exists p, [| v = Vptr p |] ** Q p (free ** free')))
          | _ => False
          end))
      |-- wp_xval (Emember_call (inl (f, Virtual, fty)) vc obj es ty) Q.

    Axiom wp_lval_virtual_call : forall ty fty f vc obj es Q,
      wp_specific_glval vc obj (fun this free => wp_args es (fun vs free' =>
          match class_type (type_of obj) with
          | Some cls =>
            resolve_virtual (σ:=resolve) (_eq this) cls f (fun fimpl_addr thisp =>
              |> fspec fty ti (Vptr fimpl_addr) (Vptr thisp :: vs) (fun v =>
                       Exists p, [| v = Vptr p |] ** Q p (free ** free')))
          | _ => False
          end))
      |-- wp_lval (Emember_call (inl (f, Virtual, fty)) vc obj es ty) Q.

    Axiom wp_prval_virtual_call : forall ty fty f vc obj es Q,
      wp_specific_glval vc obj (fun this free => wp_args es (fun vs free' =>
          match class_type (type_of obj) with
          | Some cls =>
            resolve_virtual (σ:=resolve) (_eq this) cls f (fun fimpl_addr thisp =>
              |> fspec fty ti (Vptr fimpl_addr) (Vptr thisp :: vs) (fun v => Q v (free ** free')))
         | _ => False
          end))
      |-- wp_prval (Emember_call (inl (f, Virtual, fty)) vc obj es ty) Q.

    Axiom wp_init_virtual_call : forall ty fty f vc obj es Q addr,
      wp_specific_glval vc obj (fun this free => wp_args es (fun vs free' =>
          match class_type (type_of obj) with
          | Some cls =>
            resolve_virtual (σ:=resolve) (_eq this) cls f (fun fimpl_addr thisp =>
              |> fspec fty ti (Vptr fimpl_addr) (Vptr thisp :: vs) (fun res => [| res = Vptr addr |] -* Q (free ** free')))
            (* NOTE as with other function calls, we are assuming an equation on the address in order
               to express the fact the the object is constructed in-place.
             *)
          | _ => False
          end))
      |-- wp_init ty addr (Emember_call (inl (f, Virtual, fty)) vc obj es ty) Q.

    (* null *)
    Axiom wp_null : forall Q,
      Q (Vptr nullptr) empSP
      |-- wp_prval Enull Q.

    (** [new (...) C(...)]
        - invokes a C++ new operator [new_fn], which returns a pointer [resp];
          [new_fn] _might_ allocate memory
          (https://eel.is/c++draft/expr.new#10), or return an argument
          address for some forms of placement new;
        - constructs a pointer [newp], which shares the address of [resp];
        - invokes the constructor C over [newp].
        https://eel.is/c++draft/expr.new

        - This axiom assumes that [resp] points to a character array that will
          _provide storage_ for a new _complete object_ [o]
          (http://eel.is/c++draft/intro.object#def:provides_storage).

          In that case, the C++ abstract machine can choose to make [newp <>
          resp], so that the old pointer [resp] cannot be used to access
          the new object. Following Cerberus, we model this by giving [newp] a
          different allocation ID.

        - The created object might be a subobject of an existing object
          (pointed to by some pointer [p])
          (https://eel.is/c++draft/basic.memobj#intro.object-2).
          It is unclear whether that requires [resp = p] or just
          [provides_storage resp p].
          In that case, we plan to allow proving that [newp] = [p ., o]; we
          offer no such support at present; we account for this case by not specifying that
          [ptr_alloc_id newp <> ptr_alloc_id resp].
        - Currently, we do not model coalescing of multiple allocations
          (https://eel.is/c++draft/expr.new#14).
     *)
    Axiom wp_prval_new : forall new_fn new_args init aty ty Q,
        Exists fa, _global new_fn.1 &~ fa **
        wp_args new_args (fun vs free =>
          Exists sz, [| size_of aty = Some sz |] **
            |> fspec new_fn.2 ti (Vptr fa) (Vn sz :: vs) (fun res => Exists resp : ptr,
                    [| res = Vptr resp |] **
                    if bool_decide (resp = nullptr) then
                      Q res free
                    else
                      (_at (_eqv res) (blockR sz) ** (* [blockR sz -|- tblockR aty] *)
                       (* todo: ^ This misses an condition that [res] is suitably aligned. (issue #149) *)
                           (Forall newp : ptr,
                              _at (_eq newp) (tblockR aty) -*
                              provides_storage resp newp aty -*
                              wp_init (type_of init) newp init (fun free' =>
                                                              Q (Vptr newp) (free ** free'))))))
      |-- wp_prval (Enew (Some new_fn) new_args aty None (Some init) ty) Q.

    (** The lifetime of an object can be ended at an arbitrary point
        without calling the destructor
        (http://eel.is/c++draft/basic.life#5). According to
        http://eel.is/c++draft/basic.life#5, a program has UB if it
        depends on the side effects of the destructor if it is not
        explicitly called before the storage is reused. This is
        reflected here by not doing the ownership manipulation that
        the destructor would potentially do. *)
    Axiom end_provides_storage : forall res newp aty sz,
       size_of aty = Some sz ->
       provides_storage res newp aty ** _at (_eq newp) (anyR aty 1)
         ={⊤}=∗ (_at (_eq res) (blockR sz)).

    (* delete

       https://eel.is/c++draft/expr.delete

       TODO this does not support array delete yet.
     *)
    Axiom wp_prval_delete : forall delete_fn e ty dtor destroyed_type Q,
        (* call the destructor on the object, and then call delete_fn *)
        wp_prval e (fun v free =>
                      Exists vp, [| v = Vptr vp |] **
          destruct_val destroyed_type vp dtor
              (Exists da, _global delete_fn.1 &~ da **
               fspec delete_fn.2 ti (Vptr da) (Vptr vp :: nil) (fun v => Q v free)))
        |-- wp_prval (Edelete false (Some delete_fn) e destroyed_type dtor ty) Q.

    (** temporary expressions
       note(gmm): these axioms should be reviewed thoroughly
     *)
    Axiom wp_lval_clean : forall e ty Q,
        wp_lval e Q |-- wp_lval (Eandclean e ty) Q.
    Axiom wp_prval_clean : forall e ty Q,
        wp_prval e Q |-- wp_prval (Eandclean e ty) Q.
    Axiom wp_xval_clean : forall e ty Q,
        wp_xval e Q |-- wp_xval (Eandclean e ty) Q.

    (** [Ematerialize_temp e ty] is an xvalue

        XXX currently there are different ways to represent
            uninitialized memory for aggregates (using [tblockR])
            and for primitves (using [uninitR] or [anyR]).
            Because of this, the this probably needs to do a case
            split on the type of the value that we are materializing.
     *)
    Axiom wp_xval_temp : forall e ty Q,
        (let raw_type := erase_qualifiers ty in
         Forall a, _at (_eq a) (tblockR raw_type) -*
                  let '(e,dt) := destructor_for e in
                  wp_init ty a e
                          (fun free => Q a (destruct_val ty a dt (_at (_eq a) (tblockR raw_type) ** free))))
        |-- wp_xval (Ematerialize_temp e ty) Q.

    (** temporary materialization only occurs when the resulting value is used.
        if the value is ignored, e.g. in `go();` (when the result of `go` is an
        aggregate) we introduce an implicit materialization and then immediately
        free the result.

        XXXX this needs a thorough review.
     *)
    Axiom wp_prval_implicit_materialize : forall e Q,
        is_aggregate (type_of e) = true ->
        (let ty := type_of e in
         let raw_type := erase_qualifiers ty in
         Forall a, _at (_eq a) (tblockR raw_type) -*
                   let '(e,dt) := destructor_for e in
                   wp_init ty a e (fun free =>
                                     Q (Vptr a) (destruct_val ty a dt (_at (_eq a) (tblockR raw_type) ** free))))
        |-- wp_prval e Q.


    (** [Ebind_temp e dtor ty] is an initialization expression that ensures
       that the destructor is called.

       this aspect of the AST seems to be non-compositional, so we handle it
       in another way, naively, the rule might look something like the following

       [[
    Axiom wp_init_bind_temp : forall e ty a dtor Q,
        wp_init ty a e (fun free =>
                     Exists fa, [| glob_addr resolve dtor fa |] **
                     |> fspec (Vptr fa) (a :: nil) ti (fun _ => Q free))
      |-- wp_init ty a (Ebind_temp e dtor ty) Q.
       ]]
     *)

    (** XXX this needs a thorough review *)
    Axiom wp_prval_materialize : forall ty e dtor Q,
      (Forall a : ptr,
      let raw_type := erase_qualifiers ty in
      _at (_eq a) (tblcokR raw_type) -*
          wp_init ty a e (fun free =>
                            Q (Vptr a) (destruct_val ty a (Some dtor) (_at (_eq a) (tblockR raw_type) ** free))))
      |-- wp_prval (Ebind_temp e dtor ty) Q.

    (** Pseudo destructors arise from calling the destructor on
        an object of templated type when the type is instantiated
        with a primitive. For example,

          template<typename T> void destroy_it(T* t) { t->~T(); }

        with [T = int].

        To maintain similarity with the rest of the system, we
        the C++ abstract machine "implments" these destructors as
        (essentially) a function with the specification:

           \pre this |-> anyR ty 1
           \post this |-> tblockR ty
     *)
    Axiom wp_pseudo_destructor : forall e ty Q,
        wp_prval e (fun v free => _at (_eqv v) (anyR ty 1) ** (_at (_eqv v) (tblockR ty) -* Q Vundef free))
        |-- wp_prval (Epseudo_destructor ty e) Q.

    (* Implicit initialization initializes the variables with
       indeterminate values.
     *)
    Axiom wp_prval_implicit_init_int : forall ty sz sgn Q,
        drop_qualifiers ty = Tint sz sgn ->
          Q Vundef emp
      |-- wp_prval (Eimplicit_init ty) Q.

    Axiom wp_prval_implicit_init_bool : forall ty Q,
        drop_qualifiers ty = Tbool ->
          Q Vundef emp
      |-- wp_prval (Eimplicit_init ty) Q.

  End with_resolve.

End Expr.

Declare Module E : Expr.

Export E.
