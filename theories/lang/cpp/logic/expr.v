(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
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
     initializers
     wp call
     translation_unit
     dispatch.

Require Import bedrock.lang.cpp.heap_notations.

Module Type Expr.

  (* TODO these should be removed *)
  Coercion Vint : Z >-> val.
  Coercion Z.of_N : N >-> Z.

  (**
   * Weakest pre-condition for expressions
   *
   * NOTE It is important that these rules are sound, but less important that
   * they are complete. When in doubt, we err on the side of caution and under-specify
   * the behavior of various constructs.
   *
   * If you run into code that requires addditional semantic specification, please file
   * an issue.
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
    Local Notation wpe := (wpe (resolve:=resolve) M ti ρ).
    Local Notation wp_specific_glval := (wp_specific_glval (resolve:=resolve) M ti ρ).
    Local Notation wp_args := (wp_args (σ:=resolve) M ti ρ).
    Local Notation fspec := (fspec resolve.(genv_tu).(globals)).
    Local Notation destruct_val := (destruct_val (σ:=resolve) ti) (only parsing).

    Local Notation glob_def := (glob_def resolve) (only parsing).
    Local Notation _global := (_global (resolve:=resolve)) (only parsing).
    Local Notation _field := (o_field resolve) (only parsing).
    Local Notation _base := (o_base resolve) (only parsing).
    Local Notation _derived := (o_derived resolve) (only parsing).
    Local Notation _sub := (o_sub resolve) (only parsing).
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
          valid_ptr (_this ρ) ** Q (Vptr $ _this ρ) emp
      |-- wp_prval (Ethis ty) Q.


    (* variables are lvalues *)
    Axiom wp_lval_lvar : forall ty x Q,
          valid_ptr (_local ρ x) ** Q (_local ρ x) emp
      |-- wp_lval (Evar (Lname x) ty) Q.

    (* what about the type? if it exists *)
    Axiom wp_lval_gvar : forall ty x Q,
          valid_ptr (_global x) ** Q (_global x) emp
      |-- wp_lval (Evar (Gname x) ty) Q.

    (* [Emember a f ty] is an lvalue by default except when
     * - where [m] is a member enumerator or a non-static member function, or
     * - where [a] is an rvalue and [m] is a non-static data member of non-reference type
     *
     * NOTE We need [vc] in order to distinguish the two forms of [rvalue], [xvalue] and [prvalue]
     *)
    Axiom wp_lval_member : forall ty vc a m Q,
        match vc with
        | Prvalue => False
        | Lvalue =>
          wp_lval a (fun base free =>
                       let addr := (base ., _field m) in
                       valid_ptr addr ** Q addr free)
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
          (* This does not occur because our AST explicitly contains [Cl2r] casts.
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
          (* This does not occur because our AST explicitly contains [Cl2r] casts.
           *)
        | Xvalue =>
          wp_xval a (fun base free =>
                       let addr := base ., _field m in
                       valid_ptr addr ** Q addr free)
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
         (Exists i, [| idx = Vint i |] **
          let addr := base .[ erase_qualifiers t ! i ] in
          valid_ptr addr ** Q addr (free' ** free)))
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
          (Exists i, [| idx = Vint i |] **
           let addr := _eqv base .[ erase_qualifiers t ! i ] in
           valid_ptr addr ** Q addr (free' ** free)))
      |-- wp_xval (Esubscript e i t) Q.

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

    (** * Unary Operators
        NOTE the following axioms assume that [eval_unop] is deterministic when it is defined
     *)
    Axiom wp_prval_unop : forall o e ty Q,
        wp_prval e (fun v free => (* todo: rval? *)
          Exists v',
          [| eval_unop o (erase_qualifiers (type_of e)) (erase_qualifiers ty) v v' |] **
          Q v' free)
        |-- wp_prval (Eunop o e ty) Q.

    Axiom wp_lval_preinc : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v' v'',
              (eval_binop Badd (erase_qualifiers (type_of e)) cty
                (erase_qualifiers ty) v' (Vint 1) v'' ** True) //\\
              (a |-> primR (erase_qualifiers ty) 1 v' **
                (a |-> primR (erase_qualifiers ty) 1 v'' -* Q a free)))
        | None => False
        end
        |-- wp_lval (Epreinc e ty) Q.

    Axiom wp_lval_predec : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v' v'',
              (eval_binop Bsub (erase_qualifiers (type_of e)) cty
                (erase_qualifiers ty) v' (Vint 1) v'' ** True) //\\
              (a |-> primR (erase_qualifiers ty) 1 v' **
                (a |-> primR (erase_qualifiers ty) 1 v'' -* Q a free)))
        | None => False
        end
        |-- wp_lval (Epredec e ty) Q.

    Axiom wp_prval_postinc : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              (eval_binop Badd (erase_qualifiers (type_of e)) cty
                (erase_qualifiers ty) v' (Vint 1) v'' ** True) //\\
              (a |-> primR (erase_qualifiers ty) 1 v' **
                (a |-> primR (erase_qualifiers ty) 1 v'' -* Q v' free)))
        | None => False
        end
        |-- wp_prval (Epostinc e ty) Q.

    Axiom wp_prval_postdec : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lval e (fun a free => Exists v', Exists v'',
              (eval_binop Bsub (erase_qualifiers (type_of e)) cty
                (erase_qualifiers ty) v' (Vint 1) v'' ** True) //\\
              (a |-> primR (erase_qualifiers ty) 1 v' **
                (a |-> primR (erase_qualifiers ty) 1 v'' -* Q v' free)))
        | None => False
        end
        |-- wp_prval (Epostdec e ty) Q.

    (** * Binary Operators *)
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
            la |-> anyR (erase_qualifiers ty) 1 **
           (la |-> primR (erase_qualifiers ty) 1 rv -* Q la (free1 ** free2)))
        |-- wp_lval (Eassign l r ty) Q.

    (* Assignemnt operators are *almost* like regular assignments except that they
       guarantee to evalute the left hand side *exactly* once (rather than twice
       which is what would come from the standard desugaring)
     *)
    Axiom wp_lval_bop_assign : forall ty o l r Q,
        (Exists Ql Qr,
        wp_lval l Ql ** wp_prval r Qr **
        Forall la free1 rv free2, Ql la free1 -* Qr rv free2 -*
             (Exists v v', la |-> primR (erase_qualifiers ty) 1 v **
                 ((eval_binop o (erase_qualifiers (type_of l)) (erase_qualifiers (type_of r)) (erase_qualifiers (type_of l)) v rv v' ** True) //\\
                 (la |-> primR (erase_qualifiers ty) 1 v' -* Q la (free1 ** free2)))))
        |-- wp_lval (Eassign_op o l r ty) Q.

    (* The comma operator can be both an lvalue and a prvalue
     * depending on what the second expression is.
     *)
    Axiom wp_lval_comma : forall {vc} ty e1 e2 Q,
        wpe vc e1 (fun _ free1 => wp_lval e2 (fun val free2 => Q val (free1 ** free2)))
        |-- wp_lval (Ecomma vc e1 e2 ty) Q.

    Axiom wp_xval_comma : forall {vc} ty e1 e2 Q,
        wpe vc e1 (fun _ free1 => wp_xval e2 (fun val free2 => Q val (free1 ** free2)))
        |-- wp_xval (Ecomma vc e1 e2 ty) Q.

    Axiom wp_prval_comma : forall {vc} ty e1 e2 Q,
        wpe vc e1 (fun _ free1 => wp_prval e2 (fun val free2 => Q val (free1 ** free2)))
        |-- wp_prval (Ecomma vc e1 e2 ty) Q.

    Axiom wp_init_comma : forall {vc} ty' ty p e1 e2 Q,
        wpe vc e1 (fun _ free1 => wp_init ty' p e2 (fun free2 => Q (free1 ** free2)))
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

    (** * Casts
        Casts apply exclusively to primitive types, all other casts in C++
        are represented as overloaded functions.
     *)

    (** [Cl2r] represents reads of locations. *)
    Axiom wp_prval_cast_l2r_l : forall ty e Q,
        wp_lval e (fun a free => Exists q, Exists v,
           (a |-> primR (erase_qualifiers ty) q v ** True) //\\ Q v free)
        |-- wp_prval (Ecast Cl2r (Lvalue, e) ty) Q.

    Axiom wp_prval_cast_l2r_x : forall ty e Q,
        wp_xval e (fun a free => Exists q, Exists v, (* was wp_lval *)
          (a |-> primR (erase_qualifiers ty) q v ** True) //\\ Q v free)
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

    (** Known places that bitcasts occur
        - casting between [void*] and [T*] for some [T].
     *)
    Axiom wp_prval_cast_bitcast : forall e t Q,
        wp_prval e Q
        |-- wp_prval (Ecast Cbitcast (Prvalue, e) t) Q.

    (** [Cintegral] casts represent casts between integral types, e.g.
        - [int] -> [short]
        - [short] -> [long]
        - [int] -> [unsigned int]
     *)
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
     * NOTE Our AST (based on Clang's AST) *seems to* generate this only when
     *      [from] is a (transitive) base class of [to]. In other instances
     *      an implicit cast, e.g. [Cderived2base], [Cintegral], etc, are
     *      inserted. This (essentially) desugars most uses of [static_cast]
     *      to simpler casts that are captured by other rules.
     *)
    Axiom wp_prval_static_cast : forall from to e ty Q,
      wp_prval e (fun addr free =>
                    (Exists path : @class_derives resolve to from,
                     let addr' := _eqv addr ., base_to_derived path in
                     valid_ptr addr' ** Q (Vptr addr') free))
      |-- wp_prval (Ecast (Cstatic from to) (Prvalue, e) ty) Q.

    (** You can cast anything to void, but an expression of type
     * [void] can only be a pr_value *)
    Axiom wp_prval_cast_tovoid : forall vc e Q,
          wpe vc e (fun _ free => Q (Vint 0) free)
      |-- wp_prval (Ecast C2void (vc, e) Tvoid) Q.

    Axiom wp_prval_cast_array2pointer : forall e t Q,
        wp_lval e (fun p => Q (Vptr p))
        |-- wp_prval (Ecast Carray2pointer (Lvalue, e) t) Q.

    (** [Cpointer2int] exposes the pointer, which is expressed with [pinned_ptr]
     *)
    Axiom wp_prval_pointer2int : forall e ty Q,
        match drop_qualifiers (type_of e) , ty with
        | Tptr _ , Tint sz sgn =>
          wp_prval e (fun v free => Exists p, [| v = Vptr p |] **
            (Forall va, pinned_ptr va p -* Q (Vint (match sgn with
                                                    | Signed => to_signed sz
                                                    | Unsigned => trim (bitsN sz)
                                                    end (Z.of_N va))) free))
        | _ , _ => False
        end
        |-- wp_prval (Ecast Cpointer2int (Prvalue, e) ty) Q.

    (** [Cint2pointer] uses "angelic non-determinism" to allow the developer to
        pick any pointer that was previously exposed as the given integer.
     *)
    Axiom wp_prval_int2pointer : forall e ty Q,
        match unptr ty with
        | Some ptype =>
          wp_prval e (fun v free => Exists va : N, [| v = Vint (Z.of_N va) |] **
             (([| (va > 0)%N |] ** Exists p, pinned_ptr va p ** type_ptr (resolve:=resolve) ptype p ** Q (Vptr p) free) \\//
              ([| va = 0%N |] ** Q (Vptr nullptr) free)))
        | _ => False
        end
        |-- wp_prval (Ecast Cint2pointer (Prvalue, e) ty) Q.

    (** [Cderived2base] casts from a derived class to a base
     * class. Casting is only permitted on pointers and references
     * - references occur with lvalues and xvalues
     * - pointers occur with prvalues
     *
     * TODO [_base] only supports casting up a single level of the
     * heirarchy at a time, so we need to construct a full path.
     *)
    Axiom wp_lval_cast_derived2base : forall e ty Q,
      wp_lval e (fun addr free =>
        match drop_qualifiers (type_of e), drop_qualifiers ty with
        | Tnamed derived , Tnamed base => (*<-- is this the only case here?*)
          Exists path : @class_derives resolve derived base,
          let addr' := addr ., derived_to_base path in
          valid_ptr addr' ** Q addr' free
        | _, _ => False
        end)
      |-- wp_lval (Ecast Cderived2base (Lvalue, e) ty) Q.

    Axiom wp_xval_cast_derived2base : forall e ty Q,
      wp_xval e (fun addr free =>
        match drop_qualifiers (type_of e), drop_qualifiers ty with
        | Tnamed derived , Tnamed base => (*<-- is this the only case here?*)
          Exists path : @class_derives resolve derived base,
          let addr' := addr ., derived_to_base path in
          valid_ptr addr' ** Q addr' free
        | _, _ => False
        end)
      |-- wp_xval (Ecast Cderived2base (Xvalue, e) ty) Q.

    Axiom wp_prval_cast_derived2base : forall e ty Q,
      wp_prval e (fun addr free =>
        match unptr (type_of e), unptr ty with
        | Some (Tnamed derived) , Some (Tnamed base) =>
          Exists path : @class_derives resolve derived base,
          let addr' := _eqv addr ., derived_to_base path in
          valid_ptr addr' ** Q (Vptr addr') free
        | _, _ => False
        end)
      |-- wp_prval (Ecast Cderived2base (Prvalue, e) ty) Q.

    (* [Cbase2derived] casts from a base class to a derived class.
     *)
    Axiom wp_lval_cast_base2derived : forall e ty Q,
      wp_lval e (fun addr free =>
        match drop_qualifiers (type_of e), drop_qualifiers ty with
        | Tnamed base, Tnamed derived => (*<-- is this the only case here?*)
          Exists path : @class_derives resolve derived base,
          let addr' := addr ., base_to_derived path in
          valid_ptr addr' ** Q addr' free
        | _, _ => False
        end)
      |-- wp_lval (Ecast Cbase2derived (Lvalue, e) ty) Q.

    Axiom wp_xval_cast_base2derived : forall e ty Q,
      wp_xval e (fun addr free =>
        match drop_qualifiers (type_of e), drop_qualifiers ty with
        | Tnamed base, Tnamed derived => (*<-- is this the only case here?*)
          Exists path : @class_derives resolve derived base,
          let addr' := addr ., base_to_derived path in
          valid_ptr addr' ** Q addr' free
        | _, _ => False
        end)
      |-- wp_xval (Ecast Cbase2derived (Xvalue, e) ty) Q.

    Axiom wp_prval_cast_base2derived : forall e ty Q,
      wp_prval e (fun addr free =>
        match unptr (type_of e), unptr ty with
        | Some (Tnamed base), Some (Tnamed derived) =>
          Exists path : @class_derives resolve derived base,
          let addr' := _eqv addr ., base_to_derived path in
          valid_ptr addr' ** Q (Vptr addr') free
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
           Forall addr : ptr, wp_init ty addr (Ecall f es ty) (fun free =>
                Q (Vptr addr) (free ** destruct_val (erase_qualifiers ty) addr None (addr |-> anyR (erase_qualifiers ty) 1 (* TODO backwards compat [tblockR (erase_qualifiers ty)] *))))
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


    (** member call *)
    Axiom wp_lval_member_call : forall ty fty f vc obj es Q,
        wp_specific_glval vc obj (fun this free_t => wp_args es (fun vs free =>
           |> fspec fty ti (Vptr $ _global f) (Vptr this :: vs) (fun v =>
                    Exists p, [| v = Vptr p |] ** Q p (free_t ** free))))
        |-- wp_lval (Emember_call (inl (f, Direct, fty)) vc obj es ty) Q.

    Axiom wp_xval_member_call : forall ty fty f vc obj es Q,
        wp_specific_glval vc obj (fun this free_t => wp_args es (fun vs free =>
           |> fspec fty ti (Vptr $ _global f) (Vptr this :: vs) (fun v =>
                    Exists p, [| v = Vptr p |] ** Q p (free_t ** free))))
        |-- wp_xval (Emember_call (inl (f, Direct, fty)) vc obj es ty) Q.

    Axiom wp_prval_member_call : forall ty fty f vc obj es Q,
          wp_specific_glval vc obj (fun this free_t => wp_args es (fun vs free =>
              |> fspec fty ti (Vptr $ _global f) (Vptr this :: vs) (fun v => Q v (free_t ** free))))
        |-- wp_prval (Emember_call (inl (f, Direct, fty)) vc obj es ty) Q.

    Axiom wp_init_member_call : forall f fty es addr ty vc obj Q,
        wp_specific_glval vc obj (fun this free_t => wp_args es (fun vs free =>
             |> fspec fty ti (Vptr $ _global f) (Vptr this :: vs) (fun res =>
                      [| res = Vptr addr |] -* Q (free_t ** free))))
        (* NOTE as with regular function calls, we use an assumed equation to unify the address
           of the returned object with the location that we are initializing.
         *)
        |-- wp_init ty addr (Emember_call (inl (f, Direct, fty)) vc obj es ty) Q.

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
            resolve_virtual (σ:=resolve) this cls f (fun fimpl_addr thisp =>
              |> fspec fty ti (Vptr fimpl_addr) (Vptr thisp :: vs) (fun v =>
                       Exists p, [| v = Vptr p |] ** Q p (free ** free')))
          | _ => False
          end))
      |-- wp_xval (Emember_call (inl (f, Virtual, fty)) vc obj es ty) Q.

    Axiom wp_lval_virtual_call : forall ty fty f vc obj es Q,
      wp_specific_glval vc obj (fun this free => wp_args es (fun vs free' =>
          match class_type (type_of obj) with
          | Some cls =>
            resolve_virtual (σ:=resolve) this cls f (fun fimpl_addr thisp =>
              |> fspec fty ti (Vptr fimpl_addr) (Vptr thisp :: vs) (fun v =>
                       Exists p, [| v = Vptr p |] ** Q p (free ** free')))
          | _ => False
          end))
      |-- wp_lval (Emember_call (inl (f, Virtual, fty)) vc obj es ty) Q.

    Axiom wp_prval_virtual_call : forall ty fty f vc obj es Q,
      wp_specific_glval vc obj (fun this free => wp_args es (fun vs free' =>
          match class_type (type_of obj) with
          | Some cls =>
            resolve_virtual (σ:=resolve) this cls f (fun fimpl_addr thisp =>
              |> fspec fty ti (Vptr fimpl_addr) (Vptr thisp :: vs) (fun v => Q v (free ** free')))
         | _ => False
          end))
      |-- wp_prval (Emember_call (inl (f, Virtual, fty)) vc obj es ty) Q.

    Axiom wp_init_virtual_call : forall ty fty f vc obj es Q addr,
      wp_specific_glval vc obj (fun this free => wp_args es (fun vs free' =>
          match class_type (type_of obj) with
          | Some cls =>
            resolve_virtual (σ:=resolve) this cls f (fun fimpl_addr thisp =>
              |> fspec fty ti (Vptr fimpl_addr) (Vptr thisp :: vs) (fun res => [| res = Vptr addr |] -* Q (free ** free')))
            (* NOTE as with other function calls, we are assuming an equation on the address in order
               to express the fact the the object is constructed in-place.
             *)
          | _ => False
          end))
      |-- wp_init ty addr (Emember_call (inl (f, Virtual, fty)) vc obj es ty) Q.

    (* null *)
    Axiom wp_null : forall Q,
      Q (Vptr nullptr) emp
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
        wp_args new_args (fun vs free =>
          Exists sz, [| size_of aty = Some sz |] **
            |> fspec new_fn.2 ti (Vptr $ _global new_fn.1) (Vn sz :: vs) (fun res => Exists resp : ptr,
                    [| res = Vptr resp |] **
                    if bool_decide (resp = nullptr) then
                      Q res free
                    else
                      (resp |-> blockR sz ** (* [blockR sz -|- tblockR aty] *)
                       (* todo: ^ This misses an condition that [res] is suitably aligned. (issue #149) *)
                           (Forall newp : ptr,
                              newp |-> anyR aty 1 (* TODO backwards compat [tblockR aty] *) -*
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
       provides_storage res newp aty ** newp |-> anyR aty 1
         ={⊤}=∗ (res |-> blockR sz).

    (* delete

       https://eel.is/c++draft/expr.delete

       TODO this does not support array delete yet.
     *)
    Axiom wp_prval_delete : forall delete_fn e ty dtor destroyed_type Q,
        (* call the destructor on the object, and then call delete_fn *)
        wp_prval e (fun v free =>
                      Exists vp, [| v = Vptr vp |] **
          destruct_val destroyed_type vp dtor
              (fspec delete_fn.2 ti (Vptr $ _global delete_fn.1) (Vptr vp :: nil) (fun v => Q v free)))
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

    (** [Ematerialize_temp e ty] is an xvalue that gets memory (with automatic
        storage duration) and initializes it using the expression.
     *)
    Axiom wp_xval_temp : forall e ty Q,
        (let raw_type := erase_qualifiers ty in
         Forall a : ptr, a |-> uninitR raw_type 1 (* TODO backwards compat [tblockR raw_type] *) -*
                  let '(e,dt) := destructor_for e in
                  wp_init ty a e
                          (fun free => Q a (destruct_val ty a dt (a |-> anyR raw_type 1 (* TODO backwards compat [tblockR raw_type] *) ** free))))
        |-- wp_xval (Ematerialize_temp e ty) Q.

    (** temporary materialization only occurs when the resulting value is used.
        if the value is ignored, e.g. in `go();` (when the result of `go` is an
        aggregate) we introduce an implicit materialization and then immediately
        free the result.

        XXX this needs a thorough review.
     *)
    Axiom wp_prval_implicit_materialize : forall e Q,
        is_aggregate (type_of e) = true ->
        (let ty := type_of e in
         let raw_type := erase_qualifiers ty in
         Forall a : ptr, a |-> uninitR raw_type 1 (* TODO backwards compat [tblockR raw_type] *) -*
                   let '(e,dt) := destructor_for e in
                   wp_init ty a e (fun free =>
                                     Q (Vptr a) (destruct_val ty a dt (a |-> anyR raw_type 1 (* TODO backwards compat [tblockR raw_type] *) ** free))))
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
      a |-> uninitR raw_type 1 (* TODO backwards compat [tblockR raw_type] *) -*
          wp_init ty a e (fun free =>
                            Q (Vptr a) (destruct_val ty a (Some dtor) (a |-> uninitR raw_type 1 (* TODO backwards compat [tblockR raw_type] *) ** free))))
      |-- wp_prval (Ebind_temp e dtor ty) Q.

    (** Pseudo destructors arise from calling the destructor on
        an object of templated type when the type is instantiated
        with a primitive. For example,

          template<typename T> void destroy_it(T* t) { t->~T(); }

        with [T = int].

        To maintain similarity with the rest of the system, we
        the C++ abstract machine "implements" these destructors as
        (essentially) a function with the specification:

           \pre this |-> anyR ty 1
           \post this |-> tblockR ty
     *)
    Axiom wp_pseudo_destructor : forall e ty Q,
        wp_prval e (fun v free => (* TODO backwards compat [_at (_eqv v) (anyR ty 1) ** (_at (_eqv v) (tblockR ty) -*] *) Q Vundef free)
        |-- wp_prval (Epseudo_destructor ty e) Q.

    (* `Eimplicit_init` nodes reflect implicit /value initializations/ which are inserted
       into the AST by Clang [1]. The C++ standard states that value initializations [2]
       are equivalent to zero initializations for non-class and non-array types [3];
       zero initializations are documented here [4].

       [1] https://clang.llvm.org/doxygen/classclang_1_1ImplicitValueInitExpr.html#details
       [2] https://eel.is/c++draft/dcl.init#general-8
       [3] https://eel.is/c++draft/dcl.init#general-8.3
       [4] https://eel.is/c++draft/dcl.init#general-6
     *)
    Axiom wp_prval_implicit_init_int : forall ty sz sgn Q,
        drop_qualifiers ty = Tint sz sgn ->
          Q (Vint 0) emp
      |-- wp_prval (Eimplicit_init ty) Q.

    Axiom wp_prval_implicit_init_bool : forall ty Q,
        drop_qualifiers ty = Tbool ->
          Q (Vbool false) emp
      |-- wp_prval (Eimplicit_init ty) Q.

  End with_resolve.

  (* `Earrayloop_init` needs to extend the region, so we need to start a new section. *)
  Section with_resolve__arrayloop.
    Context `{Σ : cpp_logic thread_info} {resolve:genv}.
    Variables (M : coPset) (ti : thread_info).

    (* These are the only ones that we need here. *)
    Local Notation wp_lval := (wp_lval (resolve:=resolve) M ti).
    Local Notation wp_glval := (wp_glval (resolve:=resolve) M ti).
    Local Notation wp_prval := (wp_prval (resolve:=resolve) M ti).
    Local Notation wp_init := (wp_init (resolve:=resolve) M ti).
    Local Notation wp_initialize := (wp_initialize (σ:=resolve) M ti).
    Local Notation primR := (primR (resolve:=resolve)) (only parsing).

    (* `Earrayloop_init` and `Earrayloop_index` correspond, respectively,
       to the `ArrayInitLoopExpr`[1] and `ArrayInitIndexExpr`[2] expressions
       from clang. While these expressions are not a part of the C++ standard,
       we can still ascribe a useful semantics.

       In particular, this is a restricted loop so we ascribe the semantics by
       unrolling. On each iteration, the C++ Abstract Machine binds a distinguished
       variable ("!loop_index", which is not a valid identifier in C++) so that
       `Earrayloop_index` can read the value. We semantically treat this variable
       as a constant, so we only give `1/2` fraction to it and demand it back at the
       end of each iteration, preferring to do the incrementing in the logic rather
       than using the program syntax.

       For example, the following `Earrayloop_init` expression has the same
       semantics as the C++ loop which follows it /except/ that the array
       we are initializing is only evaluated once (c.f. [1]):
       ```
       (* Coq *)
       Earrayloop_init 16 target init (Tarray ``::uint8`` 16)

       (* C++ *)
       for (int "!loop_index" = 0; "!loop_index" < 16; "!loop_index"++) {
           target["!loop_index"] = init;
       }
       ```

       [1] https://clang.llvm.org/doxygen/classclang_1_1ArrayInitLoopExpr.html#details
       [2] https://clang.llvm.org/doxygen/classclang_1_1ArrayInitIndexExpr.html#details
     *)

    (* A very simple mangling of numbers to strings. Soundness only requires this to be
       injective and we don't expect the [N] to be very large in practice so we pick
       a very naive encoding.
     *)
    Definition N_to_bs (n : N) : bs :=
      N.peano_rect (fun _ => bs)
                   BS.EmptyString
                   (fun _ x => BS.String "1" x) n.

    Definition arrayloop_loop_index (n : N) : bs := "!loop_index" ++ N_to_bs n.
    Definition opaque_val (n : N) : bs := "%opaque" ++ N_to_bs n.

    (* Maybe we can `Rbind (opaque n) p`, and then add `_opaque` to encapsulate looking this up in the region;
       the new premise would be (after Loc:=ptr goes in) `Q _opaque` *)
    Axiom wp_lval_opaque_ref : forall n ρ ty Q,
          wp_lval ρ (Evar (Lname (opaque_val n)) ty) Q
      |-- wp_lval ρ (Eopaque_ref n ty) Q.

    (* Maybe do something similar to what was suggested for `wp_lval_opaque_ref` above. *)
    Axiom wp_prval_arrayloop_index : forall ρ level ty Q,
          Exists v,
            ((Exists q, _local ρ (arrayloop_loop_index level)
                               |-> primR (erase_qualifiers ty) q v) **
              True) //\\ Q v emp
      |-- wp_prval ρ (Earrayloop_index level ty) Q.

    (* The following loop is essentially the following:
       recursion of `sz`:
       ```
       Fixpoint _arrayloop_init
                (ρ : region) (level : N)
                (targetp : ptr) (init : Expr)
                (ty : type) (Q : FreeTemps -> epred)
                (sz : nat) (idx : N)
                {struct sz}
         : mpred :=
         let loop_index := _local ρ (loop_index level) in
         match sz with
         | O => Q emp
         | S sz' =>
           _at loop_index (primR (Tint W64 Unsigned) (1/2) idx) -*
           wp_init ρ ty (Vptr $ _offset_ptr targetp $ o_sub resolve ty idx) init
                   (fun free => free **
                      _at loop_index (primR (Tint W64 Unsigned) (1/2) idx) **
                      _arrayloop_init level sz' ρ (S idx) targetp init ty Q)
         end%I.
       ```

       We use `N.peano_rect` to avoid potentially building a large natural number.
     *)
    Definition _arrayloop_init
               (ρ : region) (level : N)
               (targetp : ptr) (init : Expr)
               (ty : type) (Q : FreeTemps -> epred)
               (* The arguments above this comment are constant throughout the recursion.

                  The arguments below this line will change during the recursion.
                *)
               (sz : N) (idx : N)
      : mpred :=
      let loop_index := _local ρ (arrayloop_loop_index level) in
      N.peano_rect (fun _ : N => N -> mpred)
                   (fun _ => Q emp)%I
                   (fun _ rest idx =>
                      (* NOTE: The abstract machine only provides 1/2 of the ownership
                           to the program to make it read-only.
                           NOTE that no "correct" program will ever modify this variable
                           anyways. *)
                      loop_index |-> (primR (Tint W64 Unsigned) (1/2) idx) -*
                      wp_initialize ρ ty (targetp .[ ty ! idx ]) init
                              (fun free => free **
                                 loop_index |-> (primR (Tint W64 Unsigned) (1/2) idx) **
                                 rest (N.succ idx))) sz idx.

    Axiom wp_init_arrayloop_init : forall oname level sz ρ trg vc src init ty Q,
          has_type (Vn sz) (Tint W64 Unsigned) ->
          wp_glval ρ src
                   (fun p free =>
                      Forall idxp,
                      _arrayloop_init (Rbind (opaque_val oname) p
                                             (Rbind (arrayloop_loop_index level) idxp ρ))
                                      level trg init ty
                                      (fun free' => Q (free ** free'))
                                      sz 0)
      |-- wp_init ρ (Tarray ty sz) trg
                    (Earrayloop_init oname (vc, src) level sz init (Tarray ty sz)) Q.

  End with_resolve__arrayloop.
End Expr.

Declare Module E : Expr.

Export E.
