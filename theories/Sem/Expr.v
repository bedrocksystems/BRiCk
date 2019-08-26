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
     Util Logic Semantics Operator PLogic Destroy Wp CompilationUnit.

Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNatDef.

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

    (* constants are rvalues *)
    Axiom wp_rhs_constant : forall ty cnst e Q,
      denoteGlobal cnst (Gconstant ty e) ** wp_rhs e Q
      |-- wp_rhs (Econst_ref (Gname cnst) ty) Q.

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
          embed (eval_unop (resolve:=resolve) o (drop_qualifiers (type_of e)) (drop_qualifiers ty) v v') //\\ Q v' free)
        |-- wp_rhs (Eunop o e ty) Q.

    (* note(gmm): operators need types! *)
    Fixpoint companion_type (t : type) : option type :=
      match t with
      | Tpointer _ => Some (Tint int_bits Signed)
      | Tint _ _ => Some t
      | Tchar _ _ => Some t
      | Tqualified _ t => companion_type t
      | _ => None
      end.

    Axiom wp_lhs_preinc : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lhs e (fun a free => Exists v', Exists v'',
              _at (_eq a) (tprim (drop_qualifiers ty) v') **
              [| eval_binop (resolve:=resolve) Badd (drop_qualifiers (type_of e)) cty (drop_qualifiers ty) v' (Vint 1) v'' |] **
              (_at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q a free))
        | None => lfalse
        end
        |-- wp_lhs (Epreinc e ty) Q.

    Axiom wp_lhs_predec : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lhs e (fun a free => Exists v', Exists v'',
              _at (_eq a) (tprim (drop_qualifiers ty) v') **
              [| eval_binop (resolve:=resolve) Bsub (drop_qualifiers (type_of e)) cty (drop_qualifiers ty) v' (Vint 1) v'' |] **
              (_at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q a free))
        | None => lfalse
        end
        |-- wp_lhs (Epredec e ty) Q.

    Axiom wp_rhs_postinc : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lhs e (fun a free => Exists v', Exists v'',
              _at (_eq a) (tprim (drop_qualifiers ty) v') **
              [| eval_binop (resolve:=resolve) Badd (drop_qualifiers (type_of e)) cty (drop_qualifiers ty) v' (Vint 1) v'' |] **
              (_at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q v' free))
        | None => lfalse
        end
        |-- wp_rhs (Epostinc e ty) Q.

    Axiom wp_rhs_postdec : forall e ty Q,
        match companion_type (type_of e) with
        | Some cty =>
          wp_lhs e (fun a free => Exists v', Exists v'',
              _at (_eq a) (tprim (drop_qualifiers ty) v') **
              [| eval_binop (resolve:=resolve) Bsub (drop_qualifiers (type_of e)) cty (drop_qualifiers ty) v' (Vint 1) v'' |] **
              (_at (_eq a) (tprim (drop_qualifiers ty) v'') -* Q v' free))
        | None => lfalse
        end
        |-- wp_rhs (Epostdec e ty) Q.

    (** binary operators *)
    Axiom wp_rhs_binop : forall o e1 e2 ty Q,
        wp_rhs e1 (fun v1 free1 => wp_rhs e2 (fun v2 free2 =>
            Exists v', embed (eval_binop (resolve:=resolve) o (drop_qualifiers (type_of e1)) (drop_qualifiers (type_of e2)) (drop_qualifiers ty) v1 v2 v') //\\ Q v' (free1 ** free2)))
        |-- wp_rhs (Ebinop o e1 e2 ty) Q.

    Axiom wp_lhs_assign : forall ty l r Q,
        wp_lhs l (fun la free1 => wp_rhs r (fun rv free2 =>
            _at (_eq la) (tany (drop_qualifiers ty)) **
           (_at (_eq la) (tprim (drop_qualifiers ty) rv) -* Q la (free1 ** free2))))
        |-- wp_lhs (Eassign l r ty) Q.

    Axiom wp_lhs_bop_assign : forall ty o l r Q,
        wp_lhs (Eassign l (Ebinop o (Ecast Cl2r (Lvalue, l) (type_of l)) r ty) ty) Q
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
          Exists v, (_at (_eq a) (tprim (drop_qualifiers ty) v) ** ltrue) //\\
                    Q v free)
        |-- wp_rhs (Ecast Cl2r (Lvalue, e) ty) Q.

    Axiom wpe_cast_noop : forall ty m e Q,
        wpe m e Q
        |-- wpe m (Ecast Cnoop (m, e) ty) Q.

    Axiom wp_rhs_cast_int2bool : forall ty e Q,
        wp_rhs e Q
        |-- wp_rhs (Ecast Cint2bool (Rvalue, e) ty) Q.
    (* ^ todo(gmm): confirm that this doesn't change the value *)

    Axiom wp_rhs_cast_ptr2bool : forall ty e Q,
        wp_rhs e Q
        |-- wp_rhs (Ecast Cptr2bool (Rvalue, e) ty) Q.
    (* ^ todo(gmm): confirm that this doesn't change the value *)

    Axiom wp_rhs_cast_function2pointer_c : forall ty ty' g Q,
        wp_lhs (Evar (Gname g) ty') Q
        |-- wp_rhs (Ecast Cfunction2pointer (Rvalue, Evar (Gname g) ty') ty) Q.
    Axiom wp_rhs_cast_function2pointer_cpp : forall ty ty' g Q,
        wp_lhs (Evar (Gname g) ty') Q
        |-- wp_rhs (Ecast Cfunction2pointer (Lvalue, Evar (Gname g) ty') ty) Q.
    (* ^ note(gmm): C and C++ classify function names differently
     * - in C, function names are Rvalues, and
     * - in C++, function names are Lvalues
     *)

    Axiom wp_rhs_cast_bitcast : forall e t Q,
        wp_rhs e Q
        |-- wp_rhs (Ecast Cbitcast (Rvalue, e) t) Q.

    Axiom wp_rhs_cast_integral : forall e t Q,
        wp_rhs e (fun v free => [| has_type v t |] ** Q v free)
        |-- wp_rhs (Ecast Cintegral (Rvalue, e) t) Q.

    Axiom wp_rhs_cast_null : forall e t Q,
        wp_rhs e Q
        |-- wp_rhs (Ecast Cnull2ptr (Rvalue, e) t) Q.
    (* ^ todo(jmgrosen): confirm that this doesn't change the value *)

    (* note(gmm): in the clang AST, the subexpression is the call.
     * in essence, `Ecast (Cuser ..)` is a syntax annotation.
     *)
    Axiom wp_rhs_cast_user : forall e ty Z Q,
        wp_rhs e Q
        |-- wp_rhs (Ecast (Cuser Z) (Rvalue, e) ty) Q.

    Axiom wp_rhs_cast_reinterpret : forall q e ty Q,
        wp_rhs e Q |-- wp_rhs (Ecast (Creinterpret q) (Rvalue, e) ty) Q.

    Axiom wp_lhs_static_cast : forall vc from to e ty Q,
      wpe vc e (fun addr free => Exists addr',
                  (_offsetL (_super from to) (_eq addr) &~ addr' //\\ ltrue) **
                          (* ^ this is a down-cast *)
                  Q addr' free)
      |-- wp_lhs (Ecast (Cstatic from to) (vc, e) ty) Q.

    Axiom wpe_cast_tovoid : forall vc e ty Q,
      wpe vc e (fun _ free => Q (Vint 0) free)
      |-- wpe vc (Ecast C2void (vc, e) ty) Q.

    Axiom wp_rhs_cast_array2pointer : forall e t Q,
        wp_lhs e Q
        |-- wp_rhs (Ecast Carray2pointer (Lvalue, e) t) Q.

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

    Axiom wp_rhs_sizeof_e : forall ty' e Q,
        wp_rhs (Esize_of (inl (type_of e)) ty') Q
        |-- wp_rhs (Esize_of (inr e) ty') Q.


    Axiom wp_rhs_alignof : forall ty' ty Q,
        Exists sz, [| @align_of resolve ty sz |] ** Q (Vint (Z.of_N sz)) empSP
        |-- wp_rhs (Ealign_of (inl ty) ty') Q.

    Axiom wp_rhs_alignof_e : forall ty' e Q,
        wp_rhs (Ealign_of (inl (type_of e)) ty') Q
        |-- wp_rhs (Ealign_of (inr e) ty') Q.

    (** constructors *)
    Axiom wp_rhs_constructor
    : forall cls cname (es : list (ValCat * Expr)) (ty : type) (Q : val -> FreeTemps -> mpred),
     (Exists ctor, [| glob_addr resolve cname ctor |] **
      wps wpAnys es (fun vs free => Exists a, _at (_eq a) (uninit (Tref cls))
          -* |> fspec (resolve:=resolve) (Vptr ctor) (a :: vs) ti (fun _ =>
                   (* note(gmm): constructors are rvalues but my semantics actually
                    * treats them like lvalues. *)
                   Q a (destroy (resolve:=resolve) ti Dt_Complete cls a free))) empSP)
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

    (* null *)
    Axiom wp_null : forall Q,
        Q (Vptr nullptr) empSP
        |-- wp_rhs Enull Q.

    (* temporary expressions
     * note(gmm): these axioms should be reviewed thoroughly
     *)
    Axiom wp_rhs_clean : forall e ty Q,
        wp_rhs e Q
        |-- wp_rhs (Eandclean e ty) Q.
    Axiom wp_lhs_temp : forall e ty Q,
        wp_rhs e Q
        |-- wp_lhs (Ematerialize_temp e ty) Q.


  End with_resolve.

End Expr.

Declare Module E : Expr.

Export E.
