(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Coq.Classes Require Import
     RelationClasses Morphisms.

From Coq Require Import
     Lists.List
     Strings.String.

From Cpp Require Import Ast.
From Cpp.Sem Require Import
        Util Semantics Logic PLogic Wp.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

Module Type Stmt.
  Local Open Scope string_scope.

  (** weakest pre-condition for statements
   *)
  Section with_resolver.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp := (wp (resolve:=resolve)  ti ρ).
    Local Notation wpe := (wpe (resolve:=resolve) ti ρ).
    Local Notation wp_lhs := (wp_lhs (resolve:=resolve) ti ρ).
    Local Notation wp_rhs := (wp_rhs (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (resolve:=resolve) ti ρ).

    Axiom wp_return_void : forall Q,
        Q.(k_return) None |-- wp (Sreturn None) Q.
    (* todo(gmm): it is possible to return left-hand-values, e.g. a reference *)
    Axiom wp_return_val : forall c e Q,
        wpe c e (finish (fun res => Q.(k_return) (Some res)))
        |-- wp (Sreturn (Some (c, e))) Q.

    Axiom wp_break : forall Q,
        Q.(k_break) |-- wp Sbreak Q.
    Axiom wp_continue : forall Q,
        Q.(k_continue) |-- wp Scontinue Q.

    Axiom wp_expr : forall vc e Q,
        wpAny (vc,e) (finish (fun _ => Q.(k_normal)))
        |-- wp (Sexpr vc e) Q.

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
               (* ^ Q is the continuation for after the declaration
                *   goes out of scope.
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
          wp_lhs init (fun a free =>
             _local ρ x &~ a -* (free ** k (Kfree (_local ρ x &~ a) Q)))
        end
      | Tfunction _ _ =>
        (* inline functions are not supported *)
        lfalse
      | Tvoid => lfalse
      | Tpointer pty =>
        match init with
        | None =>
          tlocal ρ x (uninit ty) -* k (Kfree (tlocal ρ x (tany ty)) Q)
        | Some init =>
          wp_rhs init (fun v free =>
                 tlocal ρ x (tprim ty v)
              -* (free ** k (Kfree (tlocal ρ x (tany ty)) Q)))
        end

      | Tbool
      | Tchar _ _
      | Tint _ _ =>
        match init with
        | None =>
          tlocal ρ x (uninit ty) -* k (Kfree (tlocal ρ x (tany ty)) Q)
        | Some init =>
          wp_rhs init (fun v free =>
                 tlocal ρ x (tprim ty v)
              -* (free ** k (Kfree (tlocal ρ x (tany ty)) Q)))
        end
      | Tarray _ _ => lfalse (* todo(gmm): arrays not yet supported *)
      | Tref gn =>
        match init with
        | Some (Econstructor cnd es _) =>
          (* todo(gmm): constructors and destructors need to be handled through
           * `cglob`.
           *)
          Exists ctor, [| glob_addr resolve cnd ctor |] **
          (* todo(gmm): is there a better way to get the destructor? *)
          wps wpAnys es (fun vs free =>
                 Forall a, _at (_eq a) (uninit (Tref gn))
              -* |> fspec (resolve:=resolve) (Vptr ctor) (a :: vs) ti (fun _ =>
                 _local ρ x &~ a -*
                 (free ** k (Kat_exit (fun Q => _local ρ x &~ a ** |> destroy (resolve:=resolve) ti Dt_Deleting gn a Q) Q)))) empSP
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
        wp s (Kseq (wp_block ss Q) Q)
      end.

    Axiom wp_seq : forall Q ss,
        wp_block ss Q |-- wp (Sseq ss) Q.


    Axiom wp_if : forall e thn els Q,
        wp_rhs e (fun v free =>
            free ** if is_true v then
                      wp thn Q
                    else
                      wp els Q)
        |-- wp (Sif None e thn els) Q.

    Axiom wp_if_decl : forall d e thn els Q,
        wp (Sseq (Sdecl (d :: nil) :: Sif None e thn els :: nil)) Q
        |-- wp (Sif (Some d) e thn els) Q.

    (* note(gmm): this rule is not sound for a total hoare logic
     *)
    Axiom wp_while : forall t b Q I,
        I |-- wp (Sif None t (Sseq (b :: Scontinue :: nil)) Sskip)
                (Kloop I Q) ->
        I |-- wp (Swhile None t b) Q.

    Axiom wp_while_decl : forall d t b Q,
        wp (Sseq (Sdecl (d :: nil) :: Swhile None t b :: nil)) Q
        |-- wp (Swhile (Some d) t b) Q.


    (* note(gmm): this rule is not sound for a total hoare logic
     *)
    Axiom wp_for : forall test incr b Q Inv,
        match test with
        | None =>
          Inv |-- wp (Sseq (b :: Scontinue :: nil))
              (Kloop match incr with
                     | None => Inv
                     | Some incr => wpAny incr (fun _ _ => Inv)
                     end Q)
        | Some test =>
          Inv |-- wp (Sif None test (Sseq (b :: Scontinue :: nil)) Sskip)
              (Kloop match incr with
                     | None => Inv
                     | Some incr => wpAny incr (fun _ _ => Inv)
                     end Q)
        end ->
        Inv |-- wp (Sfor None test incr b) Q.

    Axiom wp_for_init : forall init test incr b Q,
        wp (Sseq (init :: Sfor None test incr b :: nil)) Q
        |-- wp (Sfor (Some init) test incr b) Q.

    Axiom wp_do : forall t b Q {T : Type} I,
        I |-- wp (Sseq (b :: (Sif None t Scontinue Sskip) :: nil)) (Kloop I Q) ->
        I |-- wp (Sdo b t) Q.


  End  with_resolver.

End Stmt.

Declare Module S : Stmt.

Export S.