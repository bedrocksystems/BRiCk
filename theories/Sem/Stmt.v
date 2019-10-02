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

From Cpp.Sem Require Import
        ChargeUtil Semantics Logic PLogic Destroy Wp Init Call Intensional.
From Cpp Require Import Ast.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

Module Type Stmt.
  Local Open Scope string_scope.

  (** weakest pre-condition for statements
   *)
  Section with_resolver.
    Context {Σ:gFunctors}.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp := (wp (Σ :=Σ) (resolve:=resolve)  ti ρ).
    Local Notation wpe := (wpe (Σ :=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_lval := (wp_lval (Σ :=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_prval := (wp_prval (Σ :=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_xval := (wp_xval (Σ :=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_glval := (wp_glval (Σ :=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_rval := (wp_rval (Σ :=Σ) (resolve:=resolve) ti ρ).
    Local Notation wp_init := (wp_init (Σ :=Σ) (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (Σ :=Σ) (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (Σ :=Σ) (resolve:=resolve) ti ρ).

    Local Notation mpred := (mpred Σ) (only parsing).
    Local Notation Kpreds := (Kpreds Σ) (only parsing).

   (* the semantics of return is like an initialization
     * expression.
     *)
    Axiom wp_return_void : forall Q,
        Q.(k_return) None empSP |-- wp (Sreturn None) Q.

    Axiom wp_return : forall c e Q,
        (if is_aggregate (type_of e) then
           (* ^ C++ erases the reference information on types for an unknown
            * reason, see http://eel.is/c++draft/expr.prop#expr.type-1.sentence-1
            * so we need to re-construct this information from the value
            * category of the expression.
            *)
           match c with
           | Rvalue =>
             Exists a, _result ρ &~ a ** ltrue //\\
             wp_init (erase_qualifiers (type_of e)) a (not_mine e) (Q.(k_return) (Some a))
           | Lvalue
           | Xvalue =>
             wpe c e (fun v => Q.(k_return) (Some v))
           end
         else
           wpe c e (fun v => Q.(k_return) (Some v)))
        |-- wp (Sreturn (Some (c, e))) Q.

    Axiom wp_break : forall Q,
        Q.(k_break) |-- wp Sbreak Q.
    Axiom wp_continue : forall Q,
        Q.(k_continue) |-- wp Scontinue Q.

    Axiom wp_expr : forall vc e Q,
        wpAny (vc,e) (SP (fun _ => Q.(k_normal)))
        |-- wp (Sexpr vc e) Q.

    (* This definition performs allocation of local variables
     * note that references do not allocate anything in the semantics, they are
     * just aliases.
     *)
    Fixpoint wp_decl (x : ident) (ty : type) (init : option Expr) (dtor : option obj_name)
               (k : Kpreds -> mpred) (Q : Kpreds)
               (* ^ Q is the continuation for after the declaration
                *   goes out of scope.
                * ^ k is the rest of the declaration
                *)
    : mpred :=
      match ty with
      | Tvoid => lfalse

        (* primitives *)
      | Tpointer _
      | Tbool
      | Tchar _ _
      | Tint _ _ =>
        Forall a,
        let done :=
            k (Kfree (tlocal_at ρ x a (tany (erase_qualifiers ty))) Q)
        in
        match init with
        | None => _at (_eq a) (uninit (erase_qualifiers ty)) -* done
        | Some init =>
          wp_prval init (fun v free => free **
                              (_local ρ x &~ a ** _at (_eq a) (tprim (erase_qualifiers ty) v)
                           -* done))
        end

      | Tref cls =>
        Forall a, _at (_eq a) (uninit ty) -*
                  let destroy :=
                      match dtor with
                      | None => fun x => x
                      | Some dtor => destruct_obj (resolve:=resolve) ti dtor cls a
                      end (_at (_eq a) (tany ty))
                  in
                  let continue :=
                      _local ρ x &~ a -* k (Kfree (_local ρ x &~ a ** destroy) Q)
                  in
                  match init with
                  | None => continue
                  | Some init =>
                    wp_init ty a (not_mine init) (fun free => free ** continue)
                  end
      | Tarray ty' N =>
        Forall a, _at (_eq a) (uninit (erase_qualifiers ty)) -*
                  let destroy : mpred :=
                      match dtor with
                      | None => fun x => x
                      | Some dtor => destruct (resolve:=resolve) ti ty a dtor
                      end (_at (_eq a) (tany (erase_qualifiers ty)))
                  in
                  let continue :=
                      _local ρ x &~ a -*
                      k (Kfree (_local ρ x &~ a ** _at (_eq a) (tany (erase_qualifiers ty))) Q)
                  in
                  match init with
                  | None => continue
                  | Some init =>
                    wp_init ty a (not_mine init) (fun free => free ** continue)
                  end

        (* references *)
      | Trv_reference t
      | Treference t =>
        match init with
        | None => lfalse
          (* ^ references must be initialized *)
        | Some init =>
          (* i should use the type here *)
          wp_lval init (fun a free =>
             _local ρ x &~ a -* (free ** k (Kfree (_local ρ x &~ a) Q)))
        end

      | Tfunction _ _ => lfalse (* not supported *)

      | Tqualified _ ty => wp_decl x ty init dtor k Q
      end.

    Fixpoint wp_decls (ds : list VarDecl)
             (k : Kpreds -> mpred) : Kpreds -> mpred :=
      match ds with
      | nil => k
      | {| vd_name := x ; vd_type := ty ; vd_init := init ; vd_dtor := dtor |} :: ds =>
        wp_decl x ty init dtor (wp_decls ds k)
      end.

    (* note(gmm): this rule is non-compositional because
     * wp_decls requires the rest of the block computation
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
        wp_prval e (fun v free =>
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

    Axiom wp_do : forall t b Q I,
        I |-- wp (Sseq (b :: (Sif None t Scontinue Sskip) :: nil)) (Kloop I Q) ->
        I |-- wp (Sdo b t) Q.

    (* compute the [Prop] that is known if this switch branch is taken *)
    Definition wp_switch_branch (v : Z) (s : SwitchBranch) : Prop :=
      match s with
      | Exact i => v = i
      | Range low high => low <= v <= high
      end%Z.

    Fixpoint no_case (s : Stmt) : bool :=
      match s with
      | Sseq ls => forallb no_case ls
      | Sdecl _ => true
      | Sif _ _ a b => no_case a && no_case b
      | Swhile _ _ s => no_case s
      | Sfor _ _ _ s => no_case s
      | Sdo s _ => no_case s
      | Sattr _ s => no_case s
      | Sswitch _ _ => true
      | Scase _
      | Sdefault => false
      | Sbreak
      | Scontinue
      | Sreturn _
      | Sexpr _ _
      | Sasm _ _ _ _ _ => true
      | Slabeled _ s => no_case s
      | Sgoto _ => true
      end.


    (* apply the [wp] calculation to the body of a switch *)
    Fixpoint wp_switch_block (e : Z) (L : Prop) (ls : list Stmt) (Q : Kpreds) : mpred :=
      match ls with
      | Scase sb :: ls =>
        let here := wp_switch_branch e sb in
        ([| here |] -* wp (Sseq ls) Q) //\\
        wp_switch_block e (L \/ here) ls Q
      | Sdefault :: ls =>
        [| ~L |] -* wp_switch_block e L ls Q
      | s :: ls =>
        if no_case s then
          wp_switch_block e L ls Q
        else
          lfalse
      | nil => lfalse
      end.
    (* ^ note(gmm): this could be optimized to avoid re-proving lines of code in the
     * case of fall-throughs
     *)

    Definition Kswitch (k : Kpreds) : Kpreds :=
      {| k_normal := k.(k_normal)
       ; k_return := k.(k_return)
       ; k_break  := k.(k_normal)
       ; k_continue := k.(k_continue) |}.

    Axiom wp_switch : forall e b Q,
        wp_prval e (fun v free =>
                    Exists vv : Z, [| v = Vint vv |] **
                    wp_switch_block vv False b (Kswitch Q))
        |-- wp (Sswitch e (Sseq b)) Q.

    (* note: case and default statements are only meaningful inside of [switch].
     * this is handled by [wp_switch_block].
     *)
    Axiom wp_case : forall sb Q, Q.(k_normal) |-- wp (Scase sb) Q.
    Axiom wp_default : forall Q, Q.(k_normal) |-- wp Sdefault Q.

  End with_resolver.

End Stmt.

Declare Module S : Stmt.

Export S.
