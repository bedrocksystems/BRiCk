(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
From Coq.Classes Require Import
     RelationClasses Morphisms.

From Coq Require Import
     Lists.List
     Strings.String.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred destroy wp initializers call intensional.

Module Type Stmt.
  (** weakest pre-condition for statements
   *)
  Section with_resolver.
    Context `{Σ : cpp_logic thread_info} {resolve:genv}.
    Variables (M : coPset) (ti : thread_info).

    Local Notation wp := (wp (resolve:=resolve) M ti).
    Local Notation wpe := (wpe (resolve:=resolve) M ti).
    Local Notation wp_lval := (wp_lval (resolve:=resolve) M ti).
    Local Notation wp_prval := (wp_prval (resolve:=resolve) M ti).
    Local Notation wp_xval := (wp_xval (resolve:=resolve) M ti).
    Local Notation wp_glval := (wp_glval (resolve:=resolve) M ti).
    Local Notation wp_rval := (wp_rval (resolve:=resolve) M ti).
    Local Notation wp_init := (wp_init (resolve:=resolve) M ti).
    Local Notation wpAny := (wpAny (resolve:=resolve) M ti).
    Local Notation wpAnys := (wpAnys (resolve:=resolve) M ti).
    Local Notation fspec := (fspec ti).
    Local Notation mdestroy := (@mdestroy Σ resolve ti) (only parsing).
    Local Notation destruct := (destruct (σ:=resolve) ti) (only parsing).
    Local Notation destruct_obj := (destruct_obj (σ:=resolve) ti) (only parsing).

    Local Notation glob_def := (glob_def resolve) (only parsing).
    Local Notation _global := (@_global resolve) (only parsing).
    Local Notation _field := (@_field resolve) (only parsing).
    Local Notation _sub := (@_sub resolve) (only parsing).
    Local Notation _super := (@_super resolve) (only parsing).
    Local Notation eval_unop := (@eval_unop resolve) (only parsing).
    Local Notation eval_binop := (@eval_binop resolve) (only parsing).
    Local Notation size_of := (@size_of resolve) (only parsing).
    Local Notation align_of := (@align_of resolve) (only parsing).
    Local Notation primR := (primR (resolve:=resolve)) (only parsing).
    Local Notation anyR := (anyR (resolve:=resolve)) (only parsing).
    Local Notation uninitR := (uninitR (resolve:=resolve)) (only parsing).


   (* the semantics of return is like an initialization
     * expression.
     *)
    Axiom wp_return_void : forall ρ Q,
        Q.(k_return) None empSP |-- wp ρ (Sreturn None) Q.

    Axiom wp_return : forall ρ c e Q,
        (if is_aggregate (type_of e) then
           (* ^ C++ erases the reference information on types for an unknown
            * reason, see http://eel.is/c++draft/expr.prop#expr.type-1.sentence-1
            * so we need to re-construct this information from the value
            * category of the expression.
            *)
           match c with
           | Rvalue =>
             Exists a, _result ρ &~ a ** ltrue //\\
             wp_init ρ (erase_qualifiers (type_of e)) (Vptr a) (not_mine e) (Q.(k_return) (Some (Vptr a)))
           | Lvalue
           | Xvalue =>
             wpe ρ c e (fun v => Q.(k_return) (Some v))
           end
         else
           wpe ρ c e (fun v => Q.(k_return) (Some v)))
        |-- wp ρ (Sreturn (Some (c, e))) Q.

    Axiom wp_break : forall ρ Q,
        |> Q.(k_break) |-- wp ρ Sbreak Q.
    Axiom wp_continue : forall ρ Q,
        |> Q.(k_continue) |-- wp ρ Scontinue Q.

    Axiom wp_expr : forall ρ vc e Q,
        |> wpAny ρ (vc,e) (SP (fun _ => Q.(k_normal)))
        |-- wp ρ (Sexpr vc e) Q.

    (* This definition performs allocation of local variables
     * note that references do not allocate anything in the semantics, they are
     * just aliases.
     *)
    Fixpoint wp_decl (ρ : region) (x : ident) (ty : type) (init : option Expr) (dtor : option obj_name)
               (k : region -> Kpreds -> mpred) (Q : Kpreds)
               (* ^ Q is the continuation for after the declaration
                *   goes out of scope.
                * ^ k is the rest of the declaration
                *)
    : mpred :=
      match ty with
      | Tvoid => lfalse

        (* primitives *)
      | Tpointer _
      | Tmember_pointer _ _
      | Tbool
      | Tchar _ _
      | Tint _ _ =>
        Forall a : ptr,
        let done :=
            k (Rbind x a ρ) (Kfree (_at (_eq a) (anyR (erase_qualifiers ty) 1)) Q)
        in
        let continue := done in
        match init with
        | None =>
          _at (_eq a) (uninitR (erase_qualifiers ty) 1) -* continue
        | Some init =>
          wp_prval ρ init (fun v free => free **
                              _at (_eq a) (primR (erase_qualifiers ty) 1 v) -* continue)
        end

      | Tnamed cls =>
        Forall a, _at (_eq a) (uninitR (erase_qualifiers ty) 1) -*
                  let destroy :=
                      match dtor with
                      | None => fun x => x
                      | Some dtor => destruct_obj dtor cls (Vptr a)
                      end (_at (_eq a) (anyR (erase_qualifiers ty) 1))
                  in
                  let continue :=
                      k (Rbind x a ρ) (Kfree destroy Q)
                  in
                  match init with
                  | None => continue
                  | Some init =>
                    wp_init ρ ty (Vptr a) (not_mine init) (fun free => free ** continue)
                  end
      | Tarray ty' N =>
        Forall a, _at (_eq a) (uninitR (erase_qualifiers ty) 1) -*
                  let destroy : mpred :=
                      match dtor with
                      | None => fun x => x
                      | Some dtor => destruct ty (Vptr a) dtor
                      end (_at (_eq a) (anyR (erase_qualifiers ty) 1))
                  in
                  let continue :=
                      k (Rbind x a ρ) (Kfree (_at (_eq a) (anyR (erase_qualifiers ty) 1)) Q)
                  in
                  match init with
                  | None => continue
                  | Some init =>
                    wp_init ρ ty (Vptr a) (not_mine init) (fun free => free ** continue)
                  end

        (* references *)
      | Trv_reference t
      | Treference t =>
        match init with
        | None => lfalse
          (* ^ references must be initialized *)
        | Some init =>
          (* i should use the type here *)
          wp_lval ρ init (fun a free =>
             Exists p, [| a = Vptr p |] **
             (free ** k (Rbind x p ρ) Q))
        end

      | Tfunction _ _ => lfalse (* not supported *)

      | Tqualified _ ty => wp_decl ρ x ty init dtor k Q
      | Tnullptr =>
        Forall a : ptr,
        let done :=
            k (Rbind x a ρ) (Kfree (_at (_eq a) (anyR (erase_qualifiers ty) 1)) Q)
        in
        let continue := done in
        match init with
        | None =>
          _at (_eq a) (primR Tnullptr 1 (Vptr nullptr)) -* continue
        | Some init =>
          wp_prval ρ init (fun v free => free **
                              _at (_eq a) (primR (erase_qualifiers ty) 1 v) -* continue)
        end
      | Tfloat _ => lfalse (* not supportd *)
      | Tarch _ _ => lfalse (* not supported *)
      end.

    Fixpoint wp_decls (ρ : region) (ds : list VarDecl)
             (k : region -> Kpreds -> mpred) (Q : Kpreds) : mpred :=
      match ds with
      | nil => k ρ Q
      | {| vd_name := x ; vd_type := ty ; vd_init := init ; vd_dtor := dtor |} :: ds =>
        |> wp_decl ρ x ty init dtor (fun ρ => wp_decls ρ ds k) Q
      end.

    (* note(gmm): this rule is non-compositional because
     * wp_decls requires the rest of the block computation
     *)
    Fixpoint wp_block (ρ : region) (ss : list Stmt) (Q : Kpreds) : mpred :=
      match ss with
      | nil => Q.(k_normal)
      | Sdecl ds :: ss =>
        wp_decls ρ ds (fun ρ => wp_block ρ ss) Q
      | s :: ss =>
        |> wp ρ s (Kseq (wp_block ρ ss) Q)
      end.

    Axiom wp_seq : forall ρ Q ss,
        wp_block ρ ss Q |-- wp ρ (Sseq ss) Q.

    Axiom wp_if : forall ρ e thn els Q,
        |> wp_prval ρ e (fun v free =>
             match is_true v with
             | None => lfalse
             | Some c =>
               free **
               if c then
                 wp ρ thn Q
               else
                 wp ρ els Q
             end)
      |-- wp ρ (Sif None e thn els) Q.

    Axiom wp_if_decl : forall ρ d e thn els Q,
        wp ρ (Sseq (Sdecl (d :: nil) :: Sif None e thn els :: nil)) Q
        |-- wp ρ (Sif (Some d) e thn els) Q.

    (* note(gmm): this rule is not sound for a total hoare logic
     *)
    Axiom wp_while : forall ρ t b Q I,
        I |-- wp ρ (Sif None t (Sseq (b :: Scontinue :: nil)) Sskip)
                (Kloop I Q) ->
        I |-- wp ρ (Swhile None t b) Q.

    Axiom wp_while_decl : forall ρ d t b Q,
        wp ρ (Sseq (Sdecl (d :: nil) :: Swhile None t b :: nil)) Q
        |-- wp ρ (Swhile (Some d) t b) Q.


    (* note(gmm): this rule is not sound for a total hoare logic
     *)
    Axiom wp_for : forall ρ test incr b Q Inv,
        match test with
        | None =>
          Inv |-- wp ρ (Sseq (b :: Scontinue :: nil))
              (Kloop match incr with
                     | None => Inv
                     | Some incr => wpAny ρ incr (fun _ _ => Inv)
                     end Q)
        | Some test =>
          Inv |-- wp ρ (Sif None test (Sseq (b :: Scontinue :: nil)) Sskip)
              (Kloop match incr with
                     | None => Inv
                     | Some incr => wpAny ρ incr (fun _ _ => Inv)
                     end Q)
        end ->
        Inv |-- wp ρ (Sfor None test incr b) Q.

    Axiom wp_for_init : forall ρ init test incr b Q,
        wp ρ (Sseq (init :: Sfor None test incr b :: nil)) Q
        |-- wp ρ (Sfor (Some init) test incr b) Q.

    Axiom wp_do : forall ρ t b Q I,
        I |-- wp ρ (Sseq (b :: (Sif None t Scontinue Sskip) :: nil)) (Kloop I Q) ->
        I |-- wp ρ (Sdo b t) Q.

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
      | Sunsupported _ => false
      end.


    (* apply the [wp] calculation to the body of a switch *)
    Fixpoint wp_switch_block (ρ : region) (e : Z) (L : Prop) (ls : list Stmt) (Q : Kpreds) : mpred :=
      match ls with
      | Scase sb :: ls =>
        let here := wp_switch_branch e sb in
        ([| here |] -* wp ρ (Sseq ls) Q) //\\
        wp_switch_block ρ e (L \/ here) ls Q
      | Sdefault :: ls =>
        [| ~L |] -* wp_switch_block ρ e L ls Q
      | s :: ls =>
        if no_case s then
          wp_switch_block ρ e L ls Q
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

    Axiom wp_switch : forall ρ e b Q,
        wp_prval ρ e (fun v free =>
                    Exists vv : Z, [| v = Vint vv |] **
                    wp_switch_block ρ vv False b (Kswitch Q))
        |-- wp ρ (Sswitch e (Sseq b)) Q.

    (* note: case and default statements are only meaningful inside of [switch].
     * this is handled by [wp_switch_block].
     *)
    Axiom wp_case : forall ρ sb Q, Q.(k_normal) |-- wp ρ (Scase sb) Q.
    Axiom wp_default : forall ρ Q, Q.(k_normal) |-- wp ρ Sdefault Q.

  End with_resolver.

End Stmt.

Declare Module S : Stmt.

Export S.
