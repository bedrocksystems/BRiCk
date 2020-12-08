(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
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
     pred path_pred heap_pred destroy wp initializers call.
Require Import bedrock.lang.cpp.heap_notations.

Module Type Stmt.
  (** weakest pre-condition for statements
   *)
  Section with_resolver.
    Context `{Σ : cpp_logic thread_info} {resolve:genv}.
    Variables (M : coPset) (ti : thread_info).

    Local Notation wp := (wp (resolve:=resolve) M ti).
    Local Notation wp_lval := (wp_lval (resolve:=resolve) M ti).
    Local Notation wp_prval := (wp_prval (resolve:=resolve) M ti).
    Local Notation wp_xval := (wp_xval (resolve:=resolve) M ti).
    Local Notation wp_glval := (wp_glval (resolve:=resolve) M ti).
    Local Notation wp_rval := (wp_rval (resolve:=resolve) M ti).
    Local Notation wp_init := (wp_init (resolve:=resolve) M ti).
    Local Notation wpe := (wpe (resolve:=resolve) M ti).
    Local Notation fspec := (fspec ti).
    Local Notation destruct_val := (destruct_val (σ:=resolve) ti) (only parsing).
    Local Notation destruct_obj := (destruct_obj (σ:=resolve) ti) (only parsing).

    Local Notation glob_def := (glob_def resolve) (only parsing).
    Local Notation _global := (@_global resolve) (only parsing).
    Local Notation _field := (@o_field resolve) (only parsing).
    Local Notation _sub := (@o_sub resolve) (only parsing).
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
           match c with
           | Prvalue =>
             if is_aggregate (type_of e) then
               (* ^ C++ erases the reference information on types for an unknown
                * reason, see http://eel.is/c++draft/expr.prop#expr.type-1.sentence-1
                * so we need to re-construct this information from the value
                * category of the expression.
                *)
               wp_init ρ (erase_qualifiers (type_of e)) (_result ρ) (not_mine e) (Q.(k_return) (Some (Vptr $ _result ρ)))
             else
               wp_prval ρ e (fun v => Q.(k_return) (Some v))
           | Lvalue =>
             wp_lval ρ e (fun v => Q.(k_return) (Some (Vptr v)))
           | Xvalue =>
             wp_xval ρ e (fun v => Q.(k_return) (Some (Vptr v)))
           end
        |-- wp ρ (Sreturn (Some (c, e))) Q.

    Axiom wp_break : forall ρ Q,
        |> Q.(k_break) |-- wp ρ Sbreak Q.
    Axiom wp_continue : forall ρ Q,
        |> Q.(k_continue) |-- wp ρ Scontinue Q.

    Axiom wp_expr : forall ρ vc e Q,
        |> wpe ρ vc e (fun _ free => free ** Q.(k_normal))
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
      | Tint _ _ =>
        Forall a : ptr,
        let continue :=
            k (Rbind x a ρ)
              (Kfree (a |-> anyR (erase_qualifiers ty) 1) Q)
        in
        match init with
        | None =>
          a |-> uninitR (erase_qualifiers ty) 1 -* continue
        | Some init =>
          wp_prval ρ init (fun v free => free **
              (a |-> primR (erase_qualifiers ty) 1 v -* continue))
        end

      | Tnamed cls =>
        Forall a : ptr, a |-> tblockR (σ:=resolve) ty -*
                  let destroy P :=
                      destruct_val ty a dtor (a |-> tblockR ty ** P)
                  in
                  let continue :=
                      k (Rbind x a ρ) (Kat_exit destroy Q)
                  in
                  match init with
                  | None => continue
                  | Some init =>
                    wp_init ρ ty a (not_mine init) (fun free => free ** continue)
                  end
      | Tarray ty' N =>
        Forall a : ptr, a |-> tblockR (σ:=resolve) ty -*
                  let destroy P :=
                      destruct_val ty a dtor (a |-> tblockR (σ:=resolve) ty ** P)
                  in
                  let continue :=
                      k (Rbind x a ρ) (Kat_exit destroy Q)
                  in
                  match init with
                  | None => continue
                  | Some init =>
                    wp_init ρ ty a (not_mine init) (fun free => free ** continue)
                  end

        (* references *)
      | Trv_reference t
      | Treference t =>
        match init with
        | None => False
          (* ^ references must be initialized *)
        | Some init =>
          (* i should use the type here *)
          wp_lval ρ init (fun p free =>
             (free ** k (Rbind x p ρ) Q))
        end

      | Tfunction _ _ => False (* not supported *)

      | Tqualified _ ty => wp_decl ρ x ty init dtor k Q
      | Tnullptr =>
        Forall a : ptr,
        let continue :=
            k (Rbind x a ρ)
              (Kfree (a |-> anyR Tnullptr 1) Q)
        in
        match init with
        | None =>
          a |-> primR Tnullptr 1 (Vptr nullptr) -* continue
        | Some init =>
          wp_prval ρ init (fun v free => free **
             (a |-> primR (erase_qualifiers ty) 1 v -* continue))
        end
      | Tfloat _ => False (* not supportd *)
      | Tarch _ _ => False (* not supported *)
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
             | None => False
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
                     | Some (vc,incr) => wpe ρ vc incr (fun _ free => free ** Inv)
                     end Q)
        | Some test =>
          Inv |-- wp ρ (Sif None test (Sseq (b :: Scontinue :: nil)) Sskip)
              (Kloop match incr with
                     | None => Inv
                     | Some (vc,incr) => wpe ρ vc incr (fun _ free => free ** Inv)
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
    Definition wp_switch_branch (s : SwitchBranch) (v : Z) : Prop :=
      match s with
      | Exact i => v = i
      | Range low high => low <= v <= high
      end%Z.

    (* This performs a syntactic check on [s] to ensure that there are no [case] or [default]
       statements. This is used to avoid missing one of these statements which would compromise
       the soundness of [wp_switch_block]
     *)
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

    Fixpoint gather_cases (ls : list Stmt) : Z -> Prop :=
      match ls with
      | Scase sb :: ls =>
        fun n' => wp_switch_branch sb n' \/ gather_cases ls n'
      | _ :: ls => gather_cases ls
      | nil => fun _ => False
      end.

    Fixpoint has_default (ls : list Stmt) : bool :=
      match ls with
      | Sdefault :: _ => true
      | _ :: ls => has_default ls
      | nil => false
      end.

    Definition or_case (P : option (Z -> Prop)) (Q : Z -> Prop) : option (Z -> Prop) :=
      match P with
      | None => Some Q
      | Some P =>  Some (fun x => P x \/ Q x)
      end.

    (** apply the [wp] calculation to the body of a switch
        the [t] argument tells you if you just processed a [case] or [default] statement.
     *)
    Section wp_switch_branch.
      Variable has_def : bool.
      Variable ρ : region.
      Variable e : Z.
      Variable Ldef : Z -> Prop.

      Fixpoint wp_switch_block (Lcur : option (Z -> Prop)) (ls : list Stmt) (Q : Kpreds) : mpred :=
        match ls with
        | Scase sb :: ls =>
          wp_switch_block (or_case Lcur (wp_switch_branch sb)) ls Q
        | Sdefault :: ls =>
          wp_switch_block (or_case Lcur Ldef) ls Q
        | s :: ls =>
          if no_case s then
            match Lcur with
            | None =>
              wp_switch_block None ls Q
            | Some Lcur =>
              ([| Lcur e |] -* wp ρ (Sseq (s :: ls)) Q) //\\
              wp_switch_block None ls Q
            end
          else
            lfalse
        | nil =>
          if has_def then ltrue else ([| Ldef e |] -* Q.(k_normal))
        end.
    End wp_switch_branch.

    Definition Kswitch (k : Kpreds) : Kpreds :=
      {| k_normal := k.(k_normal)
       ; k_return := k.(k_return)
       ; k_break  := k.(k_normal)
       ; k_continue := k.(k_continue) |}.

    Axiom wp_switch : forall ρ e b Q,
        wp_prval ρ e (fun v free =>
                    Exists vv : Z, [| v = Vint vv |] **
                    wp_switch_block (has_default b) ρ vv (fun x => ~gather_cases b x) None b (Kswitch Q))
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
