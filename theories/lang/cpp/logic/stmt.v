(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
From Coq.Classes Require Import
     RelationClasses Morphisms.

From Coq Require Import
     Lists.List.
Require Import iris.proofmode.tactics.

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
    Local Notation wp_init := (wp_init (resolve:=resolve) M ti).
    Local Notation wpe := (wpe (resolve:=resolve) M ti).
    Local Notation fspec := (fspec ti).
    Local Notation destruct_val := (destruct_val (σ:=resolve) ti) (only parsing).
    Local Notation destruct_obj := (destruct_obj (σ:=resolve) ti) (only parsing).

    Local Notation glob_def := (glob_def resolve) (only parsing).
    Local Notation size_of := (@size_of resolve) (only parsing).
    Local Notation align_of := (@align_of resolve) (only parsing).
    Local Notation primR := (primR (resolve:=resolve)) (only parsing).
    Local Notation anyR := (anyR (resolve:=resolve)) (only parsing).
    Local Notation uninitR := (uninitR (resolve:=resolve)) (only parsing).

    Implicit Types Q : KpredI.

   (* the semantics of return is like an initialization
     * expression.
     *)
    Axiom wp_return_void : forall ρ Q,
        get_return_type ρ = Tvoid ->
        Q ReturnVoid |-- wp ρ (Sreturn None) Q.

    Axiom wp_return : forall ρ c e (Q : KpredI),
           match c with
           | Prvalue =>
             let rty := get_return_type ρ in
             if is_aggregate rty then
               (* ^ C++ erases the reference information on types for an unknown
                * reason, see http://eel.is/c++draft/expr.prop#expr.type-1.sentence-1
                * so we need to re-construct this information from the value
                * category of the expression.
                *)
               Forall ra : ptr, ra |-> uninitR (erase_qualifiers rty) 1 -*
               wp_init ρ (erase_qualifiers rty) ra (not_mine e) (fun free => free ** Q (ReturnVal (Vptr ra)))
             else
               wp_prval ρ e (fun v free => free ** Q (ReturnVal v))
           | Lvalue =>
             wp_lval ρ e (fun v free => free ** Q (ReturnVal (Vptr v)))
           | Xvalue =>
             wp_xval ρ e (fun v free => free ** Q (ReturnVal (Vptr v)))
           end
       |-- wp ρ (Sreturn (Some (c, e))) Q.

    Axiom wp_break : forall ρ Q,
        |> Q Break |-- wp ρ Sbreak Q.
    Axiom wp_continue : forall ρ Q,
        |> Q Continue |-- wp ρ Scontinue Q.

    Axiom wp_expr : forall ρ vc e Q,
        |> wpe ρ vc e (fun _ free => free ** Q Normal)
        |-- wp ρ (Sexpr vc e) Q.

    (* This definition performs allocation of local variables
     * note that references do not allocate anything in the semantics, they are
     * just aliases.
     *)
    Fixpoint wp_decl (ρ : region) (x : ident) (ty : type) (init : option Expr) (dtor : option obj_name)
               (k : region -> KpredI -> mpred) (Q : KpredI)
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

    Lemma wp_decl_frame : forall x ρ m (Q Q' : Kpred) init ty dtor,
        Forall rt : rt_biIndex, Q rt -* Q' rt
        |-- (Forall a (b b' : Kpred), (Forall rt, b rt -* b' rt) -* m a b -* m a b') -*
            wp_decl ρ x ty init dtor m Q -* wp_decl ρ x ty init dtor m Q'.
    Proof.
      (* TODO(gmm) postponing since I am revising initialization semantics *)
    Admitted.

    Fixpoint wp_decls (ρ : region) (ds : list VarDecl)
             (k : region -> Kpred -> mpred) (Q : Kpred) : mpred :=
      match ds with
      | nil => k ρ Q
      | {| vd_name := x ; vd_type := ty ; vd_init := init ; vd_dtor := dtor |} :: ds =>
        |> wp_decl ρ x ty init dtor (fun ρ => wp_decls ρ ds k) Q
      end.

    Lemma wp_decls_frame : forall ds ρ m (Q Q' : Kpred),
        (Forall rt : rt_biIndex, Q rt -* Q' rt)
        |-- (Forall a (b b' : Kpred), (Forall rt, b rt -* b' rt) -* m a b -* m a b') -*
            wp_decls ρ ds m Q -* wp_decls ρ ds m Q'.
    Proof.
      clear. induction ds; simpl; intros.
      - iIntros "a b c".
        iApply ("b" with "a"); eauto.
      - iIntros "a b c". iNext.
        iRevert "c". iApply (wp_decl_frame with "a").
        iIntros (???) "a". iApply (IHds with "a"). eauto.
    Qed.

    (* note(gmm): this rule is non-compositional because
     * wp_decls requires the rest of the block computation
     *)
    Fixpoint wp_block (ρ : region) (ss : list Stmt) (Q : Kpred) : mpred :=
      match ss with
      | nil => Q Normal
      | Sdecl ds :: ss =>
        wp_decls ρ ds (fun ρ => wp_block ρ ss) Q
      | s :: ss =>
        |> wp ρ s (Kseq (wp_block ρ ss) Q)
      end.

    Lemma wp_block_frame : forall body ρ (Q Q' : Kpred),
        (Forall rt, Q rt -* Q' rt) |-- wp_block ρ body Q -* wp_block ρ body Q'.
    Proof.
      clear.
      induction body; simpl; intros.
      - iIntros "A"; iApply "A".
      - assert
          (Forall rt, Q rt -* Q' rt |--
                        (Forall ds, wp_decls ρ ds (fun ρ' => wp_block ρ' body) Q -*
                                    wp_decls ρ ds (fun ρ' => wp_block ρ' body) Q') //\\
                        (|> wp ρ a (Kseq (wp_block ρ body) Q) -*
                            |> wp ρ a (Kseq (wp_block ρ body) Q'))).
        { iIntros "X"; iSplit.
          - iIntros (ds).
            iDestruct (wp_decls_frame ds ρ (fun a b => wp_block a body b)
                         with "X") as "X".
            iApply "X".
            iIntros (???) "X". by iApply IHbody.
          - iIntros "Z". iNext. iRevert "Z".
            iApply wp_frame =>//.
            iIntros (rt) => /=. destruct rt; eauto.
              by iApply IHbody. }
        iIntros "X".
        iDestruct (H with "X") as "X".
        destruct a; try solve [ iDestruct "X" as "[_ $]" ].
        iDestruct "X" as "[X _]". iApply "X".
    Qed.

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
      | Sswitch _ _ _ => true
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

    Fixpoint get_cases (ls : list Stmt) : list SwitchBranch :=
      match ls with
      | Scase sb :: ls =>
        sb :: get_cases ls
      | _ :: ls => get_cases ls
      | nil => nil
      end.

    Definition default_from_cases (ls : list SwitchBranch) (v : Z) : Prop :=
      (fold_right (fun sb P => ~wp_switch_branch sb v /\ P) True ls).


    (** apply the [wp] calculation to the body of a switch

        NOTE that the semantics of [switch] statements is *very* conservative in the
        current setup. In particular.

          1. We do not support using a [case] to jump over a variable declaration
          2. We do not support [case] statements that jump into the bodies of loops,
             i.e. Duft's device.

        Supporting 1 should not be difficult in principle.
        Full support for 2 seems to require a more sophisticated setup for [wp].
        In other work, this sort of thing is handled as essentially unstructured
        programs.

        We interpret the semantics of [wp_switch_block] by el
     *)
    Fixpoint wp_switch_block (Ldef : option (Z -> Prop)) (ls : list Stmt)
      : option (list ((Z -> Prop) * list Stmt)) :=
      match ls with
      | Scase sb :: ls =>
        (fun x => (wp_switch_branch sb, ls) :: x) <$> wp_switch_block Ldef ls
      | Sdefault :: ls =>
        match Ldef with
        | None =>
          (* NOTE in this case there were multiple [default] statements which is
             not legal *)
          None
        | Some def =>
          (fun x => (def, ls) :: x) <$> wp_switch_block None ls
        end
      | Sdecl _ :: ls' =>
        (* NOTE this check ensures that we never case past a declaration which
           could be problematic from a soundness point of view.
         *)
        if no_case (Sseq ls') then
          wp_switch_block Ldef ls'
        else
          None
      | s :: ls' =>
        if no_case s then
          wp_switch_block Ldef ls'
        else
          None
      | nil =>
        match Ldef with
        | None => Some nil
        | Some def => Some ((def, nil) :: nil)
        end
      end.

    Definition Kswitch (k : Kpred) : Kpred :=
      KP (fun rt =>
            match rt with
            | Break => k Normal
            | rt => k rt
            end).

    Axiom wp_switch_decl : forall ρ d e ls Q,
        wp ρ (Sseq (Sdecl (d :: nil) :: Sswitch None e ls :: nil)) Q
        |-- wp ρ (Sswitch (Some d) e ls) Q.

    Axiom wp_switch : forall ρ e b Q,
        match wp_switch_block (Some $ default_from_cases (get_cases b)) b with
        | None => False
        | Some cases =>
          wp_prval ρ e (fun v free => free **
                    Exists vv : Z, [| v = Vint vv |] **
                    [∧list] x ∈ cases, [| x.1 vv |] -* wp_block ρ x.2 (Kswitch Q))
        end
        |-- wp ρ (Sswitch None e (Sseq b)) Q.

    (* note: case and default statements are only meaningful inside of [switch].
     * this is handled by [wp_switch_block].
     *)
    Axiom wp_case : forall ρ sb Q, Q Normal |-- wp ρ (Scase sb) Q.
    Axiom wp_default : forall ρ Q, Q Normal |-- wp ρ Sdefault Q.

  End with_resolver.

End Stmt.

Declare Module S : Stmt.

Export S.
