(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.proofmode.proofmode.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred destroy wp initializers call.
Require Import bedrock.lang.bi.errors.

Module Type Stmt.
  #[local] Arguments wp_test [_ _ _] _ _ _.

  (** weakest pre-condition for statements
   *)
  Section with_resolver.
    Context `{Σ : cpp_logic thread_info} {σ : genv}.
    Variable (tu : translation_unit).

    #[local] Notation wp := (wp tu).
    #[local] Notation interp := (interp tu).
    #[local] Notation wp_initialize := (wp_initialize tu).
    #[local] Notation default_initialize := (default_initialize tu).


    Implicit Types Q : Kpred.

    Definition Kseq (Q : Kpred -> mpred) (k : Kpred) : Kpred :=
      KP (funI rt =>
          match rt with
          | Normal => Q k
          | rt => k rt
          end).
    #[global] Instance Kseq_mono : Proper (((⊢) ==> (⊢)) ==> (⊢) ==> (⊢)) Kseq.
    Proof.
      constructor => rt; rewrite /Kseq/KP/=.
      destruct rt; try apply H; apply H0.
    Qed.

    Definition Kfree (free : FreeTemp) : Kpred -> Kpred :=
      Kat_exit (interp free).

    Lemma Kfree_frame free Q Q' rt :
      Q rt -* Q' rt |-- Kfree free Q rt -* Kfree free Q' rt.
    Proof.
      iIntros "X". iApply Kat_exit_frame => //.
      iIntros (??) "H"; by iApply interp_frame.
    Qed.

    (** * Expression Evaluation *)

    Axiom wp_expr : forall ρ vc e Q,
        |> wp_discard tu ρ vc e (fun free => interp free (Q Normal))
        |-- wp ρ (Sexpr vc e) Q.

    (** * Declarations *)

    (* This definition performs allocation of local variables.
     *
     * note that references do not allocate anything in the semantics, they are
     * just aliases.
     *
     * TODO there is a lot of overlap between this and [wp_initialize] (which does initialization
     * of aggregate fields).
     *)
    Definition wp_decl_var (ρ ρ_init : region) (x : ident) (ty : type) (init : option Expr)
               (k : region -> FreeTemp -> epred)
      : mpred :=
      Forall (addr : ptr),
        let rty := erase_qualifiers ty in
        let destroy frees :=
            interp frees (k (Rbind x addr ρ) (FreeTemps.delete rty addr))
        in
        match init with
        | Some init => wp_initialize ρ_init ty addr init $ fun frees => destroy frees
        | None => default_initialize ty addr (fun frees => destroy frees)
        end.

    Lemma wp_decl_var_frame : forall x ρ ρ_init init ty (k k' : region -> FreeTemps -> epred),
        Forall a (b : _), k a b -* k' a b
        |-- wp_decl_var ρ ρ_init x ty init k -* wp_decl_var ρ ρ_init x ty init k'.
    Proof.
      rewrite /wp_decl_var; intros.
      iIntros "X Y" (addr); iSpecialize ("Y" $! addr); iRevert "Y".
      case_match;
        [ iApply wp_initialize_frame | iApply default_initialize_frame ];
        iIntros (?); iApply interp_frame; iApply "X".
    Qed.

    (* An error used to say that thread safe initializers are not supported *)
    Record thread_safe_initializer (d : VarDecl) : Prop := {}.

    Fixpoint wp_decl (ρ ρ_init : region) (d : VarDecl) (k : region -> FreeTemps -> epred) {struct d} : mpred :=
      match d with
      | Dvar x ty init => wp_decl_var ρ ρ_init x ty init k
      | Ddecompose init x ds =>
        wp_decl_var ρ_init ρ_init x (type_of init) (Some init) (fun ρ_init' free =>
          (fix continue ds ρ k free :=
             match ds with
             | nil => k ρ free
             | d :: ds => wp_decl ρ ρ_init' d (fun ρ free' => continue ds ρ k (FreeTemps.seq free' free))
             end) ds ρ k free)
      | Dinit ts nm ty init =>
        let do_init :=
            match init with
            | None => default_initialize ty (_global nm) (k ρ)
            | Some init => wp_initialize ρ_init ty (_global nm) init (k ρ)
            end
        in
        if ts then
          UNSUPPORTED (thread_safe_initializer d)
        else
          _global nm |-> tblockR ty 1 ** do_init
      end.

    Lemma wp_decl_frame : forall ds ρ ρ_init m m',
        Forall a b, m a b -* m' a b
        |-- wp_decl ρ ρ_init ds m -* wp_decl ρ ρ_init ds m'.
    Proof.
      refine (fix IH ds := _); destruct ds; simpl; intros.
      { iIntros "X"; by iApply wp_decl_var_frame. }
      { iIntros "A". iApply wp_decl_var_frame.
        iStopProof.
        generalize dependent ρ; generalize dependent m. induction l; intros.
        { iIntros "X" (??) "Y". iApply "X". eauto. }
        { iIntros "x" (??). iApply IH.
          iIntros (??) "Z". iRevert "Z". iApply (IHl with "x"); eauto. } }
      { case_match; eauto.
        case_match.
        { iIntros "? [$ X]"; iRevert "X"; iApply wp_initialize_frame => //; iIntros (?); done. }
        { iIntros "? [$ X]"; iRevert "X"; iApply default_initialize_frame => //. } }
    Qed.

    Fixpoint wp_decls (ρ ρ_init : region) (ds : list VarDecl)
             (k : region -> FreeTemps -> epred) : mpred :=
      match ds with
      | nil => k ρ FreeTemps.id
      | d :: ds => |> wp_decl ρ ρ_init d (fun ρ free => wp_decls ρ ρ_init ds (fun ρ' free' => k ρ' (FreeTemps.seq free' free)))
      end.

    Lemma wp_decls_frame : forall ds ρ ρ_init (Q Q' : region -> FreeTemps -> epred),
        Forall a (b : _), Q a b -* Q' a b
        |-- wp_decls ρ ρ_init ds Q -* wp_decls ρ ρ_init ds Q'.
    Proof.
      induction ds; simpl; intros.
      - iIntros "a"; iApply "a".
      - iIntros "a b"; iNext; iRevert "b".
        iApply wp_decl_frame.
        iIntros (??). iApply IHds. iIntros (??) "X". by iApply "a".
    Qed.

    (** * Blocks *)

    Fixpoint wp_block (ρ : region) (ss : list Stmt) (Q : Kpred) : mpred :=
      match ss with
      | nil => |> Q Normal
      | Sdecl ds :: ss =>
        wp_decls ρ ρ ds (fun ρ free => |> wp_block ρ ss (Kfree free Q))
      | s :: ss =>
        |> wp ρ s (Kseq (wp_block ρ ss) Q)
      end.

    Lemma wp_block_frame : forall body ρ (Q Q' : Kpred),
        (Forall rt, Q rt -* Q' rt) |-- wp_block ρ body Q -* wp_block ρ body Q'.
    Proof.
      clear.
      induction body; simpl; intros.
      - iIntros "a b"; iNext; iApply "a"; eauto.
      - assert
          (Forall rt, Q rt -* Q' rt |--
                        (Forall ds, wp_decls ρ ρ ds (fun ρ' free => |> wp_block ρ' body (Kfree free Q)) -*
                                    wp_decls ρ ρ ds (fun ρ' free => |> wp_block ρ' body (Kfree free Q'))) //\\
                        (|> wp ρ a (Kseq (wp_block ρ body) Q) -*
                            |> wp ρ a (Kseq (wp_block ρ body) Q'))).
        { iIntros "X"; iSplit.
          - iIntros (ds).
            iApply wp_decls_frame. iIntros (??) "x"; iNext.
            iRevert "x"; iApply IHbody.
            iIntros (?); iApply Kfree_frame; iApply "X".
          - iIntros "x"; iNext; iRevert "x"; iApply wp_frame; first by reflexivity.
            iIntros (rt); destruct rt =>/=; eauto.
            by iApply IHbody. }
        iIntros "X".
        iDestruct (H with "X") as "X".
        destruct a; try solve [ iDestruct "X" as "[_ $]" ].
        iDestruct "X" as "[X _]". iApply "X".
    Qed.

    Axiom wp_seq : forall ρ Q ss,
        wp_block ρ ss Q |-- wp ρ (Sseq ss) Q.

    (** [if] *)

    Axiom wp_if : forall ρ e thn els Q,
        |> Unfold WPE.wp_test (wp_test tu ρ e (fun c free =>
               interp free $
               if c
               then wp ρ thn Q
               else wp ρ els Q))
      |-- wp ρ (Sif None e thn els) Q.

    Axiom wp_if_decl : forall ρ d e thn els Q,
        wp ρ (Sseq (Sdecl (d :: nil) :: Sif None e thn els :: nil)) Q
        |-- wp ρ (Sif (Some d) e thn els) Q.

    (** * Loops *)
    (* The loop rules are phrased using loop invariants. An alternative
     * is to use their 1-step unfoldings and a greatest-fixpoint.
     *
     * Inconsistency: Certain infinite loops can be optimized away
     * in C/C++. E.g. [while (1);] can be optimized to [;]. The loop
     * rules do not support these.
     *)

    (* loop with invariant `I` *)
    Definition Kloop (I : mpred) (Q : Kpred) : Kpred :=
      KP (funI rt =>
          match rt with
          | Break => Q Normal
          | Normal | Continue => I
          | rt => Q rt
          end).

    Axiom wp_while : forall ρ test body Q I,
        I |-- wp ρ (Sif None test body Sbreak) (Kloop I Q) ->
        I |-- wp ρ (Swhile None test body) Q.

    (**
       `while (T x = e) body` desugars to `{ T x = e; while (x) body }`
     *)
    Axiom wp_while_decl : forall ρ d test body Q,
            wp ρ (Sseq (Sdecl (d :: nil) :: Swhile None test body :: nil)) Q
        |-- wp ρ (Swhile (Some d) test body) Q.

    Axiom wp_for : forall ρ test incr body Q I,
        let incr_I :=
          match incr with
          | None => I
          | Some (vc,incr) => wp_discard tu ρ vc incr (fun free => interp free I)
          end
        in
        match test with
        | None =>
          I |-- wp ρ body (Kloop incr_I Q)
        | Some test =>
          I |-- wp ρ (Sif None test body Sbreak) (Kloop incr_I Q)
        end ->
        I |-- wp ρ (Sfor None test incr body) Q.

    (**
       `for (init; test; incr) body` desugars to `{ init; for (; test; incr) body }`
     *)
    Axiom wp_for_init : forall ρ init test incr b Q,
            wp ρ (Sseq (init :: Sfor None test incr b :: nil)) Q
        |-- wp ρ (Sfor (Some init) test incr b) Q.

    (** ** `do` loops *)

    Definition Kdo (ρ : region) (e : Expr) (I : mpred) (Q : Kpred) : Kpred :=
      KP (funI rt =>
          match rt with
          | Break => Q Normal
          | Continue | Normal =>
            Unfold WPE.wp_test (wp_test tu ρ e (fun c free => interp free $ if c then I else Q Normal))
          | rt => Q rt
          end).

    Axiom wp_do : forall ρ test body Q I,
        I |-- wp ρ body (Kdo ρ test I Q) ->
        I |-- wp ρ (Sdo body test) Q.

    (** * Return *)

    (* the semantics of return is like an initialization
     * expression.
     *)
    Axiom wp_return_void : forall ρ Q,
        get_return_type ρ = Tvoid ->
        Q ReturnVoid |-- wp ρ (Sreturn None) Q.

    Axiom wp_return : forall ρ e (Q : Kpred),
          (let rty := erase_qualifiers (get_return_type ρ) in
           Forall p, wp_initialize ρ rty p e (fun frees =>
                                         interp frees (Q (ReturnVal p))))
           (* ^ NOTE discard [free] because we are extruding the scope of the value *)
       |-- wp ρ (Sreturn (Some e)) Q.

    Axiom wp_return_frame : forall ρ rv (Q Q' : Kpred),
        match rv with
        | None => Q ReturnVoid -* Q' ReturnVoid
        | Some _ =>
          (* NOTE unsound in the presence of exceptions *)
          Forall v, Q (ReturnVal v) -* Q' (ReturnVal v)
        end |-- wp ρ (Sreturn rv) Q -* wp ρ (Sreturn rv) Q'.

    (** * Control flow: `break`, `continue` *)

    Axiom wp_break : forall ρ Q,
        |> Q Break |-- wp ρ Sbreak Q.
    Axiom wp_break_frame : forall ρ (Q Q' : Kpred),
        Q Break -* Q' Break |-- wp ρ Sbreak Q -* wp ρ Sbreak Q'.

    Axiom wp_continue : forall ρ Q,
        |> Q Continue |-- wp ρ Scontinue Q.
    Axiom wp_continue_frame : forall ρ (Q Q' : Kpred),
        Q Continue -* Q' Continue |-- wp ρ Scontinue Q -* wp ρ Scontinue Q'.

    (** `switch` *)

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

    (* An error to say that a `switch` block with [body] is not supported *)
    Record switch_block (body : list Stmt) : Prop := {}.

    Axiom wp_switch : forall ρ e b Q,
        match wp_switch_block (Some $ default_from_cases (get_cases b)) b with
        | None => UNSUPPORTED (switch_block b)
        | Some cases =>
          wp_operand tu ρ e (fun v free => interp free $
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

  (* ideally, we would like to use the following line, but [cbn] does not seem to
       like the !.
      Arguments wp_decl_var _ _ _ _ !_ _ /. *)
  #[global] Arguments wp_decl_var _ _ _ _ _ _ _ _ _ /.
  #[global] Arguments wp_decl _ _ _ _ _ _ _ /. (* ! should occur on [d] *)

End Stmt.

Declare Module S : Stmt.

Export S.
