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
Require Import bedrock.lang.bi.errors.
Require Import bedrock.lang.cpp.heap_notations.

Module Type Stmt.
  (** weakest pre-condition for statements
   *)
  Section with_resolver.
    Context `{Σ : cpp_logic thread_info} {resolve:genv}.
    Variables (M : coPset).

    Local Notation wp := (wp M).
    Local Notation wp_lval := (wp_lval M).
    Local Notation wp_prval := (wp_prval M).
    Local Notation wp_xval := (wp_xval M).
    Local Notation wp_init := (wp_init M).
    Local Notation wpe := (wpe M).

    Local Notation glob_def := (glob_def resolve) (only parsing).

    Implicit Types Q : KpredI.

    Instance Kpred_fupd: FUpd KpredI :=
      funI l r Q => KP (fun v => |={l,r}=> Q v).

    Definition Kseq (Q : KpredI -> mpred) (k : KpredI) : KpredI :=
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

    (* loop with invariant `I` *)
    Definition Kloop (I : mpred) (Q : KpredI) : KpredI :=
      KP (funI rt =>
          match rt with
          | Break | Normal => Q Normal
          | Continue => I
          | rt => Q rt
          end).

    Definition Kfree (free : FreeTemp) : KpredI -> KpredI :=
      Kat_exit (interp free).

    Lemma Kfree_frame free Q Q' rt :
      Q rt -* Q' rt |-- Kfree free Q rt -* Kfree free Q' rt.
    Proof.
      iIntros "X". iApply Kat_exit_frame => //.
      iIntros (??) "H"; by iApply interp_frame.
    Qed.

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
               Forall ra : ptr, ra |-> tblockR (erase_qualifiers rty) 1 -*
               wp_init ρ (erase_qualifiers rty) ra (not_mine e) (fun free => interp free $ Q (ReturnVal (Vptr ra)))
             else
               wp_prval ρ e (fun v free => interp free $ Q (ReturnVal v))
           | Lvalue =>
             wp_lval ρ e (fun v free => interp free $ Q (ReturnVal (Vptr v)))
           | Xvalue =>
             wp_xval ρ e (fun v free => interp free $ Q (ReturnVal (Vptr v)))
           end
       |-- wp ρ (Sreturn (Some (c, e))) Q.
    Axiom wp_return_frame : forall ρ rv (Q Q' : KpredI),
        match rv with
        | None => Q ReturnVoid -* Q' ReturnVoid
        | Some _ =>
          (* NOTE unsound in the presence of exceptions *)
          Forall v, Q (ReturnVal v) -* Q' (ReturnVal v)
        end |-- wp ρ (Sreturn rv) Q -* wp ρ (Sreturn rv) Q'.

    Axiom wp_break : forall ρ Q,
        |> Q Break |-- wp ρ Sbreak Q.
    Axiom wp_break_frame : forall ρ (Q Q' : KpredI),
        Q Break -* Q' Break |-- wp ρ Sbreak Q -* wp ρ Sbreak Q'.

    Axiom wp_continue : forall ρ Q,
        |> Q Continue |-- wp ρ Scontinue Q.
    Axiom wp_continue_frame : forall ρ (Q Q' : KpredI),
        Q Continue -* Q' Continue |-- wp ρ Scontinue Q -* wp ρ Scontinue Q'.

    Axiom wp_expr : forall ρ vc e Q,
        |> wpe ρ vc e (fun _ free => interp free (Q Normal))
        |-- wp ρ (Sexpr vc e) Q.

    (* This definition performs allocation of local variables.
     *
     * note that references do not allocate anything in the semantics, they are
     * just aliases.
     *
     * TODO there is a lot of overlap between this and [wp_initialize] (which does initialization
     * of aggregate fields).
     *)
    Fixpoint wp_decl_var (ρ ρ_init : region) (x : ident) (ty : type) (init : option Expr)
               (k : region -> FreeTemps -> mpredI)
    : mpred :=
      match ty with
      | Tvoid => False

        (* primitives *)
      | Tpointer _
      | Tmember_pointer _ _
      | Tbool
      | Tint _ _ =>
        Forall a : ptr,
        let continue :=
            k (Rbind x a ρ) (FreeTemps.delete (erase_qualifiers ty) a)
        in
        match init with
        | None =>
          a |-> uninitR (erase_qualifiers ty) 1 -* continue
        | Some init =>
          wp_prval ρ_init init (fun v free => interp free $
              (a |-> primR (erase_qualifiers ty) 1 v -* continue))
        end

      | Tnamed cls =>
        match init with
        | None => ERROR "uninitialized class"
                 (* NOTE this does not occur within our semantics because constructors
                    are explicit. *)
        | Some init =>
          Forall a : ptr,
          a |-> tblockR (σ:=resolve) ty 1 -*
            wp_init ρ_init ty a (not_mine init) (fun free => interp free $ k (Rbind x a ρ) (FreeTemps.delete ty a))
        end
      | Tarray ty' N as rty =>
        Forall a : ptr,
        let continue := k (Rbind x a ρ) (FreeTemps.delete ty a) in
        match init with
        | None =>
          default_initialize rty a (fun free => interp free continue)
        | Some init =>
          a |-> tblockR (σ:=resolve) ty 1 -*
            wp_init ρ_init ty a (not_mine init) (fun free => interp free continue)
        end

        (* references *)
      | Trv_reference t
      | Treference t =>
        match init with
        | None => ERROR "uninitialized reference"
          (* ^ references must be initialized *)
        | Some init =>
          (* i should use the type here *)
          wp_lval ρ init (fun p free =>
             interp free $ k (Rbind x p ρ) FreeTemps.id)
        end

      | Tfunction _ _ => UNSUPPORTED "local function declarations are not supported" (* not supported *)

      | Tqualified _ ty => wp_decl_var ρ ρ_init x ty init k
      | Tnullptr =>
        Forall a : ptr,
        let continue :=
            k (Rbind x a ρ) (FreeTemps.delete Tnullptr a)
        in
        match init with
        | None =>
          a |-> primR Tnullptr 1 (Vptr nullptr) -* continue
        | Some init =>
          wp_prval ρ_init init (fun v free => interp free $
             (a |-> primR (erase_qualifiers ty) 1 v -* continue))
        end
      | Tfloat _ => UNSUPPORTED "floating point declarations" (* not supportd *)
      | Tarch _ _ => UNSUPPORTED "architecure specific declarations" (* not supported *)
      end%I%bs.

    Lemma decl_prim (x : ident) (ρ ρ_init : region) (init : option Expr) (ty : type)
           (k k' : region → FreeTemps → mpred) :
             Forall (a : region) b, k a b -* k' a b
         |-- (Forall a : ptr,
                         match init with
                         | Some init0 =>
                           wp_prval ρ_init init0
                                    (λ (v : val) (free : FreeTemps),
                                     interp free $
                                          (a |-> heap_pred.primR (erase_qualifiers ty) 1 v -*
                                             k (Rbind x a ρ) (FreeTemps.delete (erase_qualifiers ty) a)))
                         | None =>
                           a |-> heap_pred.uninitR (erase_qualifiers ty) 1 -*
                             k (Rbind x a ρ) (FreeTemps.delete (erase_qualifiers ty) a)
                         end) -*
         (Forall a : ptr,
                     match init with
                     | Some init0 =>
                       wp_prval ρ_init init0
                                (λ (v : val) (free : FreeTemps),
                                 interp free $
                                      (a |-> heap_pred.primR (erase_qualifiers ty) 1 v -*
                                         k' (Rbind x a ρ) (FreeTemps.delete (erase_qualifiers ty) a)))
                     | None =>
                       a |-> heap_pred.uninitR (erase_qualifiers ty) 1 -*
                         k' (Rbind x a ρ) (FreeTemps.delete (erase_qualifiers ty) a)
                     end).
    Proof.
      case: init=>[e | ];iIntros "K h" (a).
      { iSpecialize ("h" $! a);iRevert "h".
        iApply wp_prval_frame;first by done.
        iIntros (v f);iApply interp_frame.
        iIntros "h h'";iDestruct ("h" with "h'") as "h".
        by iApply "K". }
      { iSpecialize ("h" $! a);iRevert "h".
        iIntros "h h'";iDestruct ("h" with "h'") as "h".
        by iApply "K". }
    Qed.

    Lemma wp_decl_var_frame : forall x ρ ρ_init init ty (k k' : region -> FreeTemps -> mpred),
        Forall a (b : _), k a b -* k' a b
        |-- wp_decl_var ρ ρ_init x ty init k -* wp_decl_var ρ ρ_init x ty init k'.
    Proof.
      induction ty using type_ind'.
      { intros; apply decl_prim with (ty:=Tptr ty). }
      { destruct init; intros.
        { iIntros "X"; iApply wp_lval_frame; first reflexivity.
          iIntros (??); iApply interp_frame; iApply "X". }
        { iIntros "? $". } }
      { destruct init; intros.
        { iIntros "X"; iApply wp_lval_frame; first reflexivity.
          iIntros (??); iApply interp_frame; iApply "X". }
        { iIntros "? $". } }
      { intros; apply decl_prim with (ty:=Tint _ _). }
      { intros; iIntros "? []". }
      { destruct init; intros.
        { iIntros "X Y" (?) "a"; iDestruct ("Y" with "a") as "Y"; iRevert "Y".
          iApply wp_init_frame; first reflexivity.
          iIntros (?); iApply interp_frame; iApply "X". }
        { iIntros "X Y" (?). iSpecialize ("Y" $! a).
          iRevert "Y". iApply default_initialize_frame.
          iIntros (?); iApply interp_frame; iApply "X". } }
      { simpl. intros.
        destruct init.
        { iIntros "X Y" (a) "a".
          iDestruct ("Y" with "a") as "Y"; iRevert "Y".
          iApply wp_init_frame; first reflexivity.
          iIntros (?); iApply interp_frame; iApply "X". }
        { iIntros "? $". } }
      { intros. iIntros "? $". }
      { intros; apply decl_prim with (ty:=Tbool). }
      { intros; apply decl_prim with (ty:=Tmember_pointer _ _). }
      { intros; iIntros "? $". }
      { intros. iIntros "X"; iApply IHty; eauto. }
      { intros; destruct init; iIntros "k Y" (a).
        { iDestruct ("Y" $! a) as "Y"; iRevert "Y".
          iApply wp_prval_frame; first reflexivity.
          iIntros (??); iApply interp_frame.
          iIntros "a b". iDestruct ("a" with "b") as "a"; iRevert "a".
          iApply "k". }
        { iDestruct ("Y" $! a) as "Y"; iRevert "Y".
          iIntros "x y"; iDestruct ("x" with "y") as "x"; iRevert "x".
          iApply "k". } }
      { intros; iIntros "? $". }
    Qed.

    Fixpoint wp_decl (ρ ρ_init : region) (d : VarDecl) (k : region -> FreeTemps -> mpred) {struct d} : mpred :=
      match d with
      | Dvar x ty init => wp_decl_var ρ ρ_init x ty init k
      | Ddecompose init x ds =>
        wp_decl_var ρ_init ρ_init x (type_of init) (Some init) (fun ρ_init' free =>
          (fix continue ds ρ k free :=
             match ds with
             | nil => k ρ free
             | d :: ds => wp_decl ρ ρ_init' d (fun ρ free' => continue ds ρ k (FreeTemps.seq free' free))
             end) ds ρ k free)
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
    Qed.

    Fixpoint wp_decls (ρ ρ_init : region) (ds : list VarDecl)
             (k : region -> FreeTemps -> mpred) : mpred :=
      match ds with
      | nil => k ρ FreeTemps.id
      | d :: ds => |> wp_decl ρ ρ_init d (fun ρ free => wp_decls ρ ρ_init ds (fun ρ' free' => k ρ' (FreeTemps.seq free' free)))
      end.

    Lemma wp_decls_frame : forall ds ρ ρ_init (Q Q' : region -> FreeTemps -> mpred),
        Forall a (b : _), Q a b -* Q' a b
        |-- wp_decls ρ ρ_init ds Q -* wp_decls ρ ρ_init ds Q'.
    Proof.
      induction ds; simpl; intros.
      - iIntros "a"; iApply "a".
      - iIntros "a b"; iNext; iRevert "b".
        iApply wp_decl_frame.
        iIntros (??). iApply IHds. iIntros (??) "X". by iApply "a".
    Qed.

    Fixpoint wp_block (ρ : region) (ss : list Stmt) (Q : KpredI) : mpred :=
      match ss with
      | nil => |> Q Normal
      | Sdecl ds :: ss =>
        wp_decls ρ ρ ds (fun ρ free => |> wp_block ρ ss (Kfree free Q))
      | s :: ss =>
        |> wp ρ s (Kseq (wp_block ρ ss) Q)
      end.


    Lemma wp_block_frame : forall body ρ (Q Q' : KpredI),
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

    Axiom wp_if : forall ρ e thn els Q,
        |> wp_prval ρ e (fun v free =>
             match is_true v with
             | None => False
             | Some c =>
               interp free $
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
                     | Some (vc,incr) => wpe ρ vc incr (fun _ free => interp free Inv)
                     end Q)
        | Some test =>
          Inv |-- wp ρ (Sif None test (Sseq (b :: Scontinue :: nil)) Sskip)
              (Kloop match incr with
                     | None => Inv
                     | Some (vc,incr) => wpe ρ vc incr (fun _ free => interp free Inv)
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

    Definition Kswitch (k : KpredI) : KpredI :=
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
          wp_prval ρ e (fun v free => interp free $
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
