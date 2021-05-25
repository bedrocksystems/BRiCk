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
    Variables (M : coPset) (ti : thread_info).

    Local Notation wp := (wp (resolve:=resolve) M ti).
    Local Notation wp_lval := (wp_lval (resolve:=resolve) M ti).
    Local Notation wp_prval := (wp_prval (resolve:=resolve) M ti).
    Local Notation wp_xval := (wp_xval (resolve:=resolve) M ti).
    Local Notation wp_init := (wp_init (resolve:=resolve) M ti).
    Local Notation wpe := (wpe (resolve:=resolve) M ti).
    Local Notation fspec := (fspec ti).
    Local Notation destruct_val := (destruct_val (σ:=resolve) ti) (only parsing).

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
               Forall ra : ptr, ra |-> tblockR (erase_qualifiers rty) 1 -*
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

    (* This definition performs allocation of local variables.
     *
     * note that references do not allocate anything in the semantics, they are
     * just aliases.
     *
     * TODO there is a lot of overlap between this and [wp_initialize] (which does initialization
     * of aggregate fields).
     *)
    Fixpoint wp_decl (ρ : region) (x : ident) (ty : type) (init : option Expr) (dtor : option obj_name)
               (k : region -> (mpred -> mpred) -> mpredI)
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
            k (Rbind x a ρ)
              (fun P => a |-> anyR (erase_qualifiers ty) 1 ** P)
        in
        match init with
        | None =>
          a |-> uninitR (erase_qualifiers ty) 1 -* continue
        | Some init =>
          wp_prval ρ init (fun v free => free **
              (a |-> primR (erase_qualifiers ty) 1 v -* continue))
        end

      | Tnamed cls =>
        Forall a : ptr, a |-> tblockR (σ:=resolve) ty 1 -*
                  let destroy P :=
                      destruct_val false ty a dtor (a |-> tblockR (erase_qualifiers ty) 1 ** P)
                  in
                  let continue := k (Rbind x a ρ) destroy in
                  match init with
                  | None => continue
                  | Some init =>
                    wp_init ρ ty a (not_mine init) (fun free => free ** continue)
                  end
      | Tarray ty' N =>
        Forall a : ptr, a |-> tblockR (σ:=resolve) ty 1 -*
                  let destroy P :=
                      destruct_val false ty a dtor (a |-> tblockR (σ:=resolve) (erase_qualifiers ty) 1 ** P)
                  in
                  let continue := k (Rbind x a ρ) destroy in
                  match init with
                  | None => continue
                  | Some init =>
                    wp_init ρ ty a (not_mine init) (fun free => free ** continue)
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
             (free ** k (Rbind x p ρ) (fun P => P)))
        end

      | Tfunction _ _ => UNSUPPORTED "local function declarations are not supported" (* not supported *)

      | Tqualified _ ty => wp_decl ρ x ty init dtor k
      | Tnullptr =>
        Forall a : ptr,
        let continue :=
            k (Rbind x a ρ) (fun P => a |-> anyR Tnullptr 1 ** P)
        in
        match init with
        | None =>
          a |-> primR Tnullptr 1 (Vptr nullptr) -* continue
        | Some init =>
          wp_prval ρ init (fun v free => free **
             (a |-> primR (erase_qualifiers ty) 1 v -* continue))
        end
      | Tfloat _ => UNSUPPORTED "floating point declarations" (* not supportd *)
      | Tarch _ _ => UNSUPPORTED "architecure specific declarations" (* not supported *)
      end.

    Lemma decl_prim:
         ∀ (x : ident) (ρ : region) (init : option Expr) (ty : type)
           (k k' : region → (mpred → mpred) → mpred),
             Forall (a : region) (b b' : mpred → mpredI), (Forall rt rt' : mpred, (rt -* rt') -* b rt -* b' rt') -* k a b -* k' a b'
         |-- (Forall a : ptr,
                         match init with
                         | Some init0 =>
                           wp_prval ρ init0
                                    (λ (v : val) (free : FreeTemps),
                                     free **
                                          (a |-> heap_pred.primR (erase_qualifiers ty) 1 v -*
                                             k (Rbind x a ρ) (λ P : mpred, a |-> heap_pred.anyR (erase_qualifiers ty) 1 ** P)))
                         | None =>
                           a |-> heap_pred.uninitR (erase_qualifiers ty) 1 -*
                             k (Rbind x a ρ) (λ P : mpred, a |-> heap_pred.anyR (erase_qualifiers ty) 1 ** P)
                         end) -*
         (Forall a : ptr,
                     match init with
                     | Some init0 =>
                       wp_prval ρ init0
                                (λ (v : val) (free : FreeTemps),
                                 free **
                                      (a |-> heap_pred.primR (erase_qualifiers ty) 1 v -*
                                         k' (Rbind x a ρ) (λ P : mpred, a |-> heap_pred.anyR (erase_qualifiers ty) 1 ** P)))
                     | None =>
                       a |-> heap_pred.uninitR (erase_qualifiers ty) 1 -*
                         k' (Rbind x a ρ) (λ P : mpred, a |-> heap_pred.anyR (erase_qualifiers ty) 1 ** P)
                     end).
    Proof.
      destruct init; intros.
      { iIntros "K h" (a); iSpecialize ("h" $! a); iRevert "h"; iApply wp_prval_frame; first by reflexivity.
        iIntros (v f) "[$ h] h'"; iDestruct ("h" with "h'") as "h"; iRevert "h"; iApply "K".
        iIntros (??) "h [$ x]"; iApply "h"; auto. }
      { iIntros "K h" (a); iSpecialize ("h" $! a); iRevert "h".
        iIntros "A B".  iDestruct ("A" with "B") as "A"; iRevert "A"; iApply "K".
        iIntros (??) "X [$ a]"; iApply "X"; eauto. }
    Qed.

    Lemma wp_decl_frame : forall x ρ init ty dtor (k k' : region -> (mpred -> mpred) -> mpred),
        Forall a (b b' : _), (Forall rt rt' : mpred, (rt -* rt') -* b rt -* b' rt') -* k a b -* k' a b'
        |-- wp_decl ρ x ty init dtor k -* wp_decl ρ x ty init dtor k'.
    Proof.
      induction ty using type_ind'; simpl;
        try solve [ intros; apply decl_prim with (ty:=Tptr ty)
                  | intros; apply decl_prim with (ty:=Tint _ _)
                  | intros; apply decl_prim with (ty:=Tbool)
                  | intros; apply decl_prim with (ty:=Tmember_pointer _ _)
                  | intros; iIntros "? []"
                  | intros; iIntros "? $"
                  ].
      { destruct init; intros.
        { iIntros "X"; iApply wp_lval_frame; first reflexivity.
          iIntros (??) "[$ k]"; iRevert "k"; iApply "X".
          iIntros (??) "$". }
        { iIntros "? $". } }
       { destruct init; intros.
        { iIntros "X"; iApply wp_lval_frame; first reflexivity.
          iIntros (??) "[$ k]"; iRevert "k"; iApply "X".
          iIntros (??) "$". }
        { iIntros "? $". } }
       { destruct init; intros.
         { iIntros "X Y" (?) "a"; iDestruct ("Y" with "a") as "Y"; iRevert "Y".
           iApply wp_init_frame; first reflexivity.
           iIntros (?) "[$ k]"; iRevert "k"; iApply "X".
           clear. iStopProof. induction (rev (seq 0 (N.to_nat sz))); simpl.
           { iIntros "_" (??) "X [$ y]"; iApply "X"; eauto. }
           { iIntros "_" (??) "X [$ y]"; iRevert "y".
             iApply destruct_val_frame; by iApply IHl. } }
         { iIntros "X Y" (?) "a"; iDestruct ("Y" with "a") as "Y"; iRevert "Y".
           iApply "X".
           clear. iStopProof. induction (rev (seq 0 (N.to_nat sz))); simpl.
           { iIntros "_" (??) "X [$ y]"; iApply "X"; eauto. }
           { iIntros "_" (??) "X [$ y]"; iRevert "y".
             iApply destruct_val_frame; by iApply IHl. } } }
       { intros. iIntros "X y" (a) "z".
         iDestruct ("y" with "z") as "y"; iRevert "y".
         destruct init.
         { iApply wp_init_frame; first reflexivity.
           iIntros (?) "[$ x]"; iRevert "x"; iApply "X".
           case_match; last iIntros (??) "? []".
           case_match; try iIntros (??) "? []".
           { iIntros (??) "k x !>".
             iRevert "x"; iApply mspec_frame.
             iIntros (_) "[? ?]"; iFrame; by iApply "k". }
           { iIntros (??) "k x !>".
             iRevert "x"; iApply mspec_frame.
             iIntros (_) "[? ?]"; iFrame; by iApply "k". } }
         { iApply "X".
           case_match; last iIntros (??) "? []".
           case_match; try iIntros (??) "? []".
           { iIntros (??) "k x !>".
             iRevert "x"; iApply mspec_frame.
             iIntros (_) "[? ?]"; iFrame; by iApply "k". }
           { iIntros (??) "k x !>".
             iRevert "x"; iApply mspec_frame.
             iIntros (_) "[? ?]"; iFrame; by iApply "k". } } }
       { intros. iIntros "X"; iApply IHty; eauto. }
       { intros; destruct init; iIntros "k Y" (a).
         { iDestruct ("Y" $! a) as "Y"; iRevert "Y".
           iApply wp_prval_frame; first reflexivity.
           iIntros (??) "[$ z] x"; iDestruct ("z" with "x") as "z"; iRevert "z".
           iApply "k". iIntros (??) "x [$ y]"; iApply "x"; eauto. }
         { iDestruct ("Y" $! a) as "Y"; iRevert "Y".
           iIntros "x y"; iDestruct ("x" with "y") as "x"; iRevert "x".
           iApply "k". iIntros (??) "x [$ y]"; iApply "x"; eauto. } }
    Qed.

    Fixpoint wp_decls (ρ : region) (ds : list VarDecl)
             (k : region -> (mpred -> mpred) -> mpred) : mpred :=
      match ds with
      | nil => k ρ (fun P => P)%I
      | {| vd_name := x ; vd_type := ty ; vd_init := init ; vd_dtor := dtor |} :: ds =>
        |> wp_decl ρ x ty init dtor (fun ρ free => wp_decls ρ ds (fun ρ free' => k ρ (fun P => free' (free P))))
      end.

    Lemma wp_decls_frame : forall ds ρ (Q Q' : region -> (mpred -> mpred) -> mpred),
        Forall a (b b' : _), (Forall rt rt' : mpred, (rt -* rt') -* b rt -* b' rt') -* Q a b -* Q' a b'
        |-- wp_decls ρ ds Q -* wp_decls ρ ds Q'.
    Proof.
      induction ds; simpl; intros.
      - iIntros "a"; iApply "a". iIntros (??) "$".
      - iIntros "a b"; iNext; iRevert "b".
        iApply wp_decl_frame.
        iIntros (???) "b". iApply IHds. iIntros (???) "X". iApply "a".
        iIntros (??) "h". iApply "X". iApply "b". eauto.
    Qed.

    Fixpoint wp_block (ρ : region) (ss : list Stmt) (Q : Kpred) : mpred :=
      match ss with
      | nil => |> Q Normal
      | Sdecl ds :: ss =>
        wp_decls ρ ds (fun ρ free => |> wp_block ρ ss (Kat_exit free Q))
      | s :: ss =>
        |> wp ρ s (Kseq (wp_block ρ ss) Q)
      end.

    Lemma Kat_exit_frame b b' Q Q' :
      (Forall rt, Q rt -* Q' rt)
      |-- (Forall f f', (f -* f') -* b f -* b' f') -*
          Forall rt, Kat_exit b Q rt -* Kat_exit b' Q' rt.
    Proof.
      iIntros "a b" (rt); destruct rt => /=; iApply "b"; iApply "a".
    Qed.

    Lemma wp_block_frame : forall body ρ (Q Q' : Kpred),
        (Forall rt, Q rt -* Q' rt) |-- wp_block ρ body Q -* wp_block ρ body Q'.
    Proof.
      clear.
      induction body; simpl; intros.
      - iIntros "a b"; iNext; iApply "a"; eauto.
      - assert
          (Forall rt, Q rt -* Q' rt
           |-- (Forall ds, wp_decls ρ ds (λ (ρ0 : region) (free : mpred → mpred), |> wp_block ρ0 body (Kat_exit free Q)) -*
                           wp_decls ρ ds (λ (ρ0 : region) (free : mpred → mpred), |> wp_block ρ0 body (Kat_exit free Q'))) //\\
               ((|> wp ρ a (Kseq (wp_block ρ body) Q)) -* |> wp ρ a (Kseq (wp_block ρ body) Q'))).
        { iIntros "X"; iSplit.
          - iIntros (ds).
            iApply wp_decls_frame. iIntros (???) "x y"; iNext.
            iRevert "y"; iApply IHbody.
            iApply (Kat_exit_frame with "X"). eauto.
          - iIntros "x"; iNext; iRevert "x"; iApply wp_frame; first by reflexivity.
            iIntros (rt); destruct rt =>/=; eauto.
            iApply IHbody. eauto. }
        { iIntros "x"; iDestruct (H with "x") as "x".
          destruct a; try iDestruct "x" as "[_ $]".
          iDestruct "x" as "[x _]". iApply "x". }
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
