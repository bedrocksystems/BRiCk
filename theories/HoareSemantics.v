From Coq.Classes Require Import
     RelationClasses Morphisms.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

Require Import Cpp.Ast.

Require Import Coq.ZArith.BinIntDef.

From auto.Tactics Require Import Discharge.

Fixpoint arrowFrom {t} u (ls : list t) (T : Type)
: Type :=
  match ls with
  | nil => T
  | cons l ls => u -> arrowFrom u ls T
  end.

Fixpoint forallEach {t u T} (ls : list t)
: forall (v : arrowFrom u ls T) (P : T -> list (t * u) -> Prop), Prop :=
  match ls with
  | nil => fun v P => P v nil
  | l :: ls => fun v P => forall x, forallEach ls (v x) (fun z xs => P z (cons (l, x) xs))
  end.

Module Type logic.

  Parameter mpred : Type.

  Parameter ILogicOps_mpred : ILogicOps mpred.
  Global Existing Instance ILogicOps_mpred.
  Parameter ILogic_mpred : ILogic mpred.
  Global Existing Instance ILogic_mpred.

  Parameter BILogicOps_mpred : BILogicOps mpred.
  Global Existing Instance BILogicOps_mpred.
  Parameter BILogic_mpred : BILogic mpred.
  Global Existing Instance BILogic_mpred.

  Parameter EmbedOp_Prop_mpred : EmbedOp Prop mpred.
  Global Existing Instance EmbedOp_Prop_mpred.
  Parameter Embed_Prop_mpred : Embed Prop mpred.
  Global Existing Instance Embed_Prop_mpred.

  Parameter ILLOperators_mpred : ILLOperators mpred.
  Global Existing Instance ILLOperators_mpred.
  Parameter ILLater_mpred : ILLater mpred.
  Global Existing Instance ILLater_mpred.

  Parameter ptr : Type.
  Parameter val : Type.
  Parameter Vptr : ptr -> val.
  Parameter Vint : Z -> val.

  (* these are the core predicates *)

  Parameter ptsto : val -> val -> mpred.

  Parameter addr_of : ident -> val -> mpred.

  Parameter genv : Type.

  (* todo(gmm): maybe `wp_lhs` and `wp_rhs` should be indexed by the types
   * todo(gmm): maybe these two should be indexed by an evaluation mechanism,
   *            i.e. lhs or rhs.
   *)
  Variant mode : Set := Lvalue | Rvalue.

  Parameter wpe
  : forall (resolve : genv), mode -> Expr -> (val -> mpred) -> mpred.
  Definition wp_rhs (resolve : genv) : Expr -> (val -> mpred) -> mpred :=
    wpe resolve Rvalue.
  Definition wp_lhs (resolve : genv) : Expr -> (val -> mpred) -> mpred :=
    wpe resolve Lvalue.

  Parameter fspec : forall (n : val) (ls : list val) (Q : val -> mpred), mpred.

  Fixpoint wps (resolve : genv)
           (es : list Expr) (Q : list val -> mpred) : mpred :=
    match es with
    | nil => Q nil
    | e :: es => wp_rhs resolve e (fun v => wps resolve es (fun vs => Q (cons v vs)))
    end.

  Notation "'[|'  P  '|]'" := (only_provable P).

(*
  Lemma provable_star : forall P (Q : Prop) R,
      Q ->
      P |-- R ->
      P |-- [| Q |] ** R.
  Proof.
    intros.
    unfold provable.
    rewrite <- empSPL.
    eapply scME; auto.
    discharge. auto.
  Qed.

  Lemma provable_intro : forall (P : Prop) Q R,
      (P -> Q |-- R) ->
      [| P |] ** Q |-- R.
  Proof.
    intros.
    unfold provable.
    rewrite embedPropExists.
    rewrite landexistsDL1.
    rewrite bilexistsscL2.
    apply lexistsL. intros.
    rewrite <- H; auto. discharge.
    eapply landL2. reflexivity.
  Qed.
*)

  (* it might be more uniform to have this be an `mpred` *)
  Parameter glob_addr : genv -> globname -> ptr -> Prop.

  Parameter offset_of : forall {c : genv} (t : type) (f : ident) (e : Z), Prop.

  Parameter size_of : forall {c : genv} (t : type) (e : N), Prop.

  Parameter offset_ptr : val -> Z -> val.

  Parameter eval_unop : UnOp -> type -> val -> val -> Prop.
  Parameter eval_binop : BinOp -> type -> val -> val -> val -> Prop.

  Parameter is_true : val -> bool.

  (* the biggest question in these semantics is how types fit into things.
   * > C semantics doesn't use a lot of implicit casts.
   *)
  Section with_resolver.
    Context {resolve : genv}.

    (* stack variables will be maintained through regions.
     *)

    Parameter has_type : val -> type -> Prop.

    Definition tptsto (ty : type) (p : val) (v : val) : mpred :=
      ptsto p v ** (embed (has_type v ty) //\\ empSP).

    Axiom wp_rhs_int : forall n ty Q,
        embed (has_type (Vint n) ty) //\\ Q (Vint n)
        |-- wp_rhs resolve (Eint n ty) Q.

    Axiom wp_rhs_bool : forall (b : bool) Q,
        (if b
         then Q (Vint 1)
         else Q (Vint 0))
        |-- wp_rhs resolve (Ebool b) Q.

    (* todo(gmm): what about the type? *)
    Axiom wp_lhs_lvar : forall x Q,
      Exists a, (addr_of x a ** ltrue) //\\ Q a
      |-- wp_lhs resolve (Evar (Lname x)) Q.

    (* what about the type? if it exists *)
    Axiom wp_lhs_gvar : forall x Q,
      Exists a, embed (glob_addr resolve x a)
           //\\ Q (Vptr a)
      |-- wp_lhs resolve (Evar (Gname x)) Q.

    Axiom wp_lhs_member : forall e f Q,
      wp_lhs resolve e (fun base =>
         Exists offset,
                embed (@offset_of resolve (Tref f.(f_type)) f.(f_name) offset)
           //\\ Q (offset_ptr base offset))
      |-- wp_lhs resolve (Emember e f) Q.

    (* y = *x; *)
    Axiom wp_rhs_deref : forall e ty Q,
        wp_rhs resolve e (fun a => Exists v, (tptsto ty a v ** ltrue) -* Q v)
        |-- wp_rhs resolve (Ederef e) Q.

    (* *x = 3; *)
    Axiom wp_lhs_deref : forall e (Q : val -> mpred),
        wp_rhs resolve e Q
        |-- wp_lhs resolve (Ederef e) Q.

    Axiom wp_rhs_addrof : forall e Q,
        wp_lhs resolve e Q
        |-- wp_rhs resolve (Eaddrof e) Q.

    Axiom wp_rhs_unop : forall o e ty Q,
        wp_rhs resolve e (fun v => Exists v', embed (eval_unop o ty v v') //\\ Q v')
        |-- wp_rhs resolve (Eunop o e) Q.

    Axiom wp_rhs_binop : forall o e1 e2 ty Q,
        wp_rhs resolve e1 (fun v1 => wp_rhs resolve e2 (fun v2 =>
            Exists v', embed (eval_binop o ty v1 v2 v') //\\ Q v'))
        |-- wp_rhs resolve (Ebinop o e1 e2) Q.

    Axiom wp_rhs_cast_l2r : forall e Q,
        wp_lhs resolve e (fun a => Exists v, (ptsto a v ** ltrue) //\\ Q v)
        |-- wp_rhs resolve (Ecast Cl2r e) Q.

    Axiom wp_rhs_cast_noop : forall m e Q,
        wpe resolve m e Q
        |-- wpe resolve m (Ecast Cnoop e) Q.

    Axiom wp_rhs_cast_int2bool : forall m e Q,
        wpe resolve m e Q
        |-- wpe resolve m (Ecast Cint2bool e) Q.

    Axiom wp_rhs_cast : True.

    Axiom wp_rhs_seqand : forall e1 e2 Q,
        wp_rhs resolve e1 (fun v1 =>
           if is_true v1
           then wp_rhs resolve e2 (fun v2 =>
                                     if is_true v2
                                     then Q (Vint 1)
                                     else Q (Vint 0))
           else Q (Vint 0))
        |-- wp_rhs resolve (Eseqand e1 e2) Q.

    Axiom wp_rhs_seqor : forall e1 e2 Q,
        wp_rhs resolve e1 (fun v1 =>
           if is_true v1
           then Q (Vint 1)
           else wp_rhs resolve e2 (fun v2 =>
                                     if is_true v2
                                     then Q (Vint 1)
                                     else Q (Vint 0)))
        |-- wp_rhs resolve (Eseqor e1 e2) Q.

    Axiom wpe_comma : forall {m} e1 e2 Q,
        wpe resolve m e1 (fun _ =>
           wpe resolve m e2 Q)
        |-- wpe resolve m (Ecomma e1 e2) Q.

    Axiom wp_rhs_condition : forall m tst th el Q,
        wp_rhs resolve tst (fun v1 =>
           if is_true v1
           then wpe resolve m th Q
           else wpe resolve m el Q)
        |-- wpe resolve m (Eif tst th el) Q.

    Axiom wp_rhs_sizeof : forall ty Q,
        Exists sz, embed (@size_of resolve ty sz) //\\ Q (Vint (Z.of_N sz))
        |-- wp_rhs resolve (Esize_of (inl ty)) Q.

    Axiom wp_lhs_assign : forall l r Q,
        wp_lhs resolve l (fun la => wp_rhs resolve r (fun rv =>
           (Exists v, ptsto la v) ** (ptsto la rv -* Q la)))
        |-- wp_lhs resolve (Eassign l r) Q.

(*
    Axiom wp_rhs_postincr : forall inc_or_dec l ty Q,
        wp_lhs resolve l (fun a =>
          Exists v, Exists v', (tptsto ty a v ** embed _) -* tptsto ty a v' ** Q v)
        |-- wp_rhs resolve (Epostincr inc_or_dec l ty) Q.
*)

    Axiom wp_call : forall f es Q,
        wp_rhs resolve f (fun f => wps resolve es (fun vs => |> fspec f vs Q))
        |-- wp_rhs resolve (Ecall f es) Q.

    Axiom wp_member_call : forall f obj es Q,
        Exists fa, [| glob_addr resolve f fa |] **
        wp_rhs resolve obj (fun this => wps resolve es (fun vs =>
            |> fspec (Vptr fa) (this :: vs) Q))
        |-- wp_rhs resolve (Emember_call f obj es) Q.

    Local Open Scope string_scope.

    Definition local (x : ident) (v : val) : mpred :=
      Exists a, addr_of x a ** ptsto a v.
    Definition tlocal (ty : type) (x : ident) (v : val) : mpred :=
      Exists a, addr_of x a ** tptsto ty a v.


    Ltac simplify_wp :=
      repeat first [ rewrite <- wp_lhs_assign
                   | rewrite <- wp_lhs_lvar
                   | rewrite <- wp_lhs_gvar
                   | rewrite <- wp_rhs_int
                   | rewrite <- wp_lhs_deref
                   | rewrite <- wp_rhs_addrof
                   | rewrite <- wp_rhs_cast_l2r
                   ].

    Parameter _x : ident.
    Parameter _y : ident.
    Coercion Vint : Z >-> val.
    Coercion Z.of_N : N >-> Z.
    Definition El2r := Ecast Cl2r.

    Parameter has_type_int : forall z,
        (Z.gtb z (-10000)%Z && Z.gtb (10000)%Z z = true)%bool ->
        has_type z T_int32.
    Parameter has_type_qual : forall v q ty,
        has_type v ty -> has_type v (Tqualified q ty).

    Ltac has_type :=
      first [ eapply has_type_int ; reflexivity
            | eapply has_type_qual ; has_type ].

    Lemma eval_add : forall ty (a b c : Z),
        c = (Z.add a b) ->
        has_type (Vint c) ty ->
        eval_binop Badd ty (Vint a) (Vint b) (Vint c).
    Admitted.

    Ltac operator :=
      first [ eapply eval_add; [ reflexivity | has_type ] ].

    Ltac t :=
      let tac := try solve [ eauto | has_type | operator ] in
      discharge tac.

    (* int x ; x = 0 ; *)
    Goal (tlocal T_int32 _x 3
         |-- wp_lhs resolve (Eassign (Evar (Lname _x)) (Eint 0 T_int32)) (fun xa => addr_of _x xa ** tptsto T_int32 xa 0))%Z.
    Proof.
      unfold tlocal.
      repeat (t; simplify_wp).
      unfold tptsto.
      t.
    Qed.

    Definition local_at (l : ident) (a : val) (v : val) : mpred :=
      addr_of l a ** ptsto a v.

    (* int *x ; *x = 0 ; *)
    Goal local "x" 3%Z ** ptsto 3%Z 12%Z
         |-- wp_lhs resolve
             (Eassign (Ederef (Ecast Cl2r (Evar (Lname "x")))) (Eint 0 T_int32))
             (fun x => embed (x = 3)%Z //\\ local "x" x ** ptsto x 0%Z).
    Proof.
      intros.
      unfold local, local_at.
      repeat (t; simplify_wp).
    Qed.

    (* int *x ; int y ; x = &y ; *)
    Goal local _x 3%Z ** local _y 12%Z
         |-- wp_lhs resolve (Eassign (Evar (Lname _x)) (Eaddrof (Evar (Lname _y))))
         (fun xa => addr_of _x xa ** Exists ya, addr_of _y ya ** ptsto xa ya ** ptsto ya 12)%Z.
    Proof.
      unfold local.
      repeat (t; simplify_wp).
    Qed.

    (* int *x ; int y ; *(x = &y) = 3; *)
    Goal local _x 3%Z ** local _y 9%Z
      |-- wp_lhs resolve (Eassign (Ederef (El2r (Eassign (Evar (Lname _x)) (Eaddrof (Evar (Lname _y)))))) (Eint 3 T_int32))%Z (fun ya => local _x ya ** ptsto ya 3%Z ** addr_of _y ya).
    Proof.
      unfold local.
      repeat (t; simplify_wp).
    Qed.

    Fixpoint uninitializedN (size : nat) (a : val) : mpred :=
      match size with
      | 0 => empSP
      | S size => (Exists x, ptsto a x) ** uninitializedN size (offset_ptr a 1)
      end.
    Definition uninitialized (size : N) : val -> mpred :=
      uninitializedN (BinNatDef.N.to_nat size).


    (** statements *)
    Record Kpreds :=
    { k_normal : mpred
    ; k_return : option val -> mpred
    ; k_break  : mpred
    ; k_continue : mpred
    }.

    Definition void_return (P : mpred) : Kpreds :=
      {| k_normal := P
       ; k_return := fun r => match r with
                           | None => P
                           | Some _ => lfalse
                           end
       ; k_break := lfalse
       ; k_continue := lfalse
      |}.

    Definition val_return (P : val -> mpred) : Kpreds :=
      {| k_normal := lfalse
       ; k_return := fun r => match r with
                           | None => lfalse
                           | Some v => P v
                           end
       ; k_break := lfalse
       ; k_continue := lfalse
      |}.

    Definition Kseq_all (Q : mpred -> mpred) (k : Kpreds) : Kpreds :=
      {| k_normal   := Q k.(k_normal)
       ; k_return v := Q (k.(k_return) v)
       ; k_break    := Q k.(k_break)
       ; k_continue := Q k.(k_continue)
       |}.
    Definition Kfree (a : mpred) : Kpreds -> Kpreds :=
      Kseq_all (fun P => a ** P).

    Parameter wp
    : forall (resolve : genv), Stmt -> Kpreds -> mpred.

    Axiom wp_skip : forall Q, Q.(k_normal) |-- wp resolve Sskip Q.

    Axiom wp_seq_nil : forall Q,
        Q.(k_normal) |-- wp resolve (Sseq nil) Q.

    Axiom wp_seq_cons : forall c cs Q,
        wp resolve c {| k_normal   := wp resolve (Sseq cs) Q
                       ; k_break    := Q.(k_break)
                       ; k_continue := Q.(k_continue)
                       ; k_return v := Q.(k_return) v |}
        |-- wp resolve (Sseq (c :: cs)) Q.


    Axiom wp_return_void : forall Q,
        Q.(k_return) None |-- wp resolve (Sreturn None) Q.
    Axiom wp_return_val : forall e Q,
        wp_rhs resolve e (fun res => Q.(k_return) (Some res))
        |-- wp resolve (Sreturn (Some e)) Q.

    Axiom wp_break : forall Q,
        Q.(k_break) |-- wp resolve Sbreak Q.
    Axiom wp_continue : forall Q,
        Q.(k_continue) |-- wp resolve Scontinue Q.

    Axiom wp_do : forall e Q,
        wp_rhs resolve e (fun _ => Q.(k_normal))
        |-- wp resolve (Sexpr e) Q.

    Axiom wp_if : forall e thn els Q,
        wp_rhs resolve e (fun v =>
                            if is_true v then
                              wp resolve els Q
                            else
                              wp resolve thn Q)
        |-- wp resolve (Sif None e thn els) Q.

    (* note(gmm): this rule is not sound for a total hoare logic
     *)
    Axiom wp_while : forall t b Q,
        Exists I,
            (wp resolve (Sif None t (Sseq (b :: Scontinue :: nil)) Sskip)
                {| k_break    := Q.(k_normal)
                 ; k_continue := I
                 ; k_return v := Q.(k_return) v
                 ; k_normal   := Q.(k_normal) |})
        |-- wp resolve (Swhile t b) Q.

    Axiom wp_decl_nil : forall Q, Q.(k_normal) |-- wp resolve (Sdecl nil) Q.

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
    Parameter classify_type : type -> N + N.
    Definition wp_decl (x : ident) (ty : type) (init : option Expr)
               (k : Kpreds -> mpred) (Q : Kpreds)
    : mpred :=
      match ty with
      | Treference t =>
        match init with
        | None => lfalse
          (* references must be initialized *)
        | Some init =>
          (* i should use the type here *)
          wp_rhs resolve init (fun a => addr_of x a -* k (Kfree (addr_of x a) Q))
        end
      | _ =>
        match classify_type ty with
        | inl _ =>
          match init with
          | None =>
            Exists v, tlocal ty x v -* k (Kfree (Exists v', tlocal ty x v') Q)
          | Some init =>
            wp_rhs resolve init (fun v => tlocal ty x v -* k (Kfree (Exists v', tlocal ty x v') Q))
          end
        | inr sz => (* not a primitive *)
          match init with
          | Some (Econstructor gn es) =>
            Exists ctor, [| glob_addr resolve gn ctor |] **
            wps resolve es (fun vs =>
                   Exists a, Exists sz, uninitialized sz a
                -* |> fspec (Vptr ctor) (a :: vs) (fun _ => k (Kfree (uninitialized sz a) Q)))
          | _ => lfalse
            (* all non-primitive declarations must have initializers *)
          end
        end
      end.

    Axiom wp_decl_cons : forall x ty init ds Q,
        wp_decl x ty init (wp resolve (Sdecl ds)) Q
        |-- wp resolve (Sdecl ((x,ty,init) :: ds)) Q.

    Require Import Cpp.Parser.
    Import ListNotations.

    Axiom wp_rhs_cast_function2pointer : forall g Q,
        wp_lhs resolve (Evar (Gname g)) Q
               |-- wp_rhs resolve (Ecast Cfunction2pointer (Evar (Gname g))) Q.

    Ltac simplify_wps :=
      repeat first [ progress simplify_wp
                   | rewrite <- wp_skip
                   | rewrite <- wp_seq_nil
                   | rewrite <- wp_seq_cons
                   | rewrite <- wp_decl_nil
                   | rewrite <- wp_decl_cons
                   | rewrite <- wp_return_val
                   | rewrite <- wp_return_void
                   | rewrite <- wp_if
                   | rewrite <- wp_continue
                   | rewrite <- wp_break
                   | rewrite <- wp_rhs_binop
                   | rewrite <- wp_call
                   | rewrite <- wp_rhs_cast_function2pointer
                   ].


    Definition triple (p : val) (ret : type) (targs : list type)
    : arrowFrom val targs ((val -> mpred) -> mpred) -> mpred.
      refine (
          (fix rec ts (fspec : list val -> (val -> mpred) -> mpred)
           : arrowFrom val ts ((val -> mpred) -> mpred) -> mpred :=
             match ts as ts
                   return arrowFrom val ts ((val -> mpred) -> mpred) -> mpred
             with
             | nil => fun PQ => Forall Q, PQ Q -* fspec nil Q
             | t :: ts => fun PQ => Forall x, rec ts (fun xs => fspec (xs ++ x :: nil)%list) (PQ x)
             end) targs (fspec p)).
    Defined.

    Theorem triple_sound : forall p r t PQ v Z,
        triple p r (t :: nil) PQ ** PQ v Z |-- fspec p (v :: nil) Z.
    Proof.
      unfold triple.
      intros.
      rewrite sepSPC.
      rewrite bilforallscR.
      eapply lforallL with (x := v).
      rewrite bilforallscR.
      eapply lforallL with (x := Z).
      simpl.
      eapply sepSPAdj'.
      reflexivity.
    Qed.

    Theorem triple_apply : forall p r t F F' PQ v Z,
        F |-- PQ v Z ** F' ->
        triple p r (t :: nil) PQ ** F |-- fspec p (v :: nil) Z ** F'.
    Proof.
      intros.
      rewrite H.
      rewrite <- triple_sound.
      t.
    Qed.

    Definition A__bar := {| g_path := "A" !:: NStop; g_name := "bar" |}.
    Goal
           (Exists abara, [| glob_addr resolve A__bar abara |] **
            (triple (Vptr abara) T_int32 (T_int32 :: nil)
                    (fun x k => Exists v, [| x = Vint v |] ** (empSP -* k (Vint (Z.add v 1))))))
        ** local "x" 3%Z
      |-- wp resolve (Sseq [
                (Sreturn (Some
                  (Ebinop Badd
                    (Ecall
                      (Ecast Cfunction2pointer
                        (Evar
                          (Gname A__bar))) [
                        (Ebinop Badd
                          (Ecast Cl2r
                            (Evar
                              (Lname  "x")))
                          (Eint 5
                            (Qmut T_int32)))])
                    (Eint 1
                      (Qmut T_int32)))))])
      (val_return (fun val => local "x" 3%Z ** [| val = Vint 10%Z |])).
    Proof.
      intros.
      repeat (t; simplify_wps).
      simpl.
      (t; simplify_wps).
      unfold local.
      repeat (t; simplify_wps).
      etransitivity; [ | eapply spec_later_weaken ].
      repeat perm_left ltac:(idtac; perm_right ltac:(idtac; eapply triple_apply)).
      t. simplify_wps.
      t.
    Qed.


  End with_resolver.

End logic.
