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

  (** the semantics, axiomatically *)
  Parameter ptr : Type.
  Parameter val : Type.
  Parameter Vptr : ptr -> val.
  Parameter Vint : Z -> val.

  Parameter eval_unop : UnOp -> type -> val -> val -> Prop.
  Parameter eval_binop : BinOp -> type -> val -> val -> val -> Prop.

  Parameter offset_ptr : val -> Z -> val.

  Parameter is_true : val -> bool.

  Parameter genv : Type.


  (** core assertions
   * note that the resource algebra contains the code memory as well as
   * the heap.
   *)
  Notation "'[|'  P  '|]'" := (only_provable P).

  (* heap points to *)
  Parameter ptsto : val -> val -> mpred.

  (* address of a local variable *)
  Parameter addr_of : ident -> val -> mpred.

  (* the pointer contains the code *)
  Parameter code_at : ptr -> Func -> mpred.
  (* code_at is freely duplicable *)
  Axiom code_at_dup : forall p f, code_at p f -|- code_at p f ** code_at p f.

  (* it might be more uniform to have this be an `mpred` *)
  Parameter glob_addr : genv -> globname -> ptr -> Prop.

  Parameter offset_of : forall {c : genv} (t : type) (f : ident) (e : Z), Prop.

  Parameter size_of : forall {c : genv} (t : type) (e : N), Prop.

  Parameter align_of : forall {c : genv} (t : type) (e : N), Prop.

  Parameter with_genv : (genv -> mpred) -> mpred.
  Axiom with_genv_single : forall f g,
      with_genv f //\\ with_genv g -|- with_genv (fun r => f r //\\ g r).

  Parameter func_ok_raw : Func -> list val -> (val -> mpred) -> mpred.
  (* this assserts the frame axiom for function specifications
   *)
  Axiom func_ok_frame : forall v vs Q F,
      func_ok_raw v vs Q ** F |-- func_ok_raw v vs (fun res => Q res ** F).

  Definition fspec (n : val) (ls : list val) (Q : val -> mpred) : mpred :=
    Exists f, [| n = Vptr f |] **
    Exists func, code_at f func ** func_ok_raw func ls Q.


  Definition function_spec (ret : type) (targs : list type) : Type :=
    arrowFrom val targs ((val -> mpred) -> mpred).

  (* this is the denotation of modules *)
  Fixpoint sepSPs (ls : list mpred) : mpred :=
    match ls with
    | nil => empSP
    | l :: ls => l ** sepSPs ls
    end.

  Fixpoint denoteDecl (ns : list ident) (d : Decl) : mpred :=
    match d with
    | Dvar v _ _ =>
      let n := {| g_path := ns ; g_name := v |} in
      Exists a, with_genv (fun resolve => [| glob_addr resolve n a |])
    | Dtypedef _ _ => empSP
                       (* note(gmm): this is compile time, and shouldn't be a
                        * problem.
                        *)
    | Dfunction n f =>
      let n := {| g_path := ns ; g_name := n |} in
      match f.(f_body) return mpred with
      | None =>
        Exists a, with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\
                  code_at a f
      end
    | Dmethod n t f =>
      let n := {| g_path := t.(g_path) ++ t.(g_name) :: nil ; g_name := n |} in
      Exists a,
      with_genv (fun resolve => [| glob_addr resolve n a |]) //\\
                code_at a f
    | Dstruct _ _ => empSP
      (* ^ this should really record size and offset information
       *)
    | Denum _ _ _ => empSP
      (* ^ this should record enumeration information
       *)
    | Dnamespace n ds =>
      sepSPs (map (denoteDecl (ns ++ n :: nil)) ds)
    | Dextern ds =>
      sepSPs (map (denoteDecl ns) ds)
    | Dtemplated _ _ ds =>
      sepSPs (map (denoteDecl ns) ds)
    end.

  (** Weakest pre-condition for expressions
   *)
  Variant mode : Set := Lvalue | Rvalue.

  (* todo(gmm): `wpe` should be indexed by types *)
  Parameter wpe
  : forall (resolve : genv), mode -> Expr -> (val -> mpred) -> mpred.

  (* note(gmm): the handling variables wrt lvalue and rvalues isn't correct
   * right now.
   *
   * primitives, e.g. int, int*:
   *    local x val ~ (Ex a, addr_of x a ** ptsto a val)
   * references, int&:
   *    ref x a'     ~ (Ex a, addr_of x a ** ptsto a a')
   *    (references are modeled as pointers)
   *    -- if this is true, then i can simplify things a little bit.
   * structures, T:
   *    local x (Inv y)
   *)


  (* the biggest question in these semantics is how types fit into things.
   * > C semantics doesn't use a lot of implicit casts.
   *)
  Section with_resolver.
    Context {resolve : genv}.

    Definition wp_rhs : Expr -> (val -> mpred) -> mpred :=
      wpe resolve Rvalue.
    Definition wp_lhs : Expr -> (val -> mpred) -> mpred :=
      wpe resolve Lvalue.

    Fixpoint wps (es : list Expr) (Q : list val -> mpred) : mpred :=
      match es with
      | nil => Q nil
      | e :: es => wp_rhs e (fun v => wps es (fun vs => Q (cons v vs)))
      end.

    (* todo(gmm): maintain stack variables through regions
     *)
    Parameter has_type : val -> type -> Prop.

    Definition tptsto (ty : type) (p : val) (v : val) : mpred :=
      ptsto p v ** (embed (has_type v ty) //\\ empSP).

    Axiom wp_rhs_int : forall n ty Q,
        embed (has_type (Vint n) ty) //\\ Q (Vint n)
        |-- wp_rhs (Eint n ty) Q.

    Axiom wp_rhs_bool : forall (b : bool) Q,
        (if b
         then Q (Vint 1)
         else Q (Vint 0))
        |-- wp_rhs (Ebool b) Q.

    (* todo(gmm): what about the type? *)
    Axiom wp_lhs_lvar : forall x Q,
      Exists a, (addr_of x a ** ltrue) //\\ Q a
      |-- wp_lhs (Evar (Lname x)) Q.

    (* what about the type? if it exists *)
    Axiom wp_lhs_gvar : forall x Q,
      Exists a, [| glob_addr resolve x a |] ** Q (Vptr a)
      |-- wp_lhs (Evar (Gname x)) Q.

    Axiom wp_lhs_member : forall e f Q,
      wp_lhs e (fun base =>
         Exists offset,
                [| @offset_of resolve (Tref f.(f_type)) f.(f_name) offset |]
           ** Q (offset_ptr base offset))
      |-- wp_lhs (Emember e f) Q.

    (* y = *x; *)
    Axiom wp_rhs_deref : forall e ty Q,
        wp_rhs e (fun a => Exists v, (tptsto ty a v ** ltrue) -* Q v)
        |-- wp_rhs (Ederef e) Q.

    (* *x = 3; *)
    Axiom wp_lhs_deref : forall e (Q : val -> mpred),
        wp_rhs e Q
        |-- wp_lhs (Ederef e) Q.

    Axiom wp_rhs_addrof : forall e Q,
        wp_lhs e Q
        |-- wp_rhs (Eaddrof e) Q.

    Axiom wp_rhs_unop : forall o e ty Q,
        wp_rhs e (fun v => Exists v', embed (eval_unop o ty v v') //\\ Q v')
        |-- wp_rhs (Eunop o e) Q.

    Axiom wp_rhs_binop : forall o e1 e2 ty Q,
        wp_rhs e1 (fun v1 => wp_rhs e2 (fun v2 =>
            Exists v', embed (eval_binop o ty v1 v2 v') //\\ Q v'))
        |-- wp_rhs (Ebinop o e1 e2) Q.

    Axiom wp_rhs_cast_l2r : forall e Q,
        wp_lhs e (fun a => Exists v, (ptsto a v ** ltrue) //\\ Q v)
        |-- wp_rhs (Ecast Cl2r e) Q.

    Axiom wp_rhs_cast_noop : forall m e Q,
        wpe resolve m e Q
        |-- wpe resolve m (Ecast Cnoop e) Q.

    Axiom wp_rhs_cast_int2bool : forall m e Q,
        wpe resolve m e Q
        |-- wpe resolve m (Ecast Cint2bool e) Q.

    Axiom wp_rhs_cast : True.

    Axiom wp_rhs_seqand : forall e1 e2 Q,
        wp_rhs e1 (fun v1 =>
           if is_true v1
           then wp_rhs e2 (fun v2 =>
                                     if is_true v2
                                     then Q (Vint 1)
                                     else Q (Vint 0))
           else Q (Vint 0))
        |-- wp_rhs (Eseqand e1 e2) Q.

    Axiom wp_rhs_seqor : forall e1 e2 Q,
        wp_rhs e1 (fun v1 =>
           if is_true v1
           then Q (Vint 1)
           else wp_rhs e2 (fun v2 =>
                                     if is_true v2
                                     then Q (Vint 1)
                                     else Q (Vint 0)))
        |-- wp_rhs (Eseqor e1 e2) Q.

    Axiom wpe_comma : forall {m} e1 e2 Q,
        wpe resolve m e1 (fun _ => wpe resolve m e2 Q)
        |-- wpe resolve m (Ecomma e1 e2) Q.

    Axiom wp_rhs_condition : forall m tst th el Q,
        wp_rhs tst (fun v1 =>
           if is_true v1
           then wpe resolve m th Q
           else wpe resolve m el Q)
        |-- wpe resolve m (Eif tst th el) Q.

    Axiom wp_rhs_sizeof : forall ty Q,
        Exists sz, [| @size_of resolve ty sz |] ** Q (Vint (Z.of_N sz))
        |-- wp_rhs (Esize_of (inl ty)) Q.

    Axiom wp_lhs_assign : forall l r Q,
        wp_lhs l (fun la => wp_rhs r (fun rv =>
           (Exists v, ptsto la v) ** (ptsto la rv -* Q la)))
        |-- wp_lhs (Eassign l r) Q.

(*
    Axiom wp_rhs_postincr : forall inc_or_dec l ty Q,
        wp_lhs resolve l (fun a =>
          Exists v, Exists v', (tptsto ty a v ** embed _) -* tptsto ty a v' ** Q v)
        |-- wp_rhs resolve (Epostincr inc_or_dec l ty) Q.
*)

    Axiom wp_rhs_cast_function2pointer : forall g Q,
        wp_lhs (Evar (Gname g)) Q
        |-- wp_rhs (Ecast Cfunction2pointer (Evar (Gname g))) Q.

    Axiom wp_call : forall f es Q,
        wp_rhs f (fun f => wps es (fun vs => |> fspec f vs Q))
        |-- wp_rhs (Ecall f es) Q.

    Axiom wp_member_call : forall f obj es Q,
        Exists fa, [| glob_addr resolve f fa |] **
        wp_rhs obj (fun this => wps es (fun vs =>
            |> fspec (Vptr fa) (this :: vs) Q))
        |-- wp_rhs (Emember_call f obj es) Q.

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
         |-- wp_lhs (Eassign (Evar (Lname _x)) (Eint 0 T_int32)) (fun xa => addr_of _x xa ** tptsto T_int32 xa 0))%Z.
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
         |-- wp_lhs
             (Eassign (Ederef (Ecast Cl2r (Evar (Lname "x")))) (Eint 0 T_int32))
             (fun x => embed (x = 3)%Z //\\ local "x" x ** ptsto x 0%Z).
    Proof.
      intros.
      unfold local, local_at.
      repeat (t; simplify_wp).
    Qed.

    (* int *x ; int y ; x = &y ; *)
    Goal local _x 3%Z ** local _y 12%Z
         |-- wp_lhs (Eassign (Evar (Lname _x)) (Eaddrof (Evar (Lname _y))))
         (fun xa => addr_of _x xa ** Exists ya, addr_of _y ya ** ptsto xa ya ** ptsto ya 12)%Z.
    Proof.
      unfold local.
      repeat (t; simplify_wp).
    Qed.

    (* int *x ; int y ; *(x = &y) = 3; *)
    Goal local _x 3%Z ** local _y 9%Z
      |-- wp_lhs (Eassign (Ederef (El2r (Eassign (Evar (Lname _x)) (Eaddrof (Evar (Lname _y)))))) (Eint 3 T_int32))%Z (fun ya => local _x ya ** ptsto ya 3%Z ** addr_of _y ya).
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

    (** weakest pre-condition for statements
     *)

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
        wp_rhs e (fun res => Q.(k_return) (Some res))
        |-- wp resolve (Sreturn (Some e)) Q.

    Axiom wp_break : forall Q,
        Q.(k_break) |-- wp resolve Sbreak Q.
    Axiom wp_continue : forall Q,
        Q.(k_continue) |-- wp resolve Scontinue Q.

    Axiom wp_do : forall e Q,
        wp_rhs e (fun _ => Q.(k_normal))
        |-- wp resolve (Sexpr e) Q.

    Axiom wp_if : forall e thn els Q,
        wp_rhs e (fun v =>
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
          wp_rhs init (fun a => addr_of x a -* k (Kfree (addr_of x a) Q))
        end
      | _ =>
        match classify_type ty with
        | inl _ =>
          match init with
          | None =>
            Exists v, tlocal ty x v -* k (Kfree (Exists v', tlocal ty x v') Q)
          | Some init =>
            wp_rhs init (fun v => tlocal ty x v -* k (Kfree (Exists v', tlocal ty x v') Q))
          end
        | inr sz => (* not a primitive *)
          match init with
          | Some (Econstructor gn es) =>
            Exists ctor, [| glob_addr resolve gn ctor |] **
            wps es (fun vs =>
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

(*
    { P } - { Q } = [] (P -* wp code Q)
*)

    Fixpoint ForallEach {t u T U} (ls : list t)
    : forall (v : arrowFrom u ls T) (v' : arrowFrom u ls U)
        (P : T -> U -> list (t * u) -> mpred), mpred :=
      match ls with
      | nil => fun v v' P => P v v' nil
      | l :: ls => fun v v' P => Forall x,
                            ForallEach ls (v x) (v' x) (fun z z' xs => P z z' (cons (l, x) xs))
      end.



    Require Import Coq.Lists.List.

    Section zip.
      Context {A B C : Type} (f : A -> B -> C).
      Fixpoint zip (x : list A) (y : list B) : list C :=
        match x , y with
        | nil , _
        | _ , nil => nil
        | x :: xs , y :: ys => f x y :: zip xs ys
        end.
    End zip.

    Definition func_ok (ret : type) (params : list (ident * type))
               (body : Stmt)
               (spec : function_spec ret (map snd params))
    : Prop.
      red in spec.
      eapply forallEach. eapply spec.
      refine (fun P args => forall Q : val -> mpred,
                  (* this is what is created from the parameters *)
                  let binds := sepSPs (zip (fun '(x, t) '(_, v) => tlocal t x v) params args) in
                  (* this is what is freed on return *)
                  let frees := sepSPs (map (fun '(x, t) => Exists v, tlocal t x v) params) in
                  (binds ** P Q) |-- (wp resolve body (Kfree frees (val_return Q)))
             ).
    Qed.

(*
    Definition ht
               (ret : type) (targs : list type)
               (ghost : Type)
               (P : ghost -> arrowFrom val targs mpred)
               (Q : ghost -> arrowFrom val targs (val -> mpred))
    : function_spec ret targs.

    Definition triple
               (f : val)
               (ret : type) (targs : list type)
               (ghost : Type)
               (P : ghost -> arrowFrom val targs mpred)
               (Q : ghost -> arrowFrom val targs (val -> mpred))
    : mpred :=
      Exists p, [| f = Vptr p |] **
      Exists body, Exists fargs,
           code_at p
                   {| f_return := ret
                    ; f_params := fargs
                    ; f_body := Some body |}
      //\\ (Forall g : ghost, ForallEach P Q (fun P Q => P -* wp resolve body (val_return Q)).







      Forall vs, fspec f vs Q -* Exists res, Q res.

    Definition ht
               (ret : type) (targs : list type)
               (ghost : Type)
               (P : ghost -> arrowFrom val targs mpred)
               (Q : ghost -> arrowFrom val targs (val -> mpred))
    : function_spec ret targs.
    red.
    revert P Q.
    induction targs; simpl.
    { intros P Q Q'.
      refine (Exists g : ghost, P g -* _).
      refine (embed (
*)

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

(*

    Goal func_ok (Qmut T_int)
         [("x",(Qmut T_int))]
         (Sseq [
              (Sreturn (Some
                          (Ebinop Badd
                                  (Ecall
                                     (Ecast Cfunction2pointer
                                            (Evar
                                               (Gname {| g_path := "A" !:: NStop; g_name := "bar" |}))) [
                                       (Ebinop Badd
                                               (Ecast Cl2r
                                                      (Evar
                                                         (Lname  "x")))
                                               (Eint 5
                                                     (Qmut T_int)))])
                                  (Eint 1
                                        (Qmut T_int)))))])
         (fun x k => _).
:: nil.

*)

  End with_resolver.

End logic.
