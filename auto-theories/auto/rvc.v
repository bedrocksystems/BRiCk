(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Coq Require Import
     ZArith.BinInt
     Strings.String
     Lists.List.
From Cpp Require Import
     Ast Sem.
From Cpp.Sem Require Import
     Util Logic Semantics Typing.
From Cpp.Auto Require Import
     Lemmas.
From bedrock.auto.Lemmas Require Wp Eval.

(* the option monad *)
Definition lvalue (c : ValCat) : option unit :=
  match c with
  | Lvalue => Some tt
  | _ => None
  end.
Definition rvalue (c : ValCat) : option unit :=
  match c with
  | Rvalue => Some tt
  | _ => None
  end.

(* working in the option monad *)
Definition ret {t} : t -> option t := @Some t.
Definition fail {t} : option t := @None t.
Definition bind {t u} (c : option t) (k : t -> option u) : option u :=
  match c with
  | None => None
  | Some x => k x
  end.
Definition fmap {t u} (f : t -> u) (x : option t) : option u :=
  match x with
  | None => None
  | Some x => Some (f x)
  end.
Definition ap {t u} (f : option (t -> u)) (x : option t) : option u :=
  match f , x with
  | Some f , Some x => Some (f x)
  | _ , _ => None
  end.


Local Notation "x <- c  ;; k" := (bind c (fun x => k))
   (at level 60, c at next level, right associativity).
Local Notation "c  ;; k" := (bind c (fun _ => k))
   (at level 60, right associativity).

Definition join {t} (a : option (option t)) : option t :=
  match a with
  | Some (Some a) => Some a
  | _ => None
  end.


Section refl.

  Variable (resolve : genv) (ti : thread_info) (r : region).

  Local Notation "[! P !]" := (embed P).

  Definition is_const_int (ty : type) (v : Z) : option bool :=
    match drop_qualifiers ty with
    | Tint (Some n) s =>
      let n := Z.of_nat n in
      Some (if s then
             BinIntDef.Z.leb (-2 ^ (n - 1)) v &&
             BinIntDef.Z.ltb v (2 ^ (n - 1))
           else
             BinIntDef.Z.leb 0 v &&
             BinIntDef.Z.ltb v (2 ^ n))
    | Tint None _ => None
    | _ => Some false
    end%bool.

  Definition unsupported (e : Expr) : mpred.
    exact lfalse.
  Qed.

  Definition error (e : string) : mpred.
    exact lfalse.
  Qed.

  Section wpes.
    Context {T U V : Type}.
    Variable wpe : T -> option ((U -> V) -> V).

    Fixpoint wpes (es : list T) : option ((list U -> V) -> V) :=
      match es with
      | nil => ret (fun Q => Q nil)
      | e :: es =>
        Qe <- wpe e ;;
        Qes <- wpes es ;;
        ret (fun Q => Qe (fun v => Qes (fun vs => Q (cons v vs))))
      end.
  End wpes.

  (* todo(gmm): convert `FreeTemps` into `option mpred` and eliminate redundant
   * `empSP`.
   *)
  Fixpoint wpe (cat : ValCat) (e : Expr)
           {struct e}
  : option (forall (Q : val -> FreeTemps -> mpred), mpred).
  refine
    (let default :=
      match cat with
      | Rvalue => ret (wp_rhs (resolve:=resolve) ti r e)
      | Lvalue => ret (wp_lhs (resolve:=resolve) ti r e)
      | Xvalue => ret (wp_lhs (resolve:=resolve) ti r e)
      end
    in
    match e with
    | Evar (Lname x) ty =>
      lvalue cat ;;
      ret (fun Q => Exists a, (_local r x &~ a ** ltrue) //\\ Q a empSP)
    | Evar (Gname x) ty =>
      lvalue cat ;;
      ret (fun Q => Exists a, [! glob_addr resolve x a !] //\\ Q (Vptr a) empSP)
    | Eint n ty =>
      let ty := drop_qualifiers ty in
      rvalue cat ;;
      ret (fun Q =>
             match is_const_int ty n with
             | None => [! has_type (Vint n) ty !] //\\ Q (Vint n) empSP
             | Some false => lfalse
             | Some true => Q (Vint n) empSP
             end)
    | Ebool b =>
      rvalue cat ;;
      ret (fun Q => if b
                 then Q (Vint 1) empSP
                 else Q (Vint 0) empSP)
    | Ethis ty =>
      rvalue cat ;;
      ret (fun Q => Exists a, (_this r &~ a ** ltrue) //\\ Q a empSP)
    | Emember e f ty =>
      QT <- wpe Lvalue e ;;
      ret (fun Q => QT (fun base free =>
         Exists addr,
           (_offsetL (_field f) (_eq base) &~ addr ** ltrue) //\\
           Q addr free))
    | Esubscript e i ty =>
      let ty := drop_qualifiers ty in
      Qe <- wpe Rvalue e ;;
      Qi <- wpe Rvalue i ;;
      ret (fun Q => Qe (fun base free => Qi (fun idx free' =>
          Exists addr,
          (Exists i, [| idx = Vint i |] **
                     _offsetL (_sub ty i) (_eq base) &~ addr ** ltrue) //\\
          Q addr (free' ** free))))
    | Ederef e ty =>
      lvalue cat ;;
      wpe Rvalue e
    | Eaddrof e ty =>
      rvalue cat ;;
      wpe Lvalue e
    | Ebinop o lhs rhs ty =>
      rvalue cat ;; (* all operators (except assignment which isn't an operator) return rvalues *)
      Ql <- wpe Rvalue lhs ;;
      Qr <- wpe Rvalue rhs ;;
      let tl := drop_qualifiers (Typing.type_of lhs) in
      let tr := drop_qualifiers (Typing.type_of rhs) in
      let ty := drop_qualifiers ty in
      ret (fun Q => Ql (fun v1 free1 => Qr (fun v2 free2 =>
            Eval.wp_eval_binop o tl tr ty v1 v2 (fun v' => Q v' (free1 ** free2)))))
    | Eunop o e ty =>
      rvalue cat ;;
      Qe <- wpe Rvalue e ;;
      let te := drop_qualifiers (Typing.type_of e) in
      let ty := drop_qualifiers ty in
      ret (fun Q => Qe (fun v free =>
            Eval.wp_eval_unop o te ty v (fun v' => Q v' free)))
    | Ecast c e ty =>
      let ty := drop_qualifiers ty in
      match c with
      | Cl2r =>
        rvalue cat ;;
        match e with
        | Evar (Lname x) _ => (* this is a very common form *)
          ret (fun Q => Exists v, (tlocal r x (tprim ty v) ** ltrue) //\\ Q v empSP)
        | _ =>
          Qe <- wpe Lvalue e ;;
          ret (fun Q => Qe (fun a free =>
          Exists v, (_at (_eq a) (tprim ty v) ** ltrue) //\\ Q v free))
        end
      | Cint2bool =>
        rvalue cat ;;
        wpe Rvalue e
      | _ => default
      end
    | Eassign l rhs ty =>
      lvalue cat ;;
      Qr <- wpe Rvalue rhs ;;
      match l with
      | Evar (Lname x) ty' =>
        let ty' := drop_qualifiers ty' in
        (* note(gmm): this is a common case that has a simpler rule. *)
        ret (fun Q => Qr (fun rv free => Exists la,
                tlocal_at r x la (tany ty') **
               (tlocal_at r x la (tprim ty' rv) -* Q la free)))
      | _ =>
        let ty := drop_qualifiers ty in
        Ql <- wpe Lvalue l ;;
        ret (fun Q => Ql (fun la free1 =>  Qr (fun rv free2 =>
                _at (_eq la) (tany ty) **
               (_at (_eq la) (tprim ty rv) -* Q la (free1 ** free2)))))
      end
    | Epostinc e ty =>
      rvalue cat ;;
      let ty := drop_qualifiers ty in
      let tye := drop_qualifiers (type_of e) in
      match e with
      | Evar (Lname x) ty' =>
        let ty' := drop_qualifiers ty' in
        ret (fun Q => Exists la, Exists val, Exists val',
                tlocal_at r x la (tprim ty val) **
               [| eval_binop Badd tye tye ty val (Vint 1) val' |] **
               (tlocal_at r x la (tprim ty val') -* Q la empSP))
      | _ =>
        Qe <- wpe Lvalue e ;;
        ret (fun Q => Qe (fun a free => Exists v', Exists v'',
              _at (_eq a) (tprim ty v') **
              [| eval_binop Badd tye tye ty v' (Vint 1) v'' |] **
              (_at (_eq a) (tprim ty v'') -* Q v' free)))
      end
    | _ => default
    end).
  Defined.

  Theorem wpe_sound : forall e vc K Q,
      wpe vc e = Some Q ->
      Q K |-- @Wp.wpe resolve ti r vc e K.
  Proof.
    induction e; simpl; intros.
  Admitted.


  Section block.
    Variable wp : forall (s : Stmt), option (Kpreds -> mpred).

    Definition wpAnys (ve : ValCat * Expr)
    : option ((val -> FreeTemps -> mpred) -> FreeTemps -> mpred) :=
      Qe <- wpe (fst ve) (snd ve) ;;
      ret (fun Q free => Qe (fun v f => Q v (f ** free))).

    (* mostly copied from Cpp.Sem.Stmt *)
    Fixpoint wp_decl (x : ident) (ty : type) (init : option Expr)
    : option ((Kpreds -> mpred) -> Kpreds -> mpred) :=
               (* ^ Q is the continuation for after the declaration
                *   goes out of scope.
                * ^ k is the rest of the declaration
                *)
      match ty with
      | Trv_reference t
      | Treference t =>
        match init with
        | None => ret (fun _ _ => error "references must be initialized")
          (* ^ references must be initialized *)
        | Some init =>
          Qi <- wpe Lvalue init ;;
          ret (fun k Q =>
          (* i should use the type here *)
          Qi (fun a free =>
             _local r x &~ a -* (free ** k (Kfree (_local r x &~ a) Q))))
        end
      | Tfunction _ _ =>
        (* inline functions are not supported *)
        ret (fun _ _ => error "unsupported: declarations of functions")
      | Tvoid =>
        ret (fun _ _ => error "declaration of void")
      | Tpointer _
      | Tbool
      | Tchar _ _
      | Tint _ _ =>
        match init with
        | None =>
          ret (fun k Q =>
                   tlocal r x (uninit ty) -*
                   k (Kfree (tlocal r x (tany ty)) Q))
        | Some init =>
          Qi <- wpe Rvalue init ;;
          ret (fun k Q => Qi (fun v free =>
                 (tlocal r x (tprim ty v)
              -* (free ** k (Kfree (tlocal r x (tany ty)) Q)))))
        end
      | Tarray _ _ => lfalse (* todo(gmm): arrays not yet supported *)
      | Tref gn =>
        match init with
        | Some (Econstructor cnd es _) =>
          Qes <- wpes wpAnys es ;;
          ret (fun k Q =>
          (* todo(gmm): constructors and destructors need to be handled through
           * `cglob`.
           *)
          Exists ctor, [| glob_addr resolve cnd ctor |] **
          (* todo(gmm): is there a better way to get the destructor? *)
          Qes (fun vs free =>
                 Forall a, _at (_eq a) (uninit (Tref gn))
              -* |> fspec (resolve:=resolve) (Vptr ctor) (a :: vs) ti (fun _ =>
                 _local r x &~ a -*
                 (free ** k (Kat_exit (fun Q => _local r x &~ a ** |> destroy (resolve:=resolve) ti Dt_Deleting gn a Q) Q)))) empSP)
        | _ => ret (fun _ _ =>
                     error "all non-primitive declarations must have initializers")
        end
      | Tqualified _ ty => wp_decl x ty init
      end.

    (* mostly copied from Cpp.Sem.Stmt *)
    Fixpoint wp_decls (ds : list (ident * type * option Expr))
    : option ((Kpreds -> mpred) -> Kpreds -> mpred) :=
      match ds with
      | nil => ret (fun Q => Q)
      | (x, ty, init) :: ds =>
        Qd <- wp_decl x ty init ;;
        Qds <- wp_decls ds ;;
        ret (fun Q k => Qd (Qds Q) k)
      end.

    (* mostly copied from Cpp.Sem.Stmt *)
    Fixpoint wp_block (ss : list Stmt) : option (Kpreds -> mpred) :=
      match ss with
      | nil => ret (fun K => K.(k_normal))
      | Sdecl ds :: ss =>
        Qds <- wp_decls ds ;;
        Qss <- wp_block ss ;;
        ret (fun K => Qds Qss K)
      | s :: ss =>
        Qs <- wp s ;;
        Qss <- wp_block ss ;;
        ret (fun K => Qs (Kseq (Qss K) K))
      end.
  End block.

  Fixpoint wp (s : Stmt) {struct s} : option (Kpreds -> mpred).
  refine
    match s with
    | Sseq ss => wp_block wp ss
    | Sdecl ds =>
      ret (fun k => error "naked decl")
    | Sbreak => ret (fun k => k.(k_break))
    | Scontinue => ret (fun k => k.(k_continue))
    | Sreturn e =>
      match e with
      | None =>
        ret (fun k => k.(k_return) None)
      | Some (c, e) =>
        Qe <- wpe c e ;;
        ret (fun Q => Qe (fun res free => free ** Q.(k_return) (Some res)))
      end
    | Sif decl test thn els =>
      match decl with
      | None =>
        Qr <- wpe Rvalue test ;;
        Wthn <- wp thn ;;
        Wels <- wp els ;;
        ret (fun k => Qr (fun v free =>
            free ** (     ([| is_true v = true |] -* Wthn k)
                     //\\ ([| is_true v = false |] -* Wels k))))
      | Some (x, ty, init) =>
        Qd <- wp_decl x ty init ;;
        Qr <- wpe Rvalue test ;;
        Wthn <- wp thn ;;
        Wels <- wp els ;;
        (* todo(gmm): this looks like it could be fishy *)
        ret (fun K => Qd (fun K : Kpreds =>
                         let k := Kseq (k_normal K) K in
            Qr
              (fun (v : val) (free : FreeTemps) =>
               free **
               ([| is_true v = true |] -* Wthn k //\\
                [| is_true v = false |] -* Wels k))) K)
      end
    | Swhile decl test body =>
      match decl with
      | None =>
        ret (@Wp.wp resolve ti r s)
      | Some (x, ty, init) =>
        (* todo(gmm): i should at least evaluate the declaration *)
        ret (@Wp.wp resolve ti r s)
      end
    | Sexpr cat e =>
      Qe <- wpe cat e ;;
      ret (fun Q => Qe (fun _ free => free ** Q.(k_normal)))
    | _ =>
      Some (Wp.wp (resolve:=resolve) ti r s)
    end.
  Defined.

  Theorem wp_sound : forall s K Q,
      wp s = Some Q ->
      Q K |-- @Wp.wp resolve ti r s K.
  Proof. Admitted.

End refl.

Ltac simplifying :=
  progress (rewrite <- wp_sound by (simpl; reflexivity); simpl).