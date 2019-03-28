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
     Util Logic Semantics.
From Cpp.Auto Require Import
     Lemmas.

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

  Fixpoint wpe (cat : ValCat) (e : Expr)
           {struct e}
  : option (forall (Q : val -> FreeTemps -> mpred), mpred).
  refine
    match e with
    | Evar (Lname x) ty =>
      lvalue cat ;;
      ret (fun Q => Exists a, (addr_of r x a ** ltrue) //\\ Q a empSP)
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
      ret (fun Q => Exists a, (addr_of r "#this"%string a ** ltrue) //\\ Q a empSP)
    | Emember e f ty =>
      QT <- wpe Lvalue e ;;
      ret (fun Q => QT (fun base free =>
         Exists offset,
                [| @offset_of resolve (Tref f.(f_type)) f.(f_name) offset |]
           ** Q (offset_ptr base offset) free))
    | Esubscript e i ty =>
      let ty := drop_qualifiers ty in
      Qe <- wpe Rvalue e ;;
      Qi <- wpe Rvalue i ;;
      ret (fun Q => Qe (fun base free => Qi
         (fun idx free' =>
          Exists sz, [| @size_of resolve ty sz |] **
          Exists i, [| idx = Vint i |] **
          Q (offset_ptr base (i * Z.of_N sz)) (free' ** free))))

    | Ederef e ty =>
      lvalue cat ;;
      wpe Rvalue e
    | Eaddrof e ty =>
      rvalue cat ;;
      wpe Lvalue e
    | Eunop o e ty =>
      let ty := drop_qualifiers ty in
      rvalue cat ;;
      Qe <- wpe Rvalue e ;;
      ret (fun Q => Qe (fun v free =>
          Exists v',
          embed (eval_unop o ty ty v v') //\\ Q v' free))
    | Ecast c e ty =>
      let ty := drop_qualifiers ty in
      match c with
      | Cl2r =>
        rvalue cat ;;
        match e with
        | Evar (Lname x) _ => (* this is a very common form *)
          ret (fun Q => Exists v, (tlocal r ty x v ** ltrue) //\\ Q v empSP)
        | _ =>
          Qe <- wpe Lvalue e ;;
          ret (fun Q => Qe (fun a free =>
          Exists v, (tptsto ty a v ** ltrue) //\\ Q v free))
        end
      | Cint2bool =>
        rvalue cat ;;
        wpe Rvalue e
      | _ => ret (fun _ => lfalse)
      end
    | Eassign l rhs ty =>
      lvalue cat ;;
      Qr <- wpe Rvalue rhs ;;
      match l with
      | Evar (Lname x) ty' =>
        let ty' := drop_qualifiers ty' in
        (* note(gmm): this is a common case that has a simpler rule. *)
        ret (fun Q => Qr (fun rv free => Exists la, Exists val,
                tlocal_at r ty' x la val **
               (tlocal_at r ty' x la rv -* Q la free)))
      | _ =>
        let ty := drop_qualifiers ty in
        Ql <- wpe Lvalue l ;;
        ret (fun Q => Ql (fun la free1 =>  Qr (fun rv free2 =>
           (Exists v, tptsto ty la v) **
                     (tptsto ty la rv -* Q la (free1 ** free2)))))
      end
    | Epostinc e ty =>
      rvalue cat ;;
      let ty := drop_qualifiers ty in
      let tye := drop_qualifiers (type_of e) in
      match e with
      | Evar (Lname x) ty' =>
        let ty' := drop_qualifiers ty' in
        ret (fun Q => Exists la, Exists val, Exists val',
                tlocal_at r ty' x la val **
               [| eval_binop Badd tye tye ty val (Vint 1) val' |] **
               (tlocal_at r ty' x la val' -* Q la empSP))
      | _ =>
        Qe <- wpe Lvalue e ;;
        ret (fun Q => Qe (fun a free => Exists v', Exists v'',
              tptsto ty a v' **
              [| eval_binop Badd tye tye ty v' (Vint 1) v'' |] **
              (tptsto ty a v'' -* Q v' free)))
      end
    | _ => _
    end.
  all: refine (ret (fun Q => unsupported e)).
  Defined.

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
             addr_of r x a -* (free ** k (Kfree (addr_of r x a) Q))))
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
          ret (fun k Q => Forall xa, Forall v,
                   tlocal_at r ty x xa v -*
                   k (Kfree (Exists v', tlocal r ty x v') Q))
        | Some init =>
          Qi <- wpe Rvalue init ;;
          ret (fun k Q => Qi (fun v free => Forall xa,
                 (tlocal_at r ty x xa v
              -* (free ** k (Kfree (Exists v', tlocal r ty x v') Q)))))
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
          (* we don't need the destructor until later, but if we prove it
           * early, then we don't need to resolve it over multiple paths.
           *)
          Exists dtor, [| glob_addr resolve (gn ++ "D1")%string dtor |] **
          (* todo(gmm): is there a better way to get the destructor? *)
          Qes (fun vs free =>
                 Forall a, uninitialized_ty (Tref gn) a
              -* |> fspec (Vptr ctor) (a :: vs) ti (fun _ =>
                 addr_of r x a -*
                 (free ** k (Kat_exit (fun Q => |> fspec (Vptr dtor) (a :: nil) ti
                                   (fun _ => addr_of r x a ** uninitialized_ty (Tref gn) a ** Q)) Q)))) empSP)
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
      | Some e =>
        Qe <- wpe Rvalue e ;;
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
        ret (@Stmt.S.wp resolve ti r s)
      | Some (x, ty, init) =>
        (* todo(gmm): i should at least evaluate the declaration *)
        ret (@Stmt.S.wp resolve ti r s)
      end
    | Sexpr cat e =>
      Qe <- wpe cat e ;;
      ret (fun Q => Qe (fun _ free => free ** Q.(k_normal)))
    | _ => _
    end.
  all: refine (ret (fun _ => error "not implemented")).
  Defined.

  Theorem wp_sound : forall s K Q,
      wp s = Some Q ->
      Q K |-- @S.wp resolve ti r s K.
  Proof. Admitted.

End refl.

Require Cpp.Auto.vc.

Local Open Scope string_scope.

Lemma test:
  forall  resolve ti r (x0 : val -> mpred),
    (Forall res : val, [| res = 3%Z |] -* x0 res)
      |-- S.wp resolve ti r
      (Sseq
         (Sdecl
            (("x", Qmut T_int, Some (Eint 1 (Qmut T_int)))
               :: ("z", Qmut T_int, Some (Eint 12 (Qmut T_int)))
               :: ("k", Qmut T_int, Some (Eint 5 (Qmut T_int))) :: nil)
            :: Sseq
            (Sdecl (("y", Qmut T_int, Some (Eint 3 (Qmut T_int))) :: nil)
                   :: Sexpr Lvalue
                   (Eassign (Evar (Lname "x") (Qmut T_int))
                            (Ecast Cl2r (Evar (Lname "y") (Qmut T_int))
                                   (Qmut T_int)) (Qmut T_int)) :: nil)
            :: Sif
            (Some
               ("q", Qmut T_int,
                Some
                  (Ecast Cl2r (Evar (Lname "x") (Qmut T_int))
                         (Qmut T_int))))
            (Ecast Cint2bool
                   (Ecast Cl2r (Evar (Lname "q") (Qmut T_int))
                          (Qmut T_int)) (Qmut Tbool))
            (Sseq
               (Sreturn
                  (Some
                     (Ecast Cl2r (Evar (Lname "x") (Qmut T_int))
                            (Qmut T_int))) :: nil))
            (Sseq (Sreturn (Some (Eint 0 (Qmut T_int))) :: nil))
            :: nil)) (Kfree empSP (val_return x0)).
Proof.
  intros.
  rewrite <- wp_sound by (simpl; reflexivity).
  simpl.
  vc.work.
  rewrite is_true_int in H. inversion H.
Qed.
