(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Coq Require Import
     NArith.BinNat
     ZArith.BinInt
     Strings.String
     Lists.List.
From Cpp Require Import
     Ast Sem.
From Cpp.Sem Require Import
     Util Logic Semantics.
From Cpp.Auto Require Import
     Definitions Lemmas.
From Cpp Require Auto.vc.
From bedrock.auto.Lemmas Require Wp Eval.
Require Import bedrock.Signatures.

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
Definition guard {P Q} (b : { P } + { Q }) : option unit :=
  match b with
  | left _ => Some tt
  | right _ => None
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

Section traverse.
  Context {t u} (f : t -> option u).

  Fixpoint traverse (ls : list t) : option (list u) :=
    match ls with
    | nil => Some nil
    | l :: ls =>
      match f l , traverse ls with
      | Some x , Some xs => Some (x :: xs)
      | _ , _ => None
      end
    end.
End traverse.


Local Notation "x <- c  ;; k" := (bind c (fun x => k))
   (at level 60, c at next level, right associativity).
Local Notation "c  ;; k" := (bind c (fun _ => k))
   (at level 60, right associativity).

Definition join {t} (a : option (option t)) : option t :=
  match a with
  | Some (Some a) => Some a
  | _ => None
  end.

Definition option_eq_dec {t} (H : forall (x y : t), { x = y } + { x <> y }) : forall (x y : option t), { x = y } + { x <> y }.
Proof. decide equality. Defined.

Definition function_specs := list (globname * function_spec).

Section refl.

  Variable (resolve : genv) (ti : thread_info) (r : region)
           (specs : signature) (cu : compilation_unit).

  Local Notation "[! P !]" := (embed P).

  Definition is_const_int (ty : type) (v : Z) : option bool :=
    match drop_qualifiers ty with
    | Tint n s =>
      let n := Z.of_N n in
      Some (if s then
             BinIntDef.Z.leb (-2 ^ (n - 1)) v &&
             BinIntDef.Z.ltb v (2 ^ (n - 1))
           else
             BinIntDef.Z.leb 0 v &&
             BinIntDef.Z.ltb v (2 ^ n))
    | _ => Some false
    end%bool.

  Definition unsupported (e : Expr) : mpred := lfalse.
  Definition error (e : string) : mpred := lfalse.

  Lemma unsupported_defn : forall e,
      unsupported e -|- lfalse.
  Proof. reflexivity. Qed.

  Lemma error_defn : forall s,
      error s -|- lfalse.
  Proof. reflexivity. Qed.

  Global Opaque unsupported error.

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

  Definition wpuo (o : UnOp) (tye ty : type) : option (val -> (val -> mpred) -> mpred) :=
    match o, tye, ty with
    | Unot, Tbool, Tbool =>
      ret (fun v Q => Exists b, [| v = Vbool b |] ** Q (Vbool (negb b)))
    | Unot, _, _ => ret (fun _ _ => error "Unot needs a boolean argument and return")
    | Ubnot, Tint w s, _ =>
      guard (type_eq_dec tye ty) ;;
      ret (fun v Q => Exists vv, [| v = Vint vv |] ** Q (Vint (Z.lnot vv)))
    | Uminus, Tint w s, _ =>
      guard (type_eq_dec tye ty) ;;
      ret (fun v Q => Exists vv, [| v = Vint vv |] ** Q (Vint (- vv)))
    | _, _, _ => ret (fun _ _ => error "unrecognized unop")
    end.


  (* todo(gmm): i still need to port these *)
  Definition int_arith_ops (o : BinOp) (w : N) : option ((Z -> Z -> Prop) * (Z -> Z -> Z)) :=
    match o with
    | Badd => Some (fun _ _ => True, Z.add)
    | Bsub => Some (fun _ _ => True, Z.sub)
    | Bmul => Some (fun _ _ => True, Z.mul)
    | Bdiv => Some (fun _ b => b <> 0, Z.div)
    | Bmod => Some (fun _ b => b <> 0, Z.modulo)
    | Bshl => Some (fun _ b => 0 <= b < Z.of_N w, Z.shiftl)
    | Bshr => Some (fun _ b => 0 <= b < Z.of_N w, Z.shiftr)
    | _ => None
    end%Z.

  Definition int_rel_ops (o : BinOp) : option (Z -> Z -> Z) :=
    match o with
    | Beq => Some (fun a b => if Z.eq_dec a b then 1 else 0)
    | Bneq => Some (fun a b => if Z.eq_dec a b then 0 else 1)
    | Blt => Some (fun a b => if ZArith_dec.Z_lt_ge_dec a b then 1 else 0)
    | Bgt => Some (fun a b => if ZArith_dec.Z_gt_le_dec a b then 1 else 0)
    | Ble => Some (fun a b => if ZArith_dec.Z_le_gt_dec a b then 1 else 0)
    | Bge => Some (fun a b => if ZArith_dec.Z_ge_lt_dec a b then 1 else 0)
    | _ => None
    end%Z.

  Definition get_Zs (v1 v2 : val) (Q : Z -> Z -> mpred) : mpred :=
    Exists i1, Exists i2,
      [| v1 = Vint i1 |] **
      [| v2 = Vint i2 |] ** Q i1 i2.

  Fixpoint size_of' (fuel : nat) : type -> option N :=
    match fuel with
    | 0 => fun _ => None
    | S fuel =>
      fix size_of_ty (ty : type) : option N :=
      match ty with
      | Tbool => Some 1
      | Tpointer _ => Some pointer_size
      | Tchar w _
      | Tint w _ =>
        (* todo(gmm): restrict to [w] a multiple of 8 *)
        Some ((w + 7) / 8)%N
      | Tarray ety n =>
        match size_of_ty ety with
        | None => None
        | Some sz => Some (n * sz)%N
        end
      | Treference _
      | Trv_reference _ => None
      | Tref cls =>
        match Lemmas.find_struct cls cu with
        | None => None
        | Some str =>
          match traverse (fun x => size_of' fuel (Tref x)) str.(s_bases)
              , traverse (fun '(_, x, _) => size_of' fuel x) str.(s_fields)
          with
          | Some xs , Some ys => Some (fold_left (fun x y => x + y) (xs ++ ys) 0)
          | _ , _ => None
          end
        end
      | Tfunction _ _ => None
      | Tqualified _ t => size_of_ty t
      | Tvoid => None
      end%N
    end.

  Definition size_of := size_of' 100.

  Definition simple_int_int_op (ty : type) (w : size) (s : signed)
             (cond : option (Z -> Z -> Prop)) (f : Z -> Z -> Z)
  : val -> val -> (val -> mpred) -> mpred :=
    if s then
      (fun v1 v2 Q => get_Zs v1 v2 (fun i1 i2 =>
             let res := f i1 i2 in
             match cond with
             | None =>
               [| has_type (Vint res) ty |] **
               Q (Vint res)
             | Some c =>
               [| c i1 i2 |] **
               [| has_type (Vint res) ty |] **
               Q (Vint res)
             end))
    else
      (fun v1 v2 Q => get_Zs v1 v2 (fun i1 i2 =>
             match cond with
             | None =>
               Q (Vint (trim w (f i1 i2)))
             | Some c =>
               [| c i1 i2 |] **
               Q (Vint (trim w (f i1 i2)))
             end)).

  (* <<, >> *)
  Definition simple_int_int_shift_op (ty : type) (w : size) (s : signed)
             (f : Z -> Z -> Z)
  : val -> val -> (val -> mpred) -> mpred :=
    if s then
      (fun v1 v2 Q => get_Zs v1 v2 (fun i1 i2 =>
             let res := f i1 i2 in
             [| (0 <= i2 < w)%Z |] **
             [| has_type (Vint res) ty |] **
             Q (Vint res)))
    else
      (fun v1 v2 Q => get_Zs v1 v2 (fun i1 i2 =>
             [| (0 <= i2 < w)%Z |] **
             Q (Vint (trim w (f i1 i2))))).

  (* &&, ||, ^ *)
  Definition simple_int_int_bin_op (f : Z -> Z -> Z)
  : val -> val -> (val -> mpred) -> mpred :=
    (fun v1 v2 Q => get_Zs v1 v2 (fun i1 i2 =>
       Q (Vint (f i1 i2)))).


  Definition wpbo (o : BinOp) (tyl tyr ty : type)
  : option (val -> val -> (val -> mpred) -> mpred).
  refine
    match o with
    | Badd =>
      match tyl , tyr with
      | Tint w s , Tint _ _ =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s None (fun a b => a + b))
      | Tchar w s , Tchar _ _ =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s None (fun a b => a + b))
      | Tpointer pty , Tint _ _ =>
        guard (type_eq_dec tyl ty) ;;
        match size_of pty with
        | None =>
          ret (fun v1 v2 Q =>
                 Exists sz, Exists i2,
                 [| Semantics.size_of resolve pty sz |] **
                 [| v2 = Vint i2 |] **
                 Q (offset_ptr v1 (sz * i2)))
        | Some sz =>
          ret (fun v1 v2 Q =>
                 Exists i2,
                 [| v2 = Vint i2 |] **
                 Q (offset_ptr v1 (sz * i2)))
        end
      | Tint _ _ , Tpointer pty =>
        guard (type_eq_dec tyr ty) ;;
        match size_of pty with
        | None =>
          ret (fun v2 v1 Q =>
                 Exists sz, Exists i2,
                 [| Semantics.size_of resolve pty sz |] **
                 [| v2 = Vint i2 |] **
                 Q (offset_ptr v1 (sz * i2)))
        | Some sz =>
          ret (fun v2 v1 Q =>
                 Exists i2,
                 [| v2 = Vint i2 |] **
                 Q (offset_ptr v1 (sz * i2)))
        end
      | _ , _ =>
        ret (fun _ _ _ => error "not supported")
      end

    | Bsub =>
      match tyl , tyr with
      | Tint w s , Tint _ _ =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s None (fun a b => a - b))
      | Tchar w s , Tchar _ _ =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s None (fun a b => a - b))
      | Tpointer pty , Tint _ _ =>
        guard (type_eq_dec tyl ty) ;;
        match size_of pty with
        | None =>
          ret (fun v1 v2 Q =>
                 Exists sz, Exists i2,
                 [| Semantics.size_of resolve pty sz |] **
                 [| v2 = Vint i2 |] **
                 Q (offset_ptr v1 (sz * -i2)))
        | Some sz =>
          ret (fun v1 v2 Q =>
                 Exists i2,
                 [| v2 = Vint i2 |] **
                 Q (offset_ptr v1 (sz * -i2)))
        end
      | Tint _ _ , Tpointer pty =>
        guard (type_eq_dec tyr ty) ;;
        match size_of pty with
        | None =>
          ret (fun v2 v1 Q =>
                 Exists sz, Exists i2,
                 [| Semantics.size_of resolve pty sz |] **
                 [| v2 = Vint i2 |] **
                 Q (offset_ptr v1 (sz * -i2)))
        | Some sz =>
          ret (fun v2 v1 Q =>
                 Exists i2,
                 [| v2 = Vint i2 |] **
                 Q (offset_ptr v1 (sz * -i2)))
        end
      | Tpointer pty , Tpointer _ =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        match size_of pty with
        | None =>
          ret (fun v1 v2 Q =>
               Exists sz,
               Exists base, Exists o1, Exists o2,
               [| Semantics.size_of resolve pty sz |] **
               [| v1 = offset_ptr base o1 |] **
               [| v2 = offset_ptr base o2 |] **
               [| o1 mod sz = 0 |] **
               [| o2 mod sz = 0 |] ** Q (Vint ((o1 - o2) / sz)))
        | Some sz =>
          ret (fun v1 v2 Q =>
               Exists base, Exists o1, Exists o2,
               [| v1 = offset_ptr base o1 |] **
               [| v2 = offset_ptr base o2 |] **
               [| o1 mod sz = 0 |] **
               [| o2 mod sz = 0 |] ** Q (Vint ((o1 - o2) / sz)))
        end
      | _ , _ =>
        ret (fun _ _ _ => error "not supported")
      end

    | Bmul =>
      match tyl with
      | Tint w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s None (fun a b => a * b))
      | Tchar w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s None (fun a b => a * b))
      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Bdiv =>
      match tyl with
      | Tint w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s (Some (fun _ b => b <> 0)) (fun a b => a / b))
      | Tchar w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s (Some (fun _ b => b <> 0)) (fun a b => a / b))
      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Bmod =>
      match tyl with
      | Tint w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s (Some (fun _ b => b <> 0)) (fun a b => a mod b))
      | Tchar w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_op ty w s (Some (fun _ b => b <> 0)) (fun a b => a mod b))
      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Band =>
      match tyl with
      | Tint w s  =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op Z.land)
      | Tchar w s  =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op Z.land)
      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Bor =>
      match tyl with
      | Tint w s  =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op Z.lor)
      | Tchar w s  =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op Z.lor)
      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Bxor =>
      match tyl with
      | Tint w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op Z.lxor)
      | Tchar w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op Z.lxor)
      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Bshl =>
      match tyl with
      | Tint w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_shift_op ty w s Z.shiftl)
      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Bshr =>
      match tyl with
      | Tint w s =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_shift_op ty w s Z.shiftr)
      | _ => ret (fun _ _ _ => error "not supported")
      end

    (* todo(gmm): relational operators *)
    | Beq =>
      match tyl with
      | Tint _ _
      | Tchar _ _
      | Tbool =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op (fun a b => if Z.eq_dec a b then 1 else 0))
        (* todo(gmm): pointers *)

      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Bneq =>
      match tyl with
      | Tint _ _
      | Tchar _ _
      | Tbool =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op (fun a b => if Z.eq_dec a b then 0 else 1))
        (* todo(gmm): pointers *)

      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Ble =>
      match tyl with
      | Tint _ _
      | Tchar _ _
      | Tbool =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op (fun a b => if ZArith_dec.Z_le_gt_dec a b then 1 else 0))
        (* todo(gmm): pointers *)

      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Blt =>
      match tyl with
      | Tint _ _
      | Tchar _ _
      | Tbool =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op (fun a b => if ZArith_dec.Z_lt_ge_dec a b then 1 else 0))
        (* todo(gmm): pointers *)

      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Bge =>
      match tyl with
      | Tint _ _
      | Tchar _ _
      | Tbool =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op (fun a b => if ZArith_dec.Z_ge_lt_dec a b then 1 else 0))
        (* todo(gmm): pointers *)

      | _ => ret (fun _ _ _ => error "not supported")
      end

    | Bgt =>
      match tyl with
      | Tint _ _
      | Tchar _ _
      | Tbool =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyr ty) ;;
        ret (simple_int_int_bin_op (fun a b => if ZArith_dec.Z_gt_le_dec a b then 1 else 0))
        (* todo(gmm): pointers *)

      | _ => ret (fun _ _ _ => error "not supported")
      end


        (* todo(gmm): support for [<=>] *)
    | _ => ret (fun _ _ _ => error "not supported")
    end%Z.
  Defined.

(*
  Definition wpbo (o : BinOp) (tyl tyr ty : type)
  : option (val -> val -> (val -> mpred) -> mpred) :=
    match tyl, ty with
    | Tint w _, Tint _ _ =>
      match int_arith_ops o w with
      | Some (cond, f) =>
        guard (type_eq_dec tyl tyr) ;;
        guard (type_eq_dec tyl ty) ;;
        ret (fun v1 v2 Q =>
               Exists i1, Exists i2,
                 [| v1 = Vint i1 |] **
                 [| v2 = Vint i2 |] **
                 [| cond i1 i2 |] **
                 [| has_type (Vint (f i1 i2)) ty |] **
                 Q (Vint (f i1 i2)))
      | None =>
        match int_rel_ops o with
        | Some f =>
          guard (type_eq_dec tyl tyr) ;;
          guard (type_eq_dec ty T_int) ;;
          ret (fun v1 v2 Q =>
                 Exists i1, Exists i2,
                   [| v1 = Vint i1 |] **
                   [| v2 = Vint i2 |] **
                   Q (Vint (f i1 i2)))
        | None => ret (fun _ _ _ => error "unrecognized arith op")
        end
      end
    | Tint _ _, Tbool =>
      match int_rel_ops o with
      | Some f =>
        guard (type_eq_dec tyl tyr) ;;
        ret (fun v1 v2 Q =>
               Exists i1, Exists i2,
                 [| v1 = Vint i1 |] **
                 [| v2 = Vint i2 |] **
                 Q (Vint (f i1 i2)))
      | None => ret (fun _ _ _ => error "unrecognized comparison op")
      end
    | Tpointer _, Tbool =>
      match o with
      | Beq =>
        guard (type_eq_dec tyl tyr) ;;
        ret (fun v1 v2 Q =>
               Exists p1, Exists p2,
                 [| v1 = Vptr p1 |] **
                 [| v2 = Vptr p2 |] **
                 Q (Vint (if ptr_eq_dec p1 p2 then 1 else 0)))
      | Bneq =>
        guard (type_eq_dec tyl tyr) ;;
        ret (fun v1 v2 Q =>
               Exists p1, Exists p2,
                 [| v1 = Vptr p1 |] **
                 [| v2 = Vptr p2 |] **
                 Q (Vint (if ptr_eq_dec p1 p2 then 0 else 1)))
      | _ => ret (fun _ _ _ => error "unrecognized pointer comparison op")
      end
    | _, _ => ret (fun _ _ _ => error "unrecognized binop")
    end%Z.
*)

  Local Ltac foo :=
    match goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    | _ : None = Some _ |- _ => discriminate
    end.

  Lemma wpbo_sound : forall o tyl tyr ty v1 v2 Q K,
      wpbo o tyl tyr ty = Some Q ->
      Q v1 v2 K |-- Eval.wp_eval_binop (resolve:=resolve) o tyl tyr ty v1 v2 K.
  Proof.
    destruct o; simpl.
    (* Opaque type_eq_dec. *)
    (* destruct tyl, ty; cbn. *)
    (* all: intros. *)
    (* all: cbv [ret] in H. *)
    (* all: try foo. *)
    (* all: try (rewrite error_defn; apply lfalseL). *)
    (* all: repeat match goal with *)
    (*             | H : context[match ?e with | _ => _ end] |- _ => destruct e; cbn in H *)
    (*             end. *)
    (* all: try foo. *)
    (* all: try (rewrite error_defn; apply lfalseL). *)
    (* all: repeat (destruct type_eq_dec; subst). *)
    (* all: cbn in *. *)
    (* all: try foo. *)
    (* all: rewrite Eval.wp_eval_binop_defn. *)
    (* all: vc.work. *)
    (* all: subst. *)
    (* all: apply embedPropR. *)
    (* all: try match goal with *)
    (*          | H : Tint _ _ = Tint _ _ |- _ => inversion H; clear H; subst *)
    (*          end. *)
    (* all: admit. *)
  Admitted.

  Definition wpAnys' (wpe' : ValCat -> Expr -> option ((val -> FreeTemps -> mpred) -> mpred)) (ve : ValCat * Expr)
    : option ((val -> FreeTemps -> mpred) -> FreeTemps -> mpred) :=
       Qe <- wpe' (fst ve) (snd ve) ;;
       ret (fun Q free => Qe (fun v f => Q v (f ** free))).

  Definition get_spec (f : obj_name) : option function_spec :=
    match find (fun '(f', _) => if string_dec f f' then true else false) specs with
    | None => None
    | Some (_, x) => Some x
    end.

  (* todo(gmm): convert `FreeTemps` into `option mpred` and eliminate redundant
   * `empSP`.
   * todo(gmm): should we semi-reflect `mpred`?
   *)
  Fixpoint wpe (cat : ValCat) (e : Expr) {struct e}
  : option (forall (Q : val -> FreeTemps -> mpred), mpred) :=
    let default :=
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
             | Some false => error "is_const_int ty n = Some false"
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
      Qo <- wpbo o tl tr ty ;;
      ret (fun Q => Ql (fun v1 free1 => Qr (fun v2 free2 =>
            Qo v1 v2 (fun v' => Q v' (free1 ** free2)))))
    | Eunop o e ty =>
      rvalue cat ;;
      Qe <- wpe Rvalue e ;;
      let te := drop_qualifiers (Typing.type_of e) in
      let ty := drop_qualifiers ty in
      Qo <- wpuo o te ty ;;
      ret (fun Q => Qe (fun v free =>
            Qo v (fun v' => Q v' free)))
    | Ecast c (vc, e) ty =>
      let ty := drop_qualifiers ty in
      match c with
      | Cl2r =>
        lvalue vc ;;
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
        rvalue vc ;;
        rvalue cat ;;
        wpe Rvalue e
      | Cintegral =>
        rvalue vc ;;
        rvalue cat ;;
        Qe <- wpe Rvalue e ;;
        ret (fun Q => Qe (fun v free => [| has_type v ty |] ** Q v free))
      | Cnull2ptr =>
        rvalue vc ;;
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
    | Eassign_op o lhs rhs ty =>
      lvalue cat ;;
      let tyl := drop_qualifiers (type_of lhs) in
      let tyr := drop_qualifiers (type_of rhs) in
      let ty := drop_qualifiers ty in
      Qr <- wpe Rvalue rhs ;;
      Qo <- wpbo o tyl tyr ty ;;
      match lhs with
      | Evar (Lname x) ty' =>
        let ty' := drop_qualifiers ty' in
        (* note(gmm): this is a common case that has a simpler rule. *)
        ret (fun Q => Qr (fun rv free => Exists la, Exists lv,
                tlocal_at r x la (tprim ty' lv) **
                Qo lv rv (fun v' =>
                  (tlocal_at r x la (tprim ty' v') -* Q la free))))
      | _ =>
        Ql <- wpe Lvalue lhs ;;
        ret (fun Q => Ql (fun la free1 =>  Qr (fun rv free2 => Exists lv,
                _at (_eq la) (tprim ty lv) **
                Qo lv rv (fun v' =>
                            (_at (_eq la) (tprim ty v') -* Q la (free1 ** free2))))))
      end
    | Epostinc e' ty
    | Epostdec e' ty =>
      rvalue cat ;;
      let ty := drop_qualifiers ty in
      let tye := drop_qualifiers (type_of e) in
      let op := match e with
                | Epostinc _ _ => Badd
                | _            => Bsub
                end in
      Qo <- wpbo op tye tye ty ;;
      match e' with
      | Evar (Lname x) _ =>
        ret (fun Q => Exists la, Exists v,
                tlocal_at r x la (tprim ty v) **
                Qo v (Vint 1) (fun v' =>
                  (tlocal_at r x la (tprim ty v') -* Q v empSP)))
      | _ =>
        Qe <- wpe Lvalue e' ;;
        ret (fun Q => Qe (fun a free => Exists v,
              _at (_eq a) (tprim ty v) **
              Qo v (Vint 1) (fun v' =>
                (_at (_eq a) (tprim ty v') -* Q v free))))
      end
    | Epreinc e' ty
    | Epredec e' ty =>
      lvalue cat ;;
      let ty := drop_qualifiers ty in
      let tye := drop_qualifiers (type_of e) in
      let op := match e with
                | Epostinc _ _ => Badd
                | _            => Bsub
                end in
      Qo <- wpbo op tye tye ty ;;
      match e' with
      | Evar (Lname x) _ =>
        ret (fun Q => Exists la, Exists v,
                tlocal_at r x la (tprim ty v) **
                Qo v (Vint 1) (fun v' =>
                  (tlocal_at r x la (tprim ty v') -* Q la empSP)))
      | _ =>
        Qe <- wpe Lvalue e' ;;
        ret (fun Q => Qe (fun a free => Exists v,
              _at (_eq a) (tprim ty v) **
              Qo v (Vint 1) (fun v' =>
                (_at (_eq a) (tprim ty v') -* Q a free))))
      end
    | Enull => ret (fun Q => Q (Vptr nullptr) empSP)
    | Ecall (Ecast Cfunction2pointer (vc, Evar (Gname f) _) _) es _ =>
      match vc with
      | Lvalue | Rvalue =>
        rvalue cat ;;
        Qes <- wpes (wpAnys' wpe) es ;;
        match get_spec f with
        | Some fs =>
          ret (fun Q =>
                 Qes (fun vs free =>
                   applyEach (fs_arguments fs) vs (fs_spec fs ti) (fun Qf _ =>
                     Qf (fun r => Q r free))) empSP)
        | None => default
        end
      | _ => default
      end
    | Emember_call false gn obj es ty =>
      rvalue cat ;;
      Qo <- wpe Lvalue obj ;;
      Qes <- wpes (wpAnys' wpe) es ;;
      match get_spec gn with
      | Some fs =>
        ret (fun Q =>
               Qo (fun this => Qes (fun vs free =>
                 applyEach (fs_arguments fs) (this :: vs) (fs_spec fs ti) (fun Qf _ =>
                   Qf (fun r => Q r free)))))
      | None => default
      end
    | Eatomic ao es ty =>
      rvalue cat ;;
      Qes <- wpes (wpAnys' wpe) es ;;
      ret (fun Q => Qes (fun vs free => wp_atom (resolve:=resolve) ao vs ty (fun v => Q v free)) empSP)
    | Eif test thn els ty =>
      Qr <- wpe Rvalue test ;;
      Qthn <- wpe cat thn ;;
      Qels <- wpe cat els ;;
      ret (fun Q => Qr (fun v free =>
             (     ([| is_true v = true |]  -* Qthn (fun v' free' => Q v' (free ** free')))
              //\\ ([| is_true v = false |] -* Qels (fun v' free' => Q v' (free ** free'))))))
    | _ => default
    end.

  Theorem wpe_sound : forall e vc K Q,
      wpe vc e = Some Q ->
      sig (resolve:=resolve) ti specs ** Q K |-- @Wp.wpe resolve ti r vc e K.
  Proof.
    (* induction e; *)
    (*   cbn; *)
    (*   destruct vc; *)
    (*   cbv [ret]; *)
    (*   intros; *)
    (*   try solve [ foo; cbn; reflexivity ]. *)
    (* all: try match goal with *)
    (*          | H : context[match ?e with | _ => _ end] |- _ => *)
    (*            destruct e; cbn in H *)
    (*          end. *)
    (* all: try foo; cbn. *)
    (* all: try vc.simplifying. *)
    (* all: try reflexivity. *)
    (* all: cbn in *. *)
    (* all: try foo; cbn. *)
    (* all: try match goal with *)
    (*          | H : context[match ?e with | _ => _ end] |- _ => *)
    (*            destruct e; cbn in H *)
    (*          end. *)
  Admitted.

  Corollary wp_lhs_sound : forall e K Q,
      wpe Lvalue e = Some Q ->
      sig (resolve:=resolve) ti specs ** Q K |-- @Wp.wp_lhs resolve ti r e K.
  Proof.
    intros.
    pose proof (wpe_sound e Lvalue).
    rewrite H0;
      cbn;
      trivial.
  Qed.

  Corollary wp_rhs_sound : forall e K Q,
      wpe Rvalue e = Some Q ->
      sig (resolve:=resolve) ti specs ** Q K |-- @Wp.wp_rhs resolve ti r e K.
  Proof.
    intros.
    pose proof (wpe_sound e Rvalue).
    rewrite H0;
      cbn;
      trivial.
  Qed.

  Definition wpAnys (ve : ValCat * Expr)
  : option ((val -> FreeTemps -> mpred) -> FreeTemps -> mpred) :=
    Qe <- wpe (fst ve) (snd ve) ;;
    ret (fun Q free => Qe (fun v f => Q v (f ** free))).

  (* mostly copied from Cpp.Sem.Func *)
  Fixpoint wpi_init (ty : type) (init : option Expr)
  : option (val -> mpred -> mpred) :=
    match ty with
    | Trv_reference _ => ret (fun _ _ => lfalse)
    | Treference t =>
      match init with
      | None => ret (fun _ _ => error "references must be initialized")
      | Some init => ret (fun _ _ => error "refernce fields are not supported")
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
        ret (fun loc Q => Q)
      | Some init =>
        Qi <- wpe Rvalue init ;;
        ret (fun loc Q => Qi (fun v free =>
               _at (_eq loc) (uninit ty)
            ** (_at (_eq loc) (tprim ty v) -*
                    (free ** Q))))
      end
    | Tarray _ _ => lfalse (* todo(gmm): arrays not yet supported *)
    | Tref gn =>
      match init with
      | Some (Econstructor cnd es _) =>
        Qes <- wpes wpAnys es ;;
        ctor_spec <- get_spec cnd ;;
        ret (fun loc Q =>
             Qes (fun vs free =>
                  applyEach _ (loc :: vs) (ctor_spec.(fs_spec) ti) (fun Q' _ =>
                    Q' (fun _ => free ** Q))) empSP)
      | _ => ret (fun _ _ =>
                   error "all non-primitive declarations must have initializers")
      end
    | Tqualified _ ty => wpi_init ty init
    end.

  Definition wpi (cls : globname) (f : FieldOrBase) (i : Expr)
  : option (val -> mpred -> mpred) :=
    Qe <- wpi_init (type_of i) (Some i) ;; (* `type_of i` isn't correct *)
    let p := offset_for cls f in
    ret (fun this Q => Exists fl,
                    (_offsetL p (_eq this) &~ fl ** ltrue) //\\
                    Qe fl Q).

  Theorem wpi_sound : forall cls fi Q this K,
      wpi cls (fst fi) (snd fi) = Some Q ->
      sig (resolve:=resolve) ti specs ** Q this K
      |-- IN.wpi (resolve:=resolve) ti r cls this fi K.
  Proof. Admitted.

  Fixpoint wpis (cls : globname) (f : list (FieldOrBase * Expr))
  : option (val -> mpred -> mpred) :=
    match f with
    | nil => ret (fun _ Q => Q)
    | (f,i) :: is =>
      Qi <- wpi cls f i ;;
      Qis <- wpis cls is ;;
      ret (fun this Q => Qi this (Qis this Q))
    end.

  Theorem wpis_sound : forall cls is Q this K,
      wpis cls is = Some Q ->
      sig (resolve:=resolve) ti specs ** Q this K
      |-- IN.wpis (resolve:=resolve) ti r cls this is K.
  Proof. Admitted.

  Definition wpd (cls : globname) (f : FieldOrBase) (dtor : obj_name)
  : option (val -> mpred -> mpred) :=
    let default := ret (fun this Q => wpd (resolve:=resolve) ti r cls this (f, dtor) Q) in
    let p := offset_for cls f in
    match get_spec dtor with
    | Some fs =>
      match fs.(fs_arguments) as X
            return (thread_info -> arrowFrom val X ((val -> mpred) -> mpred)) -> _
      with
      | _ :: nil => fun spec => ret (fun this Q => spec ti this (fun _ => Q))
      | _ => fun _ => default
      end fs.(fs_spec)
    | None => default
    end.

  Theorem wpd_sound : forall cls fi Q this K,
      wpd cls (fst fi) (snd fi) = Some Q ->
      sig (resolve:=resolve) ti specs ** Q this K |-- D.wpd (resolve:=resolve) ti r cls this fi K.
  Proof. Admitted.

  Fixpoint wpds (cls : globname) (f : list (FieldOrBase * obj_name))
  : option (val -> mpred -> mpred) :=
    match f with
    | nil => ret (fun _ Q => Q)
    | (f,i) :: is =>
      Qi <- wpd cls f i ;;
      Qis <- wpds cls is ;;
      ret (fun this Q => Qi this (Qis this Q))
    end.

  Theorem wpds_sound : forall cls is Q this K,
      wpds cls is = Some Q ->
      sig (resolve:=resolve) ti specs ** Q this K
      |-- D.wpds (resolve:=resolve) ti r cls this is K.
  Proof. Admitted.


  Section block.
    Variable wp : forall (s : Stmt), option (Kpreds -> mpred).

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
      | Tarray _ _ => ret (fun _ _ => error "arrays unsupported") (* todo(gmm): arrays not yet supported *)
      | Tref gn =>
        match init with
        | Some (Econstructor cnd es _) =>
          Qes <- wpes wpAnys es ;;
          ctor_spec <- get_spec cnd ;;
          dtor_spec <- get_spec (dtor_name Dt_Deleting gn) ;;
          ret (fun k Q =>
                 Qes (fun vs free =>
                   Forall a,
                     _at (_eq a) (uninit (Tref gn)) -*
                     applyEach _ (a :: vs) (ctor_spec.(fs_spec) ti) (fun Q' _ =>
                       Q' (fun _ =>
                         _local r x &~ a -*
                         (free ** k (Kat_exit (fun Q'' =>
                           _local r x &~ a **
                           applyEach _ (a :: nil) (dtor_spec.(fs_spec) ti) (fun Q _ => Q (fun _ => Q''))) Q))))) empSP)
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
               (([| is_true v = true |] -* Wthn k) //\\
                ([| is_true v = false |] -* Wels k)))) K)
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
      sig (resolve:=resolve) ti specs ** Q K |-- @Wp.wp resolve ti r s K.
  Proof. Admitted.

  Definition wp_ctor (cls : globname)
             (inits : list (FieldOrBase * Expr)) (body : Stmt)
  : option (val -> Kpreds -> mpred) :=
    Qi <- wpis cls inits ;;
    Qbody <- wp body ;;
    ret (fun this Q => Qi this (Qbody Q)).

  Theorem wp_ctor_sound : forall cls is b K Q this,
      wp_ctor cls is b = Some Q ->
      sig (resolve:=resolve) ti specs ** Q this K |-- F.wp_ctor (resolve:=resolve) cls ti r this is b K.
  Proof. Admitted.

  Definition wp_dtor (cls : globname)
             (body : Stmt) (ds : list (FieldOrBase * obj_name))
  : option (val -> mpred -> mpred -> mpred) :=
    Qbody <- wp body ;;
    Qd <- wpds cls ds ;;
    ret (fun this frees Q => Qbody (Kfree frees (void_return (Qd this Q)))).

  Theorem wp_dtor_sound : forall cls is b K Q this free,
      wp_dtor cls b is = Some Q ->
      sig (resolve:=resolve) ti specs ** Q this free K |-- F.wp_dtor (resolve:=resolve) cls ti r this b is free K.
  Proof. Admitted.

End refl.

Definition cu_app (a b : compilation_unit) : compilation_unit :=
  {| symbols := a.(symbols) ++ b.(symbols) ; globals := a.(globals) ++ b.(globals) |}.

Ltac with_specs' c specs md k :=
  match c with
  | ?l ** ?r =>
    with_specs' l specs md ltac:(fun specs' md' => with_specs' r specs' md' k)
  | @sig _ _ ?spec => k constr:(List.app spec specs) md
  | ti_cglob ?f ?spec => k constr:((f, spec) :: specs) md
  | |> ti_cglob ?f ?spec => k constr:((f, spec) :: specs) md
  | cglob ?f _ ?spec => k constr:((f, spec) :: specs) md
  | |> cglob ?f _ ?spec => k constr:((f, spec) :: specs) md
  | denoteModule ?m => k specs constr:(cu_app md m)
  | _ => k specs
  end.

Ltac with_specs_and_mod k :=
  match goal with
  | |- ?l |-- _ => with_specs' l constr:(@nil (globname * function_spec))
                                constr:({| symbols := nil ; globals := nil |}) k
  end.

Ltac simplifying :=
  progress (with_specs_and_mod ltac:(fun s md =>
     first [ rewrite <- wp_sound with (cu:=md) (specs:=s) by (simpl; reflexivity)
           | rewrite <- wp_ctor_sound with (cu:=md) (specs:=s) by (simpl; reflexivity)
           | rewrite <- wp_dtor_sound with (cu:=md) (specs:=s) by (simpl; reflexivity)
           | rewrite <- wp_lhs_sound with (cu:=md) (specs:=s) by (simpl; reflexivity)
           | rewrite <- wp_rhs_sound with (cu:=md) (specs:=s) by (simpl; reflexivity)
           ]); cbn).
