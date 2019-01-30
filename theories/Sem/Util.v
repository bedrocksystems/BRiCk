From Coq.Classes Require Import
     RelationClasses Morphisms.

Require Import Coq.Lists.List.
Require Import Coq.Lists.List.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.


Fixpoint arrowFrom {t} u (ls : list t) (T : Type)
: Type :=
  match ls with
  | nil => T
  | cons l ls => u -> arrowFrom u ls T
  end.

Section zip.
  Context {A B C : Type} (f : A -> B -> C).
  Fixpoint zip (x : list A) (y : list B) : list C :=
    match x , y with
    | nil , _
    | _ , nil => nil
    | x :: xs , y :: ys => f x y :: zip xs ys
    end.
End zip.


Section withLogic.
  Context {L : Type}.
  Context {ILogicOps_L : ILogicOps L}.
  Existing Instance ILogicOps_L.

  Fixpoint applyEach {t u T} (ls : list t) (vals : list u)
    : forall (v : arrowFrom u ls T)
        (P : T -> list (t * u) -> L), L :=
    match ls , vals with
    | nil , nil => fun v P => P v nil
    | l :: ls , x :: xs => fun v P =>
      applyEach ls xs (v x) (fun z xs => P z (cons (l, x) xs))
    | _ , _ => fun _ _ => lfalse
    end.

  Fixpoint ForallEach {t u T} (ls : list t)
    : forall (v : arrowFrom u ls T)
        (P : T -> list (t * u) -> L), L :=
    match ls with
    | nil => fun v P => P v nil
    | l :: ls => fun v P => Forall x,
      ForallEach ls (v x) (fun z xs => P z (cons (l, x) xs))
    end.

  Fixpoint Forall2Each {t u T U} (ls : list t)
    : forall (v : arrowFrom u ls T) (v' : arrowFrom u ls U)
        (P : T -> U -> list (t * u) -> L), L :=
    match ls with
    | nil => fun v v' P => P v v' nil
    | l :: ls => fun v v' P => Forall x,
      Forall2Each ls (v x) (v' x) (fun z z' xs => P z z' (cons (l, x) xs))
    end.

  Fixpoint ExistsEach {t u T} (ls : list t)
    : forall (v : arrowFrom u ls T)
        (P : T -> list (t * u) -> L), L :=
    match ls with
    | nil => fun v P => P v nil
    | l :: ls => fun v P => Exists x,
      ExistsEach ls (v x) (fun z xs => P z (cons (l, x) xs))
    end.

End withLogic.

Definition forallEach := @ForallEach Prop _.
Arguments forallEach {_ _ _}.
