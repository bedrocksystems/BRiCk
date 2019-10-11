From iris Require Import bi.notation.
From iris Require Import bi.bi.

Global Notation lentails := (bi_entails) (only parsing).
Global Notation lequiv := (≡) (only parsing).
Global Notation ltrue := (bi_pure True) (only parsing).
Global Notation lfalse := (bi_pure False) (only parsing).
Global Notation land := (bi_and) (only parsing).
Global Notation lor := (bi_or) (only parsing).
Global Notation limpl := (bi_impl) (only parsing).
Global Notation lforall := (bi_forall) (only parsing).
Global Notation lexists := (bi_exist) (only parsing).

Global Notation empSP := (bi_emp) (only parsing).
Global Notation sepSP := (bi_sep) (only parsing).
Global Notation wandSP := (bi_wand) (only parsing).
Global Notation illater := (sbi_later) (only parsing).

Global Notation embed := (bi_pure) (only parsing).
Ltac split' := intros; apply (anti_symm (⊢)).

Global Notation only_provable P := (<affine>(embed P%type))%I (only parsing).

(* Charge notation levels *)
Module ChargeNotation.

  Infix "|--"  := (⊢)%I (at level 80, no associativity).
  Notation "P //\\ Q"   := (P ∧ Q)%I (at level 75, right associativity).
  Notation "P \\// Q"   := (P ∨ Q)%I (at level 76, right associativity).
  Notation "P -->> Q"   := (P → Q)%I (at level 77, right associativity).
  Notation "'Forall' x .. y , p" :=
    (lforall (fun x => .. (lforall (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).

  Notation "'Exists' x .. y , p" :=
    (lexists (fun x => .. (lexists (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).

  Notation "|--  P" := (bi_pure True |-- P) (at level 85, no associativity).

  Notation "P ** Q" := (P ∗ Q)%I (at level 58, right associativity).
  Notation "P -* Q" := (P -∗ Q)%I (at level 60, right associativity).
  Notation "'sepSPs' ps" := ([∗] ps)%I (at level 20).

  (* Notation "'|>' P" := (▷  P)%I (at level 71). *)
  Notation "|> P" := (▷  P)%I (at level 20, right associativity).

  Infix "-|-"  := (≡)%I (at level 85, no associativity).
  Notation "'[|'  P  '|]'" := (only_provable P).

End ChargeNotation.

(* IPM notation levels *)
Module IPMNotation.
  Notation "P |-- Q" := (P ⊢ Q)%I (at level 99, Q at level 200, right associativity).
  Notation "P //\\ Q" := (P ∧ Q)%I (at level 99, Q at level 80, right associativity).
  Notation "P \\// Q" := (P ∨ Q)%I (at level 99, Q at level 85, right associativity).
  Notation "P -->> Q" := (P → Q)%I (at level 99, Q at level 200, right associativity).

  Notation "'Forall' x .. y , p" :=
    (lforall (fun x => .. (lforall (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).
  Notation "'Exists' x .. y , p" :=
    (lexists (fun x => .. (lexists (fun y => p)) ..))%I (at level 78, x binder, y binder, right associativity).

  Infix "-|-"  := (⊣⊢)%I (at level 95, no associativity).
  Notation "|--  P" := (True |-- P)%I (at level 85, no associativity).

  Notation "P ** Q" := (P ∗ Q)%I (at level 80, right associativity).
  Notation "P -* Q" := (P -∗ Q)%I (at level 99, Q at level 200, right associativity,
                                   format "'[' P  '/' -*  Q ']'").
  Notation "[| P |]" := (⌜ P ⌝%I) (at level 1, P at level 200).
  Notation "[|| P ||]" := (⎡ P ⎤%I) (at level 1, P at level 200).
  Notation "'sepSPs' ps" := ([∗] ps)%I (at level 20).

  Notation "|> P" := (▷  P)%I (at level 20, right associativity).
End IPMNotation.
