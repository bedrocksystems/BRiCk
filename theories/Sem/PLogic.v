(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

From Cpp Require Import Ast.

From Cpp.Sem Require Import Logic Semantics.

(* todo(gmm): these can be moved somewhere more generic *)
Class Affine (P : mpred) : Prop :=
{ can_dup : P |-- P ** P }.
Class Droppable (P : mpred) : Prop :=
{ can_drop : P |-- empSP }.


(* representations are predicates over a location, they should be used to
 * assert propreties of the heap
 *)
Definition Rep : Type := forall addr : val, mpred.
(* locations are predicates over a location and are used to do address
 * arithmetic.
 * - note(gmm): they are always computable from the program except for when
 *   they use field and the layout of a class is non-standard or when they
 *   mention local variables.
 *)
Record Loc : Type :=
{ addr_of : forall addr : val, mpred }.

Definition LocEq (l1 l2 : Loc) : Prop :=
  forall x y, l1.(addr_of) x //\\ l2.(addr_of) y |-- [| x = y |].

Definition _eq (a : val) : Loc :=
{| addr_of p := [| p = a |] |}.
Theorem _eq_LocEq : forall a b, LocEq (_eq a) (_eq b) -> a = b.
Proof. unfold LocEq, _eq. intros.
       simpl in *.
       specialize (H a b).
       admit.
Admitted.

Definition _local (r : region) (x : ident) : Loc.
Admitted.
Axiom _local_det : forall r x, LocEq (_local r x) (_local r x).

Definition _field (f : field) (base : Loc) : Loc.
Admitted.
Axiom Proper__field : forall {f}, Proper (LocEq ==> LocEq) (_field f).

Definition _sub (t : type) (i : Z) (base : Loc) : Loc.
Admitted.
Axiom Proper__sub : forall t i, Proper (LocEq ==> LocEq) (_sub t i).

(* this represents static_cast *)
Definition _super (from to : type) (base : Loc) : Loc.
Admitted.
Axiom Proper__super : forall from to, Proper (LocEq ==> LocEq) (_super from to).




(*
(** pointer offsets *)
Definition field_addr (f : field) (base : val) : Loc := fun ptr =>
  with_genv (fun g => Exists off : Z,
      [| offset_of (c:=g) (Tref f.(f_type)) f.(f_name) off |] **
      [| offset_ptr base off = ptr |]).

(* todo(gmm): i need a way to compute a parent class offset. *)
Parameter parent_addr : forall (parent derived : globname) (base : val), Loc.

(* address of a local variable *)
Parameter local_addr : region -> ident -> Loc.
*)

(* heap points to *)
(* note(gmm): this needs to support fractional permissions and other features *)
Parameter ptsto : val -> Rep.



(* the pointer contains the code *)
Parameter code_at : Func -> ptr -> mpred.
(* code_at is freely duplicable *)
Axiom code_at_dup : forall p f, code_at p f -|- code_at p f ** code_at p f.
Axiom code_at_drop : forall p f, code_at p f |-- empSP.

Parameter ctor_at : ptr -> Ctor -> mpred.
Parameter dtor_at : ptr -> Dtor -> mpred.


Parameter is_true : val -> bool.
Axiom is_true_int : forall i,
    is_true (Vint i) = negb (BinIntDef.Z.eqb i 0).

(* there shouldn't be locals because locals need a spatial ownership (over
 * the region)
 * global addresses admit duplication and weakening
 *)
Inductive path : Type :=
| p_done
| p_dot  (_ : field) (_ : path) (* field offset *)
| p_cast (from to : type)  (_ : path) (* parent-class offset, i.e. static_cast *)
| p_sub  (_ : type) (_ : val) (_ : path).

Fixpoint pathD (p : path) (l : Loc) : Loc :=
  match p with
  | p_done => l
  | p_dot f p => pathD p (_field f l)
  | p_cast from to p => pathD p (_super (drop_qualifiers from) (drop_qualifiers to) l)
  | p_sub t v p =>
    {| addr_of a := Exists i : Z,
         [| Vint i = v |] //\\
         (pathD p (_sub (drop_qualifiers t) i l)).(addr_of) a |}
  end.

Require Import Cpp.Auto.Discharge.

Lemma pathD_det : forall p l1 l2,
    LocEq l1 l2  -> LocEq (pathD p l1) (pathD p l2).
Proof.
  induction p; simpl; intros; eauto.
  { eapply IHp. eapply Proper__field; eauto. }
  { eapply IHp. eapply Proper__super. eauto. }
  { red. simpl. intros.
    rewrite landexistsDL1; eapply lexistsL; intro.
    rewrite landexistsDL2; eapply lexistsL; intro.
    unfold only_provable.
    admit. }
Admitted.


Definition _addr (base : val) (p : path) : Loc :=
  pathD p (_eq base).

Notation "a @@ b" := (a.(addr_of) b) (at level 30, no associativity).

Theorem _addr_det : forall p b a1 a2,
    _addr b p @@ a1 ** _addr b p @@ a2 |-- _addr b p @@ a1 ** [| a1 = a2 |].
Proof. Admitted.


(*
Parameter Affine__addr : forall b p a, Affine (_addr b p a).
Parameter Droppable__addr : forall b p a, Droppable (_addr b p a).
*)

Definition _atP (base : val) (p : path) (P : Rep) : mpred :=
  Exists addr, (_addr base p) @@ addr ** P addr.


Definition _at (base : Loc) (P : Rep) : mpred :=
  Exists addr, base @@ addr ** P addr.

(* this should probably be split up into a bunch of simpler definitions, e.g.
 * - `tint (size : nat) : N -> Rep`
 * - `tuint (size : nat) : N -> Rep`
 * - ...etc...
 *)
Definition tprim (ty : type) (v : val) : Rep :=
  fun addr => ptsto addr v ** [| has_type v (drop_qualifiers ty) |].

Definition uninit (ty : type) : Rep := fun addr =>
  Exists bits,
    (* with_genv (fun env => [| size_of env ty size |]) ** *)
    tprim ty bits addr.

Definition tany (t : type) : Rep := fun addr =>
  Exists v, [| has_type v t |] ** tprim t v addr.

(* this isn't really necessary, we should simply drop it and write
 * predicates in this way to start with
 *)
Definition tinv {model} (Inv : val -> model -> mpred) (m : model) : Rep :=
  fun addr => Inv addr m.

Lemma val_uninit : forall t v, tprim t v |-- uninit t.
Proof. Admitted.

Lemma val_any : forall t v, tprim t v |-- tany t.
Proof. Admitted.

Definition _at_cancel : forall a (V V' : Rep) P Q,
    V |-- V' ->
    P |-- Q ->
    _at a V ** P |-- _at a V' ** Q.
Proof. Admitted.

Definition tlocal_at (r : region) (ty : type) (l : ident) (a : val) (v : val) : mpred :=
  _local r l @@ a **
  [| has_type a (Tpointer ty) |] **
  _at (_eq a) (tprim ty v).

Definition tlocal (r : region) (ty : type) (x : ident) (v : val) : mpred :=
  Exists a, tlocal_at r ty x a v.

Lemma tlocal_at_tlocal : forall r ty x a v F F',
    F |-- F' ->
    tlocal_at r ty x a v ** F |-- tlocal r ty x v ** F'.
Proof.
  clear. unfold tlocal, tlocal_at.
  intros.
  rewrite H.
  Discharge.discharge fail eauto.
Qed.

Fixpoint uninitializedN (size : nat) (a : val) : mpred :=
  match size with
  | 0 => empSP
  | S size => (Exists x, ptsto a x) ** uninitializedN size (offset_ptr a 1)
  end.
Definition uninitialized (size : N) : val -> mpred :=
  uninitializedN (BinNatDef.N.to_nat size).

Definition uninitialized_ty (tn : type) (p : val) : mpred :=
  Exists sz, with_genv (fun g => [| @size_of g tn sz |]) **
                       uninitialized sz p.


(* p is a path
 * P is a predicate over the resulting value
 *)
Definition data (P : val -> mpred) (p : val -> mpred) : mpred.
refine (Exists v, p v //\\ P v).
Defined.

Require Import Coq.Lists.List.

Definition tptsto t a v :=
  _at a (tprim (drop_qualifiers t) v).

Definition tat_field (t : type) (base : val) (f : field) (v : val) : mpred :=
  _atP base (p_dot f p_done) (tprim t v).



Lemma tat_uninitialized
  : forall t b f v F F',
    F |-- F' ->
    tat_field t b f v ** F |-- _atP b (p_dot f p_done) (uninit t).
Proof. Admitted.
