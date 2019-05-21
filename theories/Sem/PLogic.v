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

Local Open Scope string_scope.

(* todo(gmm): these can be moved somewhere more generic *)
Class Affine {L : Type} {LL : ILogicOps L} {LS : BILogicOps L} (P : L) : Prop :=
{ can_dup : P |-- P ** P }.
Class Droppable {L : Type} {LL : ILogicOps L} {LS : BILogicOps L} (P : L) : Prop :=
{ can_drop : P |-- empSP }.

(* representations are predicates over a location, they should be used to
 * assert propreties of the heap
 *)
(* todo(gmm): `addr : val` -> `addr : ptr` *)
Record Rep : Type :=
  { repr : forall addr : val, mpred }.

Global Instance ILogicOps_Rep : ILogicOps Rep :=
{ lentails P Q := forall a, P.(repr) a |-- Q.(repr) a
; ltrue := {| repr _ := ltrue |}
; lfalse := {| repr _ := lfalse |}
; land  P Q := {| repr a := land (P.(repr) a) (Q.(repr) a) |}
; lor   P Q := {| repr a := lor (P.(repr) a) (Q.(repr) a) |}
; limpl P Q := {| repr a := limpl (P.(repr) a) (Q.(repr) a) |}
; lforall T P := {| repr a := lforall (fun v : T => (P v).(repr) a) |}
; lexists T P := {| repr a := lexists (fun v : T => (P v).(repr) a) |}
}.
Global Instance ILogic_Rep : ILogic Rep.
Admitted.
Global Instance BILogicOps_Rep : BILogicOps Rep :=
{ empSP := {| repr _ := empSP |}
; sepSP P Q := {| repr a := sepSP (P.(repr) a) (Q.(repr) a) |}
; wandSP P Q := {| repr a := wandSP (P.(repr) a) (Q.(repr) a) |}
}.
Global Instance BILogic_Rep : BILogic Rep.
Admitted.


(* locations are predicates over a location and are used to do address
 * arithmetic.
 * - note(gmm): they are always computable from the program except for when
 *   they use field and the layout of a non-standard class or when they
 *   mention local variables.
 *)
Record Loc : Type :=
  { addr_of : forall addr : val, mpred }.
Global Instance ILogicOps_Loc : ILogicOps Loc :=
{ lentails P Q := forall a, P.(addr_of) a |-- Q.(addr_of) a
; ltrue := {| addr_of _ := ltrue |}
; lfalse := {| addr_of _ := lfalse |}
; land  P Q := {| addr_of a := land (P.(addr_of) a) (Q.(addr_of) a) |}
; lor   P Q := {| addr_of a := lor (P.(addr_of) a) (Q.(addr_of) a) |}
; limpl P Q := {| addr_of a := limpl (P.(addr_of) a) (Q.(addr_of) a) |}
; lforall T P := {| addr_of a := lforall (fun v : T => (P v).(addr_of) a) |}
; lexists T P := {| addr_of a := lexists (fun v : T => (P v).(addr_of) a) |}
}.
Global Instance ILogic_Loc : ILogic Loc.
Admitted.
Global Instance BILogicOps_Loc : BILogicOps Loc :=
{ empSP := {| addr_of _ := empSP |}
; sepSP P Q := {| addr_of a := sepSP (P.(addr_of) a) (Q.(addr_of) a) |}
; wandSP P Q := {| addr_of a := wandSP (P.(addr_of) a) (Q.(addr_of) a) |}
}.
Global Instance BILogic_Loc : BILogic Loc.
Admitted.



Record Offset : Type :=
  { offset : forall base new : val, mpred }.

Global Instance ILogicOps_Offset : ILogicOps Offset :=
{ lentails P Q := forall a b, P.(offset) a b |-- Q.(offset) a b
; ltrue := {| offset _ := ltrue |}
; lfalse := {| offset _ := lfalse |}
; land  P Q := {| offset a := land (P.(offset) a) (Q.(offset) a) |}
; lor   P Q := {| offset a := lor (P.(offset) a) (Q.(offset) a) |}
; limpl P Q := {| offset a := limpl (P.(offset) a) (Q.(offset) a) |}
; lforall T P := {| offset a := lforall (fun v : T => (P v).(offset) a) |}
; lexists T P := {| offset a := lexists (fun v : T => (P v).(offset) a) |}
}.
Global Instance ILogic_Offset : ILogic Offset.
Admitted.
Global Instance BILogicOps_Offset : BILogicOps Offset :=
{ empSP := {| offset _ _ := empSP |}
; sepSP P Q := {| offset a b := sepSP (P.(offset) a b) (Q.(offset) a b) |}
; wandSP P Q := {| offset a b := wandSP (P.(offset) a b) (Q.(offset) a b) |}
}.
Global Instance BILogic_Offset : BILogic Offset.
Admitted.




Definition LocEq (l1 l2 : Loc) : Prop :=
  forall x y, l1.(addr_of) x //\\ l2.(addr_of) y |-- [| x = y |].

Class Dup_Loc (l : Loc) : Prop :=
  { can_dupL : l |-- l ** l }.

(* absolute locations *)
Definition _eq (a : val) : Loc :=
  {| addr_of p := [| p = a |] |}.

(* note(gmm): this is *not* duplicable *)
Definition _local (r : region) (x : ident) : Loc.
Admitted.
Axiom _local_det : forall r x, LocEq (_local r x) (_local r x).

Definition _this (r : region) : Loc :=
  _local r "#this".


Definition _global (x : globname) : Loc.
Admitted.

(* offsets *)
Definition _field (f : field) : Offset.
Admitted.

Definition _sub (t : type) (i : Z) : Offset.
Admitted.

(* this represents static_cast *)
Definition _super (from to : type) : Offset.
Admitted.

Definition _id : Offset :=
  {| offset a b := embed (a = b) |}.
Definition _dot (o1 o2 : Offset) : Offset :=
  {| offset a c := Exists b, o1.(offset) a b ** o2.(offset) b c |}.

Definition _offsetL (o : Offset) (l : Loc) : Loc :=
  {| addr_of a := Exists a', o.(offset) a' a ** l.(addr_of) a' |}.
Lemma _offsetL_dot : forall o1 o2 l,
    _offsetL o2 (_offsetL o1 l) -|- _offsetL (_dot o1 o2) l.
Proof.
  unfold _offsetL, _dot; simpl.
  constructor; simpl; intros; Discharge.discharge fail fail idtac.
Qed.

Definition _offsetR (o : Offset) (r : Rep) : Rep :=
  {| repr a := Exists a', o.(offset) a a' ** r.(repr) a' |}.
Lemma _offsetR_dot : forall o1 o2 l,
    _offsetR o1 (_offsetR o2 l) -|- _offsetR (_dot o1 o2) l.
Proof.
  unfold _offsetL, _dot; simpl.
  constructor; simpl; intros; Discharge.discharge fail fail idtac.
Qed.




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
Parameter ptsto : forall addr value : val, mpred.



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

Fixpoint pathD (p : path) : Offset :=
  match p with
  | p_done => _id
  | p_dot f p => _dot (_field f) (pathD p)
  | p_cast from to p =>
    _dot (_super (drop_qualifiers from) (drop_qualifiers to)) (pathD p)
  | p_sub t v p =>
    {| offset b a := Exists i : Z,
         [| Vint i = v |] //\\
         (_dot (_sub (drop_qualifiers t) i) (pathD p)).(offset) b a |}
  end.

Require Import Cpp.Auto.Discharge.

(* Lemma pathD_det : forall p l1 l2, *)
(*     LocEq l1 l2  -> LocEq (pathD p l1) (pathD p l2). *)
(* Proof. *)
(*   induction p; simpl; intros; eauto. *)
(*   { eapply IHp. eapply Proper__field; eauto. } *)
(*   { eapply IHp. eapply Proper__super. eauto. } *)
(*   { red. simpl. intros. *)
(*     rewrite landexistsDL1; eapply lexistsL; intro. *)
(*     rewrite landexistsDL2; eapply lexistsL; intro. *)
(*     unfold only_provable. *)
(*     admit. } *)
(* Admitted. *)


(* Definition _addr (base : val) (p : path) : Loc := *)
(*   pathD p (_eq base). *)

Notation "a &~ b" := (a.(addr_of) b) (at level 30, no associativity).

(* Theorem _addr_det : forall p b a1 a2, *)
(*     _addr b p @@ a1 ** _addr b p @@ a2 |-- _addr b p @@ a1 ** [| a1 = a2 |]. *)
(* Proof. Admitted. *)

Class Duplicable_Offset (o : Offset) : Prop :=
  { dup_offset : o |-- o ** o }.
Arguments dup_offset {_ _}.

Global Instance Duplicable_offset o {Do : Duplicable_Offset o} a b : Affine (offset o a b).
Proof.
  constructor. eapply dup_offset.
Qed.


Definition _at (base : Loc) (P : Rep) : mpred :=
  Exists a, base.(addr_of) a ** P.(repr) a.

Definition _atP (base : Loc) (p : Offset) (P : Rep) : mpred :=
  _at (_offsetL p base) P.

Theorem _atP_at : forall b p P,
    _atP b p P -|- _at (_offsetL p b) P.
Proof. reflexivity. Qed.

Arguments can_dup {_ _ _} _ {_}.

Lemma offset_consolidate p a b c :
  offset p a b ** offset p a c |-- offset p a b ** [| b = c |].
Proof. Admitted.

Lemma _atP_sepSP : forall b p P Q,
    Duplicable_Offset p ->
    _atP (_eq b) p (P ** Q) -|- _atP (_eq b) p P ** _atP (_eq b) p Q.
Proof.
  intros; split.
  { unfold _atP, _at, _eq, _offsetL. simpl.
    lift_ex_l fail.
    rewrite (can_dup (offset p x0 x)).
    Discharge.discharge fail fail idtac.
    eapply provable_star; auto.
    eapply only_provable_only; eauto. }
  { unfold _atP, _at, _eq, _offsetL. simpl.
    lift_ex_l fail.
    subst.
    transitivity ((offset p b x1 ** offset p b x) ** repr P x ** repr Q x1).
    - Discharge.discharge fail fail idtac.
    - rewrite offset_consolidate.
      Discharge.discharge fail fail idtac.
      subst.
      Discharge.discharge fail fail idtac.
      eapply only_provable_only; eauto. }
Qed.

Lemma _atP_exists : forall b p T (P : T -> _),
    _atP b p (lexists P) -|- Exists x : T, _atP b p (P x).
Proof.
  unfold _atP, _at; simpl.
  split.
  { Discharge.discharge fail fail idtac. }
  { Discharge.discharge fail fail idtac. }
Qed.

Lemma _atP_offsetR : forall b p o P,
    _atP b p (_offsetR o P) -|- _atP b (_dot p o) P.
Proof.
  unfold _atP, _at, _offsetR; simpl. split.
  { Discharge.discharge fail fail idtac. }
  { Discharge.discharge fail fail idtac. }
Qed.




(* this should probably be split up into a bunch of simpler definitions, e.g.
 * - `tint (size : nat) : N -> Rep`
 * - `tuint (size : nat) : N -> Rep`
 * - ...etc...
 *)
Definition tint (sz : nat) (v : Z) : Rep :=
  {| repr := fun addr =>
               ptsto addr (Vint v) **
               [| has_type (Vint v) (Tint (Some sz) true) |] |}.
Definition tuint (sz : nat) (v : Z) : Rep :=
  {| repr := fun addr =>
               ptsto addr (Vint v) **
               [| has_type (Vint v) (Tint (Some sz) false) |] |}.
Definition tptr (ty : type) (p : ptr) : Rep :=
  {| repr := fun addr => ptsto addr (Vptr p) |}.
Definition tref (ty : type) (p : val) : Rep :=
  {| repr addr := [| addr = p |] |}.


Definition tprim (ty : type) (v : val) : Rep :=
  {| repr := fun addr => ptsto addr v ** [| has_type v (drop_qualifiers ty) |] |}.
Axiom tprim_tint : forall sz v,
    tprim (Tint (Some sz) true) (Vint v) -|- tint sz v.
Axiom tprim_tuint : forall sz v,
    tprim (Tint (Some sz) false) (Vint v) -|- tuint sz v.
Axiom tprim_tptr : forall ty p,
    tprim (Tpointer ty) (Vptr p) -|- tptr (drop_qualifiers ty) p.

Definition uninit (ty : type) : Rep :=
  {| repr := fun addr =>
               Exists bits,
               (* with_genv (fun env => [| size_of env ty size |]) ** *)
               (tprim ty bits).(repr) addr |}.

Definition tany (t : type) : Rep :=
  {| repr := fun addr =>
               Exists v, [| has_type v t |] ** (tprim t v).(repr) addr |}.

(* this isn't really necessary, we should simply drop it and write
 * predicates in this way to start with
 *)
Definition tinv {model} (Inv : val -> model -> mpred) (m : model) : Rep :=
  {| repr := fun addr => Inv addr m |}.

Lemma tint_uninit : forall sz v, tint sz v |-- uninit (Tint (Some sz) true).
Admitted.
Lemma tuint_uninit : forall sz v, tuint sz v |-- uninit (Tint (Some sz) false).
Admitted.
Lemma tptr_uninit : forall ty p, tptr ty p |-- uninit (Tpointer ty).
Admitted.
Lemma tprim_uninit : forall t v, tprim t v |-- uninit t.
Proof. Admitted.

Lemma val_any : forall t v, tprim t v |-- tany t.
Proof. Admitted.

Lemma refine_tprim_ptr : forall p ty v F Q,
    (forall pt, Vptr pt = v ->
           _at p (tptr (drop_qualifiers ty) pt) ** F |-- Q) ->
    _at p (tprim (Tpointer ty) v) ** F |-- Q.
Proof.
  unfold _at, tprim.
  intros; simpl.
Admitted.

Definition _at_cancel : forall a (V V' : Rep) P Q,
    V |-- V' ->
    P |-- Q ->
    _at a V ** P |-- _at a V' ** Q.
Proof. Admitted.

Definition tlocal_at (r : region) (l : ident) (a : val) (v : Rep) : mpred :=
  _local r l &~ a **
  _at (_eq a) v.

Definition tlocal (r : region) (x : ident) (v : Rep) : mpred :=
  Exists a, tlocal_at r x a v.

Lemma tlocal_at_tlocal : forall r x a v F F',
    F |-- F' ->
    tlocal_at r x a v ** F |-- tlocal r x v ** F'.
Proof.
  clear. unfold tlocal, tlocal_at.
  intros.
  rewrite H.
  Discharge.discharge ltac:(fail) fail eauto.
Qed.

Fixpoint uninitializedN (size : nat) (a : val) : mpred :=
  match size with
  | 0 => empSP
  | S size => (Exists x, ptsto a x) ** uninitializedN size (offset_ptr a 1)
  end.
Definition uninitialized (size : N) : Rep :=
  {| repr := uninitializedN (BinNatDef.N.to_nat size) |}.

Definition uninitialized_ty (tn : type) : Rep :=
{| repr := fun p : val =>
  Exists sz, with_genv (fun g => [| @size_of g tn sz |]) **
                       (uninitialized sz).(repr) p |}.

Opaque uninitialized_ty.

(*
(* p is a path
 * P is a predicate over the resulting value
 *)
Definition data (P : val -> mpred) (p : val -> mpred) : mpred.
refine (Exists v, p v //\\ P v).
Defined.
*)

(* Require Import Coq.Lists.List. *)

(* Definition tptsto t a v := *)
(*   _at a (tprim (drop_qualifiers t) v). *)

(* Definition tat_field (t : type) (base : val) (f : field) (v : val) : mpred := *)
(*   _atP base (p_dot f p_done) (tprim t v). *)

(* Lemma tat_uninitialized *)
(*   : forall t b f v F F', *)
(*     F |-- F' -> *)
(*     tat_field t b f v ** F |-- _atP b (p_dot f p_done) (uninit t). *)
(* Proof. Admitted. *)
