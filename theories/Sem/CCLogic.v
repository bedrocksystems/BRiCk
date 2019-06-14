Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From Coq.QArith Require Import QArith Qcanon.
Require Import Coq.QArith.Qfield.
From Coq.micromega Require Import
     QMicromega Psatz.

Require Import Coq.ssr.ssrbool.

From Coq.Classes Require Import
     RelationClasses Morphisms.

From ChargeCore.SepAlg Require Import SepAlg.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Semantics Logic PLogic Wp Expr.
From Cpp.Auto Require Import
     Discharge.

(* semantics of atomic builtins
 * https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
 *)

Module Type cclogic.

  (****** Logical State ********)

  (* the type of (functional) separation algebras
   * note(gmm): this definition differs from the ChargeCore definition
   * because it defines `compose` as a function rather than as a relation.
   *)
  Structure SA :=
  { s_type :> Type;
    s_bot: s_type;
    s_top: s_type;
    s_undef: s_type;
    s_compose: s_type -> s_type -> s_type;
    s_compose_com: forall s1 s2, s_compose s1 s2 = s_compose s2 s1;
    s_compose_assoc: forall s1 s2 s3, s_compose (s_compose s1 s2) s3 = s_compose s1 (s_compose s2 s3);
    s_compose_cancel: forall s1 s1' s2, s_compose s1 s2 <> s_undef ->
                                        s_compose s1 s2 = s_compose s1' s2 -> s1 = s1';
    s_compose_bot: forall s1 s2, s_compose s1 s2 = s_bot -> s1 = s_bot /\ s2 = s_bot;
    s_compose_w_bot: forall s, s_compose s s_bot = s;
    s_compose_w_undef: forall s, s_compose s s_undef = s_undef;
    s_compose_complete_top: forall s, s_compose s_top s <> s_undef -> s = s_bot;
    s_top_not_bot: s_top <> s_bot;
    s_top_not_undef: s_top <> s_undef;
    s_ord : rel s_type;
    s_ord_refl : reflexive s_ord;
    s_ord_antis : antisymmetric s_ord;
    s_ord_trans : transitive s_ord;
    s_ord_total : total s_ord
  }.

  (** The Fractional Permission Separation Algebra **)
  Module Fp.
    Local Definition ok (q : Qc) : Prop :=
      match Qccompare 0 q , Qccompare q 1 with
      | Gt , _
      | _ , Gt => False
      | _ , _ => True
      end.
    Lemma to_prop : forall q, ok q <-> 0 <= q <= 1.
    Proof.
      intros; unfold ok.
      destruct (0 ?= q) eqn:?.
      { eapply Qceq_alt in Heqc; subst.
        compute. firstorder congruence. }
      { eapply Qclt_alt in Heqc.
        destruct (q ?= 1) eqn:X;
          [ eapply Qceq_alt in X | eapply Qclt_alt in X | eapply Qcgt_alt in X ].
        { subst. split; auto.
          compute; firstorder; congruence. }
        { split; auto.
          intro. split;
          eapply Qclt_le_weak; eauto. }
        { split; try tauto.
          destruct 1.
          eapply Qclt_not_le in X. tauto. } }
      { split; try tauto.
        eapply Qcgt_alt in Heqc.
        eapply Qclt_not_le in Heqc.
        destruct 1. tauto. }
    Qed.

    Definition is_ok q : {ok q} + {~ok q}.
      unfold ok.
      destruct (0 ?= q); destruct (q ?= 1);
        solve [ left ; trivial | right; tauto ].
    Defined.

    Lemma ok_irr : forall a (x y : ok a), x = y.
    Proof.
      unfold ok. intros.
      destruct (0 ?= a); destruct (a ?= 1); try contradiction.
      all: destruct x; destruct y; auto.
    Qed.

    Inductive Fp :=
    | FPerm (f:Qc) (UNIT: ok f)
    | FPermUndef.

    Definition Fp_zero : Fp :=
      FPerm 0 ltac:(compute; split; congruence).

    Definition Fp_full : Fp :=
      FPerm 1 ltac:(compute; split; congruence).

    Lemma FPerm_Equal: forall f g UNITf UNITg ,
        f = g -> FPerm f UNITf = FPerm g UNITg.
    Proof.
      intros. subst. f_equal.
      eapply ok_irr.
    Qed.

    Lemma FPerm_Inj : forall a b c d,
        FPerm a b = FPerm c d ->
        a = c.
    Proof. inversion 1; auto. Qed.

    (*Composition over fractional permissions*)
    Definition FPerm_Compose f g :=
      match f, g return Fp with
      | FPermUndef, _ => FPermUndef
      | _, FPermUndef => FPermUndef
      | FPerm f' _ , FPerm g' _ =>
        match is_ok (f' + g') with
        | left Pred => FPerm (f' + g') Pred
        | right _ => FPermUndef
        end
      end.

    (*Order*)
    Definition FPerm_Order f g : bool :=
      match f, g with
      | FPermUndef, _ => true
      | FPerm _ _, FPermUndef => false
      | FPerm f' _, FPerm g' _ =>
        match Qccompare f' g' with
        | Lt | Eq => true
        | _ => false
        end
      end.

    (* Example carrier monoid *)
    Program Definition Fp_Monoid : SA :=
      {| s_type := Fp;
         s_bot := Fp_zero ;
         s_top := Fp_full ;
         s_undef := FPermUndef;
         s_compose := FPerm_Compose;
         s_ord := FPerm_Order
      |}.
    Next Obligation.
      destruct s1; destruct s2; simpl; auto.
      rewrite Qcplus_comm. reflexivity.
    Qed.
    Next Obligation.
      destruct s1; destruct s2; destruct s3; simpl; auto.
      unfold FPerm_Compose.
      repeat match goal with
             | |- _ => eapply FPerm_Equal
             | |- FPerm _ _ = FPermUndef => exfalso
             | |- FPermUndef = FPerm _ _ => exfalso
             | _ : context [ match ?X with _ => _ end ] |- _ =>
               lazymatch X with
               | match _ with _ => _ end => fail
               | _ => destruct X; simpl
               end
             | |- context [ match ?X with _ => _ end ] =>
               lazymatch X with
               | match _ with _ => _ end => fail
               | _ => destruct X; simpl
               end
             | H : FPerm _ _ = FPerm _ _ |- _ => inversion H; clear H; subst
             | H : ok _ |- _ => eapply to_prop in H
             end; simpl; eauto.
      - ring.
      - eapply n. eapply to_prop. rewrite Qcplus_assoc. auto.
      - eapply n. eapply to_prop. rewrite Qcplus_comm.
        admit.
      - admit.
      - admit.
      - unfold FPerm_Compose.
        destruct (is_ok (f + f0)); auto.
    Admitted.
    Next Obligation.
      unfold FPerm_Compose in *.
      destruct s1; destruct s2; try congruence.
      destruct s1'; try congruence.
      destruct (is_ok (f + f0)).
      { destruct (is_ok (f1 + f0)).
        { eapply FPerm_Inj in H0.
          revert UNIT. cutrewrite (f = f1).
          intros.
          eapply FPerm_Equal; eauto.
          admit. }
        { congruence. } }
      { congruence. }
    Admitted.
    Next Obligation.
      split.
    Admitted.
    Next Obligation.
    Admitted.
    Next Obligation.
    Admitted.
    Next Obligation.
    Admitted.
    Next Obligation.
    Admitted.
    Next Obligation.
    Admitted.
    Next Obligation.
    Admitted.
    Next Obligation.
    Admitted.

  End Fp.

  Import Fp.

  (* A note to Gregory, If I were to paramterize mpred (p:Fp_Monoid) ...
   * THIS WOULD BE A NEAT SOLUTION.
   * I dont like them to be separate axioms. It is a ad-hoc solution,
   * but lets keep it as it for now.
   *)
  Axiom logical_fptsto: forall (Prm: SA) (p: Prm) (l: val) (v : val), mpred.

  Definition Frac_PointsTo l q v :=
    match is_ok q with
    | right _ => lfalse
    | left pf =>
      match q ?= 0 with
      | Eq => empSP
      | _ => logical_fptsto Fp.Fp_Monoid (Fp.FPerm q pf)  l v
      end
    end.


  (*Similarly one can encode ghost state using SA*)
  (*
   This type extends as we introduce new logical assertions such as logical_ghost etc.
   A generic ghost location gl and a value kept gv.

     A General Note to Gregory : If we want to refer to resources encoded via monoids
      -- let's say Pg -- then we     have to bookkeep/pass  guard and containers (guard: In monoid_instance guard_container).

    I did not do bookeeping of Monoids -- guard: In MONID LIST MONOID -- for fractional permissions and pointsto but in general we have to have the following structure for all logical predicates.

   Specs below assume that we do not refer to any resource encoded via monoids so there exists no guard and monoid container that we defined above. In case we want you can introduce them to the specs below.
   *)
  Variable guard_container : list SA.
  Axiom logical_ghost: forall (ghost : SA) (guard : In ghost guard_container)  (gl : ghost) (gv : val), mpred.

  (*
    Gregory suggests emp |- Exists g. g:m
  *)
  Parameter wp_ghst : Expr -> (val -> mpred) -> mpred.

   (*
     {P} E {Q}
    ------------
    {P} E {Q * exists l. l:g} //ghost location l carries the ghost resource g
   *)

  (*******Atomic Instruction Specification*******)
  Axiom rule_ghost_intro:
  forall  g P E Qp CMI (guard: In CMI guard_container) (ptriple: P |-- (wp_ghst E Qp)),
     P |-- wp_ghst E (fun v =>  (Qp v) ** (Exists l, logical_ghost CMI  guard l g)).

  (****** Wp Semantics for atomic operations
   * These are given in the style of function call axioms
   *)
  Parameter wp_atom : AtomicOp -> list val -> type -> (val -> mpred) -> mpred.

  Axiom wp_rhs_atomic: forall rslv ti r ao es ty Q,
      wps (wpAnys (resolve:=rslv) ti r) es  (fun (vs : list val) (free : FreeTemps) =>
           wp_atom ao vs ty (fun v => Q v free)) empSP
      |-- wp_rhs (resolve:=rslv) ti r (Eatomic ao es ty) Q.

  (* Ideas adopted from the paper:
   * Relaxed Separation Logic: A program logic for C11 Concurrency -- Vefeiadis et al.
   *)

  (*Atomic CAS access permission*)
  Parameter AtomInv : Fp.Fp -> type -> (val -> mpred) -> Rep.

(*
  (*Atomic READ access permission*)
  Parameter AtomRDPerm: val -> (val -> mpred) -> mpred.

  (*Atomic WRITE access permission*)
  Parameter AtomWRTPerm: val -> (val -> mpred) -> mpred.
*)

(*
  (* Perm LocInv l * Perm LocInv' l -|- Perm LocInv*LocInv' l
    Composability of two location invariant maps: val -> mpred on location l
    todo(isk): Existentials are weak?
   *)
  Axiom Splittable_RDPerm: forall (LocInv: val->mpred) (LocInv':val->mpred) l,
      AtomRDPerm l LocInv **  AtomRDPerm l LocInv'
      -|- Exists v, (Exists LocInv'', (LocInv'' v -* (LocInv' v ** LocInv v)) //\\ (AtomRDPerm v LocInv'')).
*)

  (*Atomic CAS access permission is duplicable*)
  Axiom Persistent_CASPerm : forall q1 q2 ty LocInv,
      AtomInv (s_compose Fp_Monoid q1 q2) ty LocInv -|- AtomInv q1 ty LocInv ** AtomInv q2 ty LocInv.

  (*Generate atomic access token via consuming the memory cell and the invariant *)
  Axiom Intro_AtomInv : forall x (t:type) (Inv:val->mpred),
      Exists v, _at (_eq x) (tprim t v) ** Inv v -|- _at (_eq x) (AtomInv Fp_full t Inv).

  (*Memory Ordering Patterns: Now we only have _SEQ_CST *)
  Definition _SEQ_CST := Vint 5.

(*
  (* *)
  Axiom Splittable_WRTPerm: forall (LocInv: val->mpred) (LocInv':val->mpred) l ,  AtomRDPerm l LocInv **  AtomRDPerm l LocInv'
                           -|- Exists v, (Exists LocInv'', (LocInv'' v -* (LocInv' v \\// LocInv v)) //\\ (AtomRDPerm v LocInv'')).
*)

  (* note(gmm): these are used for reading and writing without compare *)
  (*todo(isk): give up the permission to read the same value again with same permission *)
  Axiom rule_atomic_load_cst
  : forall q memorder (acc_type:type) l (Inv Qlearn: val -> mpred) P Q
      (read : forall v, P ** Inv v |-- Inv v ** Qlearn v),
      _at (_eq l) (AtomInv q acc_type Inv) **
      P **
      [| memorder = _SEQ_CST |] **
      (Forall x, (Qlearn x ** _at (_eq l) (AtomInv q acc_type Inv)) -* Q x)
      |-- wp_atom AO__atomic_load_n (l :: memorder :: nil) acc_type Q.

  Axiom rule_atomic_store_cst
  : forall q memorder (acc_type:type) l (Inv Qlearn : val -> mpred) P Q
      val
      (store : forall v, P ** Inv v |-- Inv val ** Qlearn v),
      _at (_eq l) (AtomInv q acc_type Inv) **
      P **
      [| memorder = _SEQ_CST |] **
      (Forall x, (Qlearn x ** _at (_eq l) (AtomInv q acc_type Inv)) -* Q x)
      |-- wp_atom AO__atomic_store_n (l :: memorder :: val :: nil) (Qmut Tvoid) Q.

  Definition Fp_readable (f : Fp) : Prop :=
    match f with
    | FPerm f _ => (0 < f)%Q
    | _ => False
    end.

  (* atomic compare and exchange n *)
  Axiom rule_atomic_compare_exchange_n:
    forall q P val_p expected_p desired wk succmemord failmemord Qp Q' Qlearn (Q:mpred)
           (ty : type)
           expected
           (preserve:  P ** Qp expected  |-- Qp desired ** Q)
           (learn : forall actual, actual <> expected ->
                              P ** Qp actual |-- (Qlearn actual //\\ empSP) ** ltrue),
      Fp_readable q ->
         _at (_eq expected_p) (tprim ty expected) **
         _at (_eq val_p) (AtomInv q ty Qp) **
         P **
         [|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
         ((((* success *)
            _at (_eq expected_p) (tprim ty expected) **
            _at (_eq val_p) (AtomInv q ty Qp) ** Q) -* Q' (Vbool true)) //\\
          (((* failure *)
            Exists x, [| x <> expected |] ** Qlearn x **
              _at (_eq expected_p) (tprim ty x) **
              _at (_eq val_p) (AtomInv q ty Qp) **
              P) -* Q' (Vbool false)))
       |-- wp_atom AO__atomic_compare_exchange_n
                   (val_p::succmemord::expected_p::failmemord::desired::wk::nil) (Qmut Tbool) Q'.



  (* atomic compare and exchange rule
   *)
  Axiom rule_atomic_compare_exchange:
    forall q P val_p expected_p desired_p wk succmemord failmemord Qp Q' Qlearn (Q:mpred)
      (ty : type)
      expected desired
      (preserve:  P ** Qp expected  |-- Qp desired ** Q)
      (learn : forall actual, actual <> expected ->
                         P ** Qp actual |-- (Qlearn actual //\\ empSP) ** ltrue),
      Fp_readable q ->
         _at (_eq expected_p) (tprim ty expected) **
         _at (_eq desired_p) (tprim ty desired) **
         _at (_eq val_p) (AtomInv q ty Qp) ** P **
         [|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
         ((((* success *)
            _at (_eq expected_p) (tprim ty expected) **
            _at (_eq desired_p) (tprim ty desired) **
            _at (_eq val_p) (AtomInv q ty Qp) ** Q) -* Q' (Vbool true)) //\\
          (((* failure *)
            Exists x, [| x <> expected |] ** Qlearn x **
              _at (_eq expected_p) (tprim ty x) **
              _at (_eq desired_p) (tprim ty desired) **
              _at (_eq val_p) (AtomInv q ty Qp) **
              P) -* Q' (Vbool false)))
       |-- wp_atom AO__atomic_compare_exchange
                   (val_p::succmemord::expected_p::failmemord::desired::wk::nil) (Qmut Tbool) Q'.

  (* atomic fetch and xxx rule *)
  Definition rule_fetch_xxx ao op : Prop :=
    forall q P E Qp pls memorder Q Q'
         (acc_type : type)
         (split: forall v,  P ** Qp v |--
                         Exists v', [| eval_binop op acc_type acc_type acc_type v pls v' |] **
                                    Qp v' ** Q v),
      Fp_readable q ->
         _at (_eq E) (AtomInv q acc_type Qp) **
         [| memorder = _SEQ_CST |] ** P **
         (Forall x, (_at (_eq E) (AtomInv q acc_type Qp) ** Q x) -* Q' x)
       |-- wp_atom ao (E::pls::memorder::nil) acc_type Q'.

  Ltac fetch_xxx ao op :=
    let G := eval unfold rule_fetch_xxx in (rule_fetch_xxx ao op) in exact G.

  Axiom wp_atomic_fetch_add : ltac:(fetch_xxx AO__atomic_fetch_add Badd).
  Axiom rule_atomic_fetch_sub : ltac:(fetch_xxx AO__atomic_fetch_sub Bsub).
  Axiom rule_atomic_fetch_and : ltac:(fetch_xxx AO__atomic_fetch_and Band).
  Axiom rule_atomic_fetch_xor : ltac:(fetch_xxx AO__atomic_fetch_xor Bxor).
  Axiom rule_atomic_fetch_or : ltac:(fetch_xxx AO__atomic_fetch_or Bor).

  (* atomic xxx and fetch rule *)
  Definition rule_xxx_fetch ao op : Prop :=
    forall q P E Qp pls memorder Q Q'
         (acc_type : type)
         (split: forall v,  P ** Qp v |--
                         Exists v', [| eval_binop op acc_type acc_type acc_type v pls v' |] **
                                    Qp v' ** Q v'),
      Fp_readable q ->
         P ** _at (_eq E) (AtomInv q acc_type Qp) **
         [| memorder = _SEQ_CST |] **
         (Forall x, (_at (_eq E) (AtomInv q acc_type Qp) ** Q x) -* Q' x)
       |-- wp_atom ao (E::pls::memorder::nil) acc_type Q'.

  Ltac xxx_fetch ao op :=
    let G := eval unfold rule_xxx_fetch in (rule_xxx_fetch ao op) in exact G.

  Axiom wp_atomic_add_fetch : ltac:(xxx_fetch AO__atomic_add_fetch Badd).
  Axiom rule_atomic_sub_fetch : ltac:(xxx_fetch AO__atomic_sub_fetch Bsub).
  Axiom rule_atomic_and_fetch : ltac:(xxx_fetch AO__atomic_and_fetch Band).
  Axiom rule_atomic_xor_fetch : ltac:(xxx_fetch AO__atomic_xor_fetch Bxor).
  Axiom rule_atomic_or_fetch : ltac:(xxx_fetch AO__atomic_or_fetch Bor).
End cclogic.

Declare Module CCL : cclogic.

Export CCL.
