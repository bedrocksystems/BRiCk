Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Permutation.
From Coq.QArith Require Import QArith Qcanon.
Require Import Coq.QArith.Qfield.
From Coq.micromega Require Import
     QMicromega Psatz.

Require Import Coq.ssr.ssrbool.

From Coq.Classes Require Import
     RelationClasses Morphisms DecidableClass.

From ChargeCore.SepAlg Require Import SepAlg.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Semantics Logic PLogic Wp Expr.
From Cpp.Auto Require Import
     Discharge.

Require Import ExtLib.Data.Member.
Fixpoint remove {T} {t : T} {ls : list T} (m : member t ls) : list T :=
  match m with
  | @MZ _ _ ls => ls
  | @MN _ _ l _ m => l :: remove m
  end.


Lemma lforall_specialize : forall {T} (x : T) (P : T -> mpred),
    lforall P |-- P x.
Proof. intros. eapply lforallL. reflexivity. Qed.

(* todo(gmm): move the above definitions *)

(* semantics of atomic builtins
 * https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
 *)

Module Type cclogic.

  (****** Logical State ********)

  (* the type of (functional) separation algebras
   * note(gmm): this definition differs from the ChargeCore definition
   * because it defines `compose` as a function rather than as a relation.
   *)
  Polymorphic Structure SA :=
  { s_type :> Type;
    s_bot: s_type;
    s_top: s_type;
    s_undef: s_type;
    s_compose: s_type -> s_type -> s_type;
    s_compose_com: forall s1 s2, s_compose s1 s2 = s_compose s2 s1;
    s_compose_assoc: forall s1 s2 s3,
        s_compose (s_compose s1 s2) s3 = s_compose s1 (s_compose s2 s3);
    s_compose_cancel: forall s1 s1' s2,
        s_compose s1 s2 <> s_undef ->
        s_compose s1 s2 = s_compose s1' s2 -> s1 = s1';
    s_compose_bot: forall s1 s2,
        s_compose s1 s2 = s_bot -> s1 = s_bot /\ s2 = s_bot;
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

    Variant Fp : Set :=
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
      - eapply n; clear n. eapply to_prop.
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

  Notation "a ⊕ b" := (s_compose _ a b) (at level 50, left associativity).

  (* the names of invariants *)
  Definition iname : Set := (string * string).

  Definition namespace (pkg s : string) : iname :=
    (pkg, s)%string.

  (* named invariants *)
  Parameter Inv : forall (name : iname) (I : mpred), mpred.
  (* ^ the invariant [I] must be droppable *)

  Definition infinite (t : Type) : Prop :=
    exists (for_each : nat -> t),
      forall n1 n2, n1 <> n2 -> for_each n1 <> for_each n2.

  Axiom Inv_new : forall pkg I,
      I |-- empSP -> (* droppable *)
      empSP |-- Exists n : _, Inv (namespace pkg n) I.
  Axiom Inv_dup : forall (n : iname) I, Inv n I -|- Inv n I ** Inv n I.
  Axiom Inv_drop : forall (n : iname) I, Inv n I |-- empSP.

  (* trackable (named) invariants *)
  Parameter TInv : forall (_ : iname) (I : mpred), mpred.
  (* ^ the invariant [I] has no restrictions *)
  Axiom TInv_dup : forall (n : iname) I, TInv n I -|- TInv n I ** TInv n I.
  Axiom TInv_drop : forall (n : iname) I, TInv n I |-- empSP.

  Parameter OPerm : Fp -> iname -> mpred.
  Parameter DPerm : iname -> mpred.
  Axiom OPerm_split : forall (f1 f2 : Fp_Monoid) n,
      OPerm (f1 ⊕ f2) n -|- OPerm f1 n ** OPerm f2 n.

  Axiom TInv_new : forall pkg I,
      I |-- Exists n : _,
            let n := namespace pkg n in
            TInv n I ** OPerm Fp_Monoid.(s_top) n ** DPerm n.

  Definition disjoint {T} (xs ys : list T) : Prop :=
    List.Forall (fun x => ~List.In x ys) xs.
  Definition subset {T} (xs ys : list T) : Prop :=
    List.Forall (fun x => List.In x ys) xs.

  (* view shifts
   * - this is an entirely different notion of entailment because it enables
   *   updating ghost state.
   *)
  Module shift.
    Parameter shift : mpred -> list iname -> list iname -> mpred -> mpred -> Prop.

    Axiom shift_id : forall P,
        shift P nil nil empSP empSP.
    Axiom shift_frame : forall P e1 e2 e' Q R S,
        disjoint e1 e' ->
        disjoint e2 e' ->
        shift P e1 e2 Q R ->
        shift P (e1 ++ e') (e2 ++ e') (Q ** S) (R ** S).
    Axiom shift_trans : forall P e1 e2 e3 Q R S,
        subset e2 (e1 ++ e3) ->
        shift P e1 e2 Q R ->
        shift P e2 e3 R S ->
        shift P e1 e3 Q S.
    Axiom shift_open : forall P Q i,
        P |-- Inv i Q ** ltrue ->
        shift P (i :: nil) nil empSP Q.
    Axiom shift_close : forall P Q i,
        P |-- Inv i Q ** ltrue ->
        shift P nil (i :: nil) Q empSP.
    Axiom shift_opent : forall P Q i,
        P |-- TInv i Q ** ltrue ->
        shift P (i :: nil) nil empSP Q.
    Axiom shift_closet : forall P Q i,
        P |-- TInv i Q ** ltrue ->
        shift P nil (i :: nil) Q empSP.

    Axiom shift_Proper :
      Proper (lentails ++> @Permutation iname ++> @Permutation iname ++> lentails --> lentails ++> Basics.impl)
             shift.
    Global Existing Instance shift_Proper.

  End shift.

  Module shift'.
    Variant Inv_type : Set :=
    | Affine
    | Tracked (_ : Fp).
    Parameter shift : list (iname * Inv_type) -> list (iname * Inv_type) -> mpred -> mpred -> mpred.

    Axiom shift_id :
      empSP |-- shift nil nil empSP empSP.
    Axiom shift_frame : forall e1 e2 e' Q R S,
        disjoint (map fst e1) (map fst e') ->
        disjoint (map fst e2) (map fst e') ->
        shift e1 e2 Q R |-- shift (e1 ++ e') (e2 ++ e') (Q ** S) (R ** S).
    Axiom shift_trans : forall e1 e2 e3 Q R S,
        subset e2 (e1 ++ e3) ->
        shift e1 e2 Q R ** shift e2 e3 R S |-- shift e1 e3 Q S.
    Axiom shift_open : forall Q i,
        Inv i Q |-- shift ((i,Affine) :: nil) nil empSP Q.
    Axiom shift_close : forall Q i,
        Inv i Q |-- shift nil ((i,Affine) :: nil) Q empSP.
    Axiom shift_opent : forall Q i,
        TInv i Q |-- Forall q, shift ((i,Tracked q) :: nil) nil (OPerm q i) Q.
    Axiom shift_closet : forall Q i,
        TInv i Q |-- Forall q, shift nil ((i,Tracked q) :: nil) Q (OPerm q i).
    Axiom shift_deletet : forall Q i,
        TInv i Q
        |-- Forall q, shift nil ((i,Tracked q) :: nil) (OPerm q i -* OPerm Fp_Monoid.(s_top) i ** DPerm i) empSP.
    (* ^ note(gmm): the `q` permission was opened already, so you get that in
     * order to establish the final `OPerm 1`
     *)

    Axiom shift_Proper :
      Proper (    @Permutation _ ++> @Permutation _ ++> lentails --> lentails ++> lentails)
             shift.
    Global Existing Instance shift_Proper.

  End shift'.
  Import shift'.

  Parameter SA_fmap : forall (k : Type) {_ : forall a b : k, Decidable (a = b)} (v : SA), SA.
  Parameter fmap_singleton : forall {k} {dec : forall a b : k, Decidable (a = b)} (v : SA),
      k -> v.(s_type) -> (@SA_fmap k dec v).(s_type).

  (* A note to Gregory, If I were to paramterize mpred (p:Fp_Monoid) ...
   * THIS WOULD BE A NEAT SOLUTION.
   * I dont like them to be separate axioms. It is a ad-hoc solution,
   * but lets keep it as it for now.
   * ^^ note(gmm): agreed. this would be a fairly simple solution.
   *    it would require that all of our code is verified with respect to
   *    arbitrary `Fp_Monoid` that contain some (relevant) monoids.
   *    an alternative would be to build a universal [Fp_Monoid] (up to
   *    universe polymorphism) and then provide a way to do allocation.
   *    this would be analagous to:
   *      [mpred Universal]
   *    where [Universal] is:
   *      Definition Universal@{i j | j < i} : Type@{i} :=
   *        forall ra : RA@{j}, ra.(s_type).
   *    which gives me access to any resource algebra of universe less than [i].
   *    it is important to note that in almost all circumstances, the practical
   *    separation algebras that we are going to use are those with finite maps,
   *    so it might be a little bit easier to say.
   *      Definition Universal@{i j | j < i} : Type@{i} :=
   *        forall ra : RA@{j}, Fmap nat ra.(s_type),
   *)
  Parameter ghost_is : forall (Prm: SA) (value : Prm), mpred.
  Definition ghost_ptsto {loc : Type} {dec : forall a b : loc, Decidable (a = b)}
             (Prm : SA) (p : loc) (value : Prm) : mpred :=
    ghost_is (SA_fmap loc Prm) (@fmap_singleton loc _ Prm p value).

  (* note(gmm): i can update any ghost location as long as I have exclusive
   * ownership of it.
   *)
  Axiom shift_ghost_update : forall loc dec prm p v v',
      |-- shift nil nil
                (@ghost_ptsto loc dec prm p v)
                (@ghost_ptsto loc dec prm p v').

  (* Definition Frac_PointsTo l q v := *)
  (*   match is_ok q with *)
  (*   | right _ => lfalse *)
  (*   | left pf => *)
  (*     match q ?= 0 with *)
  (*     | Eq => empSP *)
  (*     | _ => ghost_ptsto Fp.Fp_Monoid (Fp.FPerm q pf)  l v *)
  (*     end *)
  (*   end. *)


  (*Similarly one can encode ghost state using SA*)
  (*
   This type extends as we introduce new logical assertions such as
   logical_ghost etc.
   A generic ghost location gl and a value kept gv.
   A General Note to Gregory : If we want to refer to resources encoded via monoids
      -- let's say Pg -- then we have to bookkeep/pass guard and containers (guard: In monoid_instance guard_container).

    I did not do bookeeping of Monoids -- guard: In MONID LIST MONOID -- for fractional permissions and pointsto but in general we have to have the following structure for all logical predicates.

   Specs below assume that we do not refer to any resource encoded via monoids so there exists no guard and monoid container that we defined above. In case we want you can introduce them to the specs below.
   *)
(*
  Variable guard_container : list SA.
  Axiom logical_ghost: forall (ghost : SA) (guard : In ghost guard_container)  (gl : ghost) (gv : val), mpred.
*)

  (* Parameter wp_ghst : Expr -> (val -> mpred) -> mpred. *)

   (*
     {P} E {Q}
    ------------
    {P} E {Q * exists l. l:g} //ghost location l carries the ghost resource g
   *)

  (* (*******Atomic Instruction Specification*******) *)
  (* Axiom rule_ghost_intro: *)
  (* forall  g P E Qp CMI (guard: In CMI guard_container) (ptriple: P |-- wp_ghst E Qp), *)
  (*    P |-- wp_ghst E (fun v =>  (Qp v) ** (Exists l, logical_ghost CMI  guard l g)). *)

  (* a "weakest pre-condition" for view shifts
   * note(gmm): in this style, we don't need to explicitly quantify over the
   * final open invariants.
   *)
  Parameter wp_shift : forall (mask : list (iname * Inv_type)),
      (list (iname * Inv_type) -> mpred) -> mpred.

  Axiom wp_shift_done : forall Q mask,
      Q mask |-- wp_shift mask Q.

  (* the rest of these need access to [P] in order to know where
   * to pull invariants from.
   *)
  Axiom wp_shift_vs : forall P from to Q,
    shift from to P Q
    |-- (* persistent *) Forall Z, ((P ** (Q -* wp_shift from Z)) -* wp_shift to Z).

  (* the next 4 axioms should be derivable from [wp_shift_vs] *)
  Theorem wp_shift_open : forall Q hide n I,
      ~In n (map fst hide) ->
      Inv n I ** (I -* wp_shift ((n, Affine) :: hide) Q)
      |-- wp_shift hide Q.
  Proof.
    intros.
    rewrite shift_open.
    erewrite shift_frame with (e':=hide) (S:=empSP).
    2:{ simpl. red. constructor. auto. constructor. }
    2:{ simpl. constructor. }
    rewrite wp_shift_vs.
    simpl.
    perm_right ltac:(idtac; perm_left ltac:(idtac; eapply use_universal_arrow)).
    discharge fail fail fail fail eauto.
    perm_right ltac:(idtac; perm_left ltac:(idtac; eapply wandSP_cancel)).
    discharge fail fail fail fail eauto.
  Qed.
  Theorem wp_shift_openT : forall q Q hide n I,
      ~In n (List.map fst hide) ->
      TInv n I ** OPerm q n ** (I -* wp_shift ((n, Tracked q) :: hide) Q)
      |-- wp_shift hide Q.
  Proof.
    intros.
    rewrite shift_opent.
    erewrite lforall_specialize.
    erewrite shift_frame with (e':=hide) (S:=empSP).
    2:{ simpl. red. constructor. auto. constructor. }
    2:{ simpl. constructor. }
    rewrite wp_shift_vs.
    simpl.
    perm_right ltac:(idtac; perm_left ltac:(idtac; eapply use_universal_arrow)).
    discharge fail fail fail fail eauto.
    perm_right ltac:(idtac; perm_left ltac:(idtac; eapply wandSP_cancel)).
    discharge fail fail fail fail eauto.
  Qed.


  Theorem wp_shift_close : forall Q hide n I,
      ~In n (map fst hide) ->
      Inv n I ** (I ** wp_shift hide Q)
      |-- wp_shift ((n,Affine) :: hide) Q.
  Proof.
    intros.
    rewrite shift_close.
    erewrite shift_frame with (e':=hide) (S:=empSP).
    2:{ simpl. constructor. }
    2:{ subst. simpl. constructor; [ | constructor ]; auto. }
    rewrite wp_shift_vs.
    simpl.
    perm_right ltac:(idtac; perm_left ltac:(idtac; eapply use_universal_arrow)).
    discharge fail fail fail fail eauto.
  Qed.
  Theorem wp_shift_closeT : forall (q : Fp_Monoid.(s_type)) Q hide n I,
      ~In n (map fst hide) ->
      TInv n I ** I ** (OPerm q n -* wp_shift hide Q)
      |-- wp_shift ((n, Tracked q) :: hide) Q.
  Proof.
    intros.
    rewrite shift_closet.
    erewrite lforall_specialize.
    erewrite shift_frame with (e':=hide) (S:=empSP).
    2:{ simpl. constructor. }
    2:{ subst. simpl. constructor; [ | constructor ]; auto. }
    rewrite wp_shift_vs.
    simpl.
    perm_right ltac:(idtac; perm_left ltac:(idtac; eapply use_universal_arrow)).
    discharge fail fail fail fail eauto.
    perm_right ltac:(idtac; perm_left ltac:(idtac; eapply wandSP_cancel)).
    discharge fail fail fail fail eauto.
  Qed.
  Theorem wp_shift_deleteT : forall (q : Fp_Monoid.(s_type)) Q hide n I,
      ~In n (map fst hide) ->
      TInv n I ** (OPerm q n -* OPerm Fp_Monoid.(s_top) n ** DPerm n) ** wp_shift hide Q
      |-- wp_shift ((n, Tracked q) :: hide) Q.
  Proof.
    intros.
    rewrite shift_deletet.
    erewrite lforall_specialize.
    erewrite shift_frame with (e':=hide).
    2:{ simpl. constructor. }
    2:{ subst. simpl. constructor; [ | constructor ]; auto. }
    simpl.
    rewrite wp_shift_vs.
    perm_right ltac:(idtac; perm_left ltac:(idtac; eapply use_universal_arrow)).
    discharge fail fail fail fail eauto.
    instantiate (1:=empSP).
    repeat rewrite empSPL.
    discharge fail fail fail fail eauto.
  Qed.

  (****** Wp Semantics for atomic operations
   * These are given in the style of function call axioms
   *)
  Parameter wp_atom : AtomicOp -> list val -> type -> (val -> mpred) -> mpred.

  (* note that this rule captures all of the interesting reasoning about atomics
   * through the use of [wp_shift]
   *)
  Axiom wp_rhs_atomic: forall rslv ti r ao es ty Q,
      wps (wpAnys (resolve:=rslv) ti r) es  (fun (vs : list val) (free : FreeTemps) =>
           wp_shift nil (fun opened => wp_atom ao vs ty (fun v => wp_shift opened (fun to => [| to = nil |] ** (Q v free))))) empSP
      |-- wp_rhs (resolve:=rslv) ti r (Eatomic ao es ty) Q.

  (* Ideas adopted from the paper:
   * Relaxed Separation Logic: A program logic for C11 Concurrency -- Vefeiadis et al.
   *)

  (*Atomic CAS access permission*)
  Definition AtomInv (fp : Fp.Fp) (n : iname) (t : type) (I : val -> mpred) : Rep :=
    {| repr p := TInv n (Exists v, _at (_eq p) (tprim t v) ** I v) **
                 OPerm fp n |}.
  (* ^ note(gmm): i introduced names here so that these can fit into TInv, but another way
   * to do this is to track the used tokens by associating them with the pointers.
   * this would mean that you have a simple atomics library that provides a logical
   * way to allocate an [AtomInv]. Doing this seems to *require* a way to
   * drop the [infinite] premise above and state "this token is not used".
   * - alternatively, there is the possibility to allocate 1 large invariant
   *   and use it to mitigate all of the definitions.
   *)
  (* ^ note(gmm): i really wanted to put `DPerm n` inside the invariant, but it doesn't
   * work in the normal Iron++ logic (which most closely resembles what we have)
   *)

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

  (* Atomic CAS access permission is a trackable invariant *)
  Theorem Persistent_CASPerm : forall (q1 q2 : Fp_Monoid) (n : iname) ty LocInv,
      AtomInv (q1 ⊕ q2) n ty LocInv -|- AtomInv q1 n ty LocInv ** AtomInv q2 n ty LocInv.
  Proof.
    unfold AtomInv.
    Transparent sepSP. simpl. Opaque sepSP.
    split; simpl; intros.
    { rewrite TInv_dup at 1; rewrite OPerm_split. discharge fail fail fail fail eauto. }
    { rewrite TInv_dup at 3; rewrite OPerm_split. discharge fail fail fail fail eauto. }
  Qed.

  (*Generate atomic access token via consuming the memory cell and the invariant *)
  Theorem Intro_AtomInv : forall x pkg (t:type) (Inv:val->mpred),
      Exists v, _at (_eq x) (tprim t v) ** Inv v
      |-- Exists n : string, let n := namespace pkg n in
                             _at (_eq x) (AtomInv Fp_full n t Inv) ** DPerm n.
  Proof.
    intros.
    unfold AtomInv.
    etransitivity.
    eapply TInv_new; eauto.
    Transparent _at. unfold _at. Opaque _at.
    simpl.
    discharge fail fail fail fail eauto.
  Qed.

  (*Memory Ordering Patterns: Now we only have _SEQ_CST *)
  Definition _SEQ_CST := Vint 5.

  (* note(gmm): these are used for reading and writing values shared between
   * threads.
   * note(gmm): these look exactly like the standard read and write assertions
   * because all of the invariant reasoning is encapsulated in [wp_shift].
   *)
  Axiom rule_atomic_load_cst
  : forall memorder (acc_type:type) (l : val) (Q : val -> mpred),
      [| memorder = _SEQ_CST |] **
      (Exists v, (_at (_eq l) (tprim acc_type v) ** ltrue //\\ Q v))
      |-- wp_atom AO__atomic_load_n (l :: memorder :: nil) acc_type Q.

(*
  Axiom rule_atomic_load_cst
  : forall q memorder (acc_type:type) name (nm : name) l (Inv Qlearn: val -> mpred) P Q
      (read : forall v, P ** Inv v |-- Inv v ** Qlearn v),
      _at (_eq l) (AtomInv q nm acc_type Inv) **
      P **
      [| memorder = _SEQ_CST |] **
      (Forall x, (Qlearn x ** _at (_eq l) (AtomInv q nm acc_type Inv)) -* Q x)
      |-- wp_atom AO__atomic_load_n (l :: memorder :: nil) acc_type Q.
*)

  Axiom rule_atomic_store_cst
  : forall memorder (acc_type:type) l Q val,
      [| memorder = _SEQ_CST |] **
      (Exists val, _at (_eq l) (tprim acc_type val)) **
      (_at (_eq l) (tprim acc_type val) -* Forall void, Q void)
      |-- wp_atom AO__atomic_store_n (l :: memorder :: val :: nil) (Qmut Tvoid) Q.

(*
  Axiom rule_atomic_store_cst
  : forall q memorder (acc_type:type) {name} (nm : name) l (Inv Qlearn : val -> mpred) P Q
      val
      (store : forall v, P ** Inv v |-- Inv val ** Qlearn v),
      _at (_eq l) (AtomInv q nm acc_type Inv) **
      P **
      [| memorder = _SEQ_CST |] **
      (Forall x, (Qlearn x ** _at (_eq l) (AtomInv q nm acc_type Inv)) -* Q x)
      |-- wp_atom AO__atomic_store_n (l :: memorder :: val :: nil) (Qmut Tvoid) Q.
*)

  Definition Fp_readable (f : Fp) : Prop :=
    match f with
    | FPerm f _ => (0 < f)%Q
    | _ => False
    end.

  (* atomic compare and exchange n *)
  Axiom rule_atomic_compare_exchange_n:
    forall val_p expected_p desired wk succmemord failmemord Q'
           (ty : type)
           expected,
      ([|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
      (_at (_eq expected_p) (tprim ty expected) ** ltrue) //\\
      Exists v,
         (_at (_eq val_p) (tprim ty v) **
         ([| v = expected |] -*
          _at (_eq val_p) (tprim ty desired) -* Q' (Vbool true)) //\\
         ([| v <> expected |] -*
          _at (_eq val_p) (tprim ty v) -* Q' (Vbool false))))
       |-- wp_atom AO__atomic_compare_exchange_n
                   (val_p::succmemord::expected_p::failmemord::desired::wk::nil) (Qmut Tbool) Q'.
  About rule_atomic_compare_exchange_n.

(*
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
*)


  (* atomic compare and exchange rule
   *)
  Axiom rule_atomic_compare_exchange:
    forall q P val_p expected_p desired_p wk succmemord failmemord Qp Q' Qlearn (Q:mpred)
      (ty : type) n
      expected desired
      (preserve:  P ** Qp expected  |-- Qp desired ** Q)
      (learn : forall actual, actual <> expected ->
                         P ** Qp actual |-- (Qlearn actual //\\ empSP) ** ltrue),
      Fp_readable q ->
         _at (_eq expected_p) (tprim ty expected) **
         _at (_eq desired_p) (tprim ty desired) **
         _at (_eq val_p) (AtomInv q n ty Qp) ** P **
         [|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
         ((((* success *)
            _at (_eq expected_p) (tprim ty expected) **
            _at (_eq desired_p) (tprim ty desired) **
            _at (_eq val_p) (AtomInv q n ty Qp) ** Q) -* Q' (Vbool true)) //\\
          (((* failure *)
            Exists x, [| x <> expected |] ** Qlearn x **
              _at (_eq expected_p) (tprim ty x) **
              _at (_eq desired_p) (tprim ty desired) **
              _at (_eq val_p) (AtomInv q n ty Qp) **
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
*)
End cclogic.

Declare Module CCL : cclogic.

Export CCL.
