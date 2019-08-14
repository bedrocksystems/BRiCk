Require Import Coq.ZArith.BinInt.
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


Local Ltac t :=
  let cancel :=
      idtac; canceler ltac:(idtac; first [ eapply use_universal_arrow
                                         | eapply wandSP_cancel ]) ltac:(eauto) in
  discharge fail fail fail cancel eauto.


(* todo(gmm): move the above definitions *)

(* semantics of atomic builtins
 * https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
 *)

Module Type cclogic.

  (****** Logical State ********)
  (* the type of (functional) separation algebras
   * notes:
   * - like Iris (and unlike ChargeCore), this definition is functional
   *   rather than relational.
   * - this definition seems to be missing a way to test whether a value
   *   is [undef].
   * todo(gmm): I should replace this definition.
   *)
  Structure PCM@{i j} : Type@{j} :=
  { p_type :> Type@{i};
    p_bot: p_type;
    p_compose: p_type -> p_type -> p_type;
    p_valid : p_type -> Prop;
    p_compose_com: forall p1 p2, p_compose p1 p2 = p_compose p2 p1;
    p_compose_assoc: forall p1 p2 p3,
        p_compose (p_compose p1 p2) p3 = p_compose p1 (p_compose p2 p3);
    p_compose_bot: forall p1 p2,
        p_compose p1 p2 = p_bot -> p1 = p_bot /\ p2 = p_bot;
    p_compose_w_bot: forall p, p_compose p p_bot = p;
    p_valid_bot : p_valid p_bot;
    p_valid_compose : forall p1 p2, p_valid (p_compose p1 p2) -> p_valid p1 /\ p_valid p2
  }.

  Arguments p_bot {_}.
  Arguments p_valid {_}.
  Arguments p_compose {_} _ _.

  Notation "a ⊕ b" := (p_compose a b) (at level 50, left associativity).

  Definition p_compatible {pcm : PCM} (a b : pcm.(p_type)) : Prop :=
    p_valid (a ⊕ b).

  (* frame-preserving update
   * this is so primitive, that it seems like it should go somewhere else
   *)
  Definition FPU {pcm} (v : pcm.(p_type)) (V' : pcm.(p_type) -> Prop) : Prop :=
    forall f, p_compatible v f -> exists v', V' v' /\ p_compatible v' f.

  Definition FPU_single {pcm} (v v' : pcm.(p_type)) : Prop :=
    FPU v (eq v').

  (* a simple way to define monoids. *)
  Section PCM_option.
    Context {T : Type} (bot : T) (compose : T -> T -> option T)
            (valid : T -> Prop).
    Hypothesis comp_comm : forall a b, compose a b = compose b a.
    Hypothesis comp_assoc : forall t t0 t1,
        match compose t t0 with
        | Some a => compose a t1
        | None => None
        end = match compose t0 t1 with
              | Some b => compose t b
              | None => None
              end.
    Hypothesis valid_bot : valid bot.
    Hypothesis valid_comp : forall a b c, compose a b = Some c ->
                                     valid c -> valid a /\ valid b.
    Hypothesis comp_bot : forall a b, compose a b = Some bot -> a = bot /\ b = bot.
    Hypothesis comp_w_bot : forall a, compose a bot = Some a.

    Local Definition pcompose := fun a b =>
                                   match a , b with
                                   | Some a , Some b => compose a b
                                   | _ , _ => None
                                   end.

    Local Definition pvalid := fun p =>
                                 match p with
                                 | None => False
                                 | Some p => valid p
                                 end.

    Definition pPCM : PCM.
    Proof.
      refine {| p_type := option T
                ; p_bot := Some bot
                ; p_compose  := pcompose
                ; p_valid := pvalid
             |}.
      all: unfold pcompose, pvalid.
      { abstract (destruct p1, p2; auto). }
      { abstract (destruct p1; auto; destruct p2; auto; destruct p3; auto;
                  destruct (compose t t0); reflexivity). }
      { abstract (destruct p1, p2; simpl; auto; try discriminate;
                  intros; eapply comp_bot in H; destruct H; subst; auto). }
      { abstract (destruct p; auto). }
      { auto. }
      { destruct p1, p2; try solve [ intuition ].
        specialize (valid_comp t t0).
        destruct (compose t t0); eauto.
        contradiction. }
    Defined.

    Opaque pcompose pvalid.

  End PCM_option.

  (** The Fractional Permission PCM **)
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

    Variant _Fp : Set :=
    | FPerm (f:Qc) (UNIT: ok f).

    Definition _Fp_zero : _Fp :=
      FPerm 0 ltac:(compute; split; congruence).

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
    Definition FPerm_Compose f g : option _Fp :=
      match f, g with
      | FPerm f' _, FPerm g' _ =>
        match is_ok (f' + g') with
        | left Pred => Some (FPerm (f' + g') Pred)
        | right _ => None
        end
      end.

    Local Ltac qify :=
      repeat match goal with
             | [ q : Qc |- _ ] => destruct q as [q ?]
             end;
      cbv [Qcle Qclt Q2Qc Qcanon.this Qcplus] in *;
      rewrite !Qred_correct in *.

    Lemma Fp_compose_com : forall s1 s2,
        FPerm_Compose s1 s2 = FPerm_Compose s2 s1.
    Proof.
      destruct s1, s2; cbn; auto.
      now rewrite Qcplus_comm.
    Qed.

    Lemma Fp_compose_assoc : forall s1 s2 s3,
        match FPerm_Compose s1 s2 with
        | None => None
        | Some x => FPerm_Compose x s3
        end = match FPerm_Compose s2 s3 with
              | None => None
              | Some x => FPerm_Compose s1 x
              end.
    Proof.
      destruct s1, s2, s3; cbn; auto.
      - unfold FPerm_Compose.
        repeat match goal with
               | |- _ => eapply FPerm_Equal
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
               | H : ~ok _ |- False => eapply H; eapply to_prop; qify; lra
               | |- Some _ = Some _ => f_equal
               | |- Some _ = None => exfalso
               | |- None = Some _ => exfalso
               end; simpl; eauto.
        ring.
    Qed.

    Lemma Fp_compose_bot : forall s1 s2,
        FPerm_Compose s1 s2 = Some _Fp_zero ->
        s1 = _Fp_zero /\ s2 = _Fp_zero.
    Proof.
      unfold _Fp_zero.
      destruct s1, s2;
        cbn;
        try destruct is_ok;
        try congruence.
      intros H.
      Opaque Qplus.
      inversion H.
      pose proof (proj1 (to_prop _) UNIT).
      pose proof (proj1 (to_prop _) UNIT0).
      assert (f + f0 == 0)%Q by (now rewrite <-H1, Qred_correct).
      split;
        f_equal;
        apply FPerm_Equal;
        qify;
        apply Qc_is_canon;
        cbn;
        lra.
    Qed.

    Lemma Fp_compose_w_bot : forall s,
        FPerm_Compose s _Fp_zero = Some s.
    Proof.
      destruct s; cbn; auto.
      replace (f + 0) with f by ring.
      destruct is_ok; intuition.
      f_equal. now apply FPerm_Equal.
    Qed.

    (* Example carrier monoid *)
    Definition t : PCM.
    Proof.
      eapply (@pPCM _ _Fp_zero FPerm_Compose (fun _ => True)).
      { eapply Fp_compose_com. }
      { eapply Fp_compose_assoc. }
      { exact I. }
      { tauto. }
      { eapply Fp_compose_bot. }
      { eapply Fp_compose_w_bot. }
    Defined.

    Definition readable (f : t) : Prop :=
      match f with
      | Some (FPerm f _) => (0 < f)%Q
      | _ => False
      end.

    Definition Fp_zero : t :=
      Some (FPerm 1 ltac:(compute; split; congruence)).

    Definition Fp_full : t :=
      Some (FPerm 1 ltac:(compute; split; congruence)).

  End Fp.
  Definition Fp := Fp.t.

  Module fmap.
    (* question(gmm): is it possible to avoid the [Decidable] issue?
     * in practice, it should be sufficient to use [nat]
     *)

    Parameter t : forall (k : Type) {_ : forall a b : k, Decidable (a = b)} (v : PCM), PCM.
    Parameter singleton : forall {k} {dec : forall a b : k, Decidable (a = b)} (v : PCM),
        k -> v.(p_type) -> (@t k dec v).(p_type).

  End fmap.
  Definition fmap := fmap.t.

  Module Invariants.
    (* notes:
     * - These can be encoded using ghost state.
     *)

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

    (* note(gmm): this is like the Iron++ logic. *)
    Parameter OPerm : Fp -> iname -> mpred.
    Parameter DPerm : Fp -> iname -> mpred.
    Axiom OPerm_split : forall (f1 f2 : Fp) n,
        OPerm (f1 ⊕ f2) n -|- OPerm f1 n ** OPerm f2 n.
    Axiom DPerm_split : forall (f1 f2 : Fp) n,
        DPerm (f1 ⊕ f2) n -|- DPerm f1 n ** DPerm f2 n.

    Axiom TInv_new : forall pkg I,
      I |-- Exists n : _,
            let n := namespace pkg n in
            TInv n I ** OPerm Fp.Fp_full n ** DPerm Fp.Fp_full n.
  End Invariants.
  Import Invariants.
  Export Invariants.

  Definition disjoint {T} (xs ys : list T) : Prop :=
    List.Forall (fun x => ~List.In x ys) xs.

  (* view shifts
   * - this is an entirely different notion of entailment because it enables
   *   updating ghost state.
   *)
  Module ViewShift.
    (* notes:
     * - these are modeled on Iris 1.0. In subsequent versions of Iris, this
     *   concept was implemented in terms of "fancy update".
     *   todo(gmm): investigate this as an alternative presentation.
     *)

    Variant Inv_type : Type :=
    | Affine
    | Tracked (_ : Fp).
    (* to make accurate tracking possible, we need to ensure that a trackable
     * invariant [ι] can not contain [OPerm 1 ι] because this would mean that
     * the invariant is invisible to the program.
     * to solve this problem, we track the fraction that the invariant was opened
     * with in the mask.
     * - when you open a trackable invariant, you lose your [OPerm q ι]
     * - when you close a trackable invariant, you get your [OPerm q ι] back.
     * - when you delete a trackable invariant, you get to use [OPerm q ι]
     *   to establish [OPerm 1 ι].
     *)

    Parameter shift : list (iname * Inv_type) -> list (iname * Inv_type) ->
                      mpred -> mpred -> mpred.
    (* ^ this definition is essentially:
     *   shift P Q |-- embed (FPU P Q)
     * except with respect to masks which can only be explained by going
     * a bit deeper into things.
     *)

    Axiom shift_id : empSP |-- shift nil nil empSP empSP.
    Axiom shift_frame : forall e1 e2 e' Q R S,
        disjoint (map fst e1) (map fst e') ->
        disjoint (map fst e2) (map fst e') ->
        shift e1 e2 Q R |-- shift (e1 ++ e') (e2 ++ e') (Q ** S) (R ** S).
    Axiom shift_trans : forall e1 e2 e3 Q R S,
        incl e2 (e1 ++ e3) ->
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
        |-- Forall q, shift nil ((i,Tracked q) :: nil) (OPerm q i -* OPerm Fp.Fp_full i ** DPerm Fp.Fp_full i) empSP.
    (* ^ note(gmm): the `q` permission was opened already, so you get that in
     * order to establish the final `OPerm 1`
     *)

    Axiom Proper_shift :
      Proper (@Permutation _ ++> @Permutation _ ++> lentails --> lentails ++> lentails)
             shift.
    Global Existing Instance Proper_shift.

    Lemma shift_conseq : forall e1 e2 P P' Q Q',
        P' |-- P ->
        Q |-- Q' ->
        shift e1 e2 P Q |-- shift e1 e2 P' Q'.
    Proof.
      intros * H1 H2.
      now rewrite H1, H2.
    Qed.

    (* this says that shifts are pure facts *)
    Axiom shift_pure : forall e1 e2 P Q, shift e1 e2 P Q |-- empSP.

    Axiom shift_lexists : forall e1 e2 T (P : T -> _) Q,
        shift e1 e2 (lexists P) Q -|- Forall x : T, shift e1 e2 (P x) Q.

  End ViewShift.
  Import ViewShift.

  Module GhostState.
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
    Parameter ghost_is : forall {Prm: PCM} (value : Prm), mpred.
    Axiom shift_ghost_is_bot : forall {Prm : PCM},
        |-- shift nil nil empSP (@ghost_is Prm p_bot).

    Definition ghost_loc : Type := nat.

    Definition ghost_ptsto (Prm : PCM) (p : ghost_loc) (value : Prm) : mpred :=
      ghost_is (fmap.singleton Prm p value).

    Opaque ghost_loc.

    Axiom shift_ghost_alloc : forall prm v,
        [| p_valid v |]
        |-- shift nil nil
                  empSP
                  (Exists p : ghost_loc, ghost_ptsto prm p v).

    Axiom shift_ghost_compose : forall prm (p : ghost_loc) v1 v2,
        ghost_ptsto prm p v1 ** ghost_ptsto prm p v2
        -|- ghost_ptsto prm p (p_compose v1 v2).

    (* note(gmm): i can update any ghost using frame preserving update
     *)
    Axiom shift_ghost_update : forall prm p v V',
        [| FPU v V' |]
        |-- shift nil nil (ghost_ptsto prm p v)
                          (Exists v', [| V' v' |] ** ghost_ptsto prm p v').

    Lemma shift_ghost_update_single : forall prm p v v',
        [| FPU_single v v' |]
        |-- shift nil nil
                  (ghost_ptsto prm p v)
                  (ghost_ptsto prm p v').
    Proof.
      intros.
      t.
      unfold FPU_single in *.
      rewrite <-shift_conseq; [ | reflexivity | ].
      1: rewrite <-shift_ghost_update; t.
      t.
      subst.
      reflexivity.
    Qed.
  End  GhostState.
  Export GhostState.

  (*Similarly one can encode ghost state using PCM*)
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
  Variable guard_container : list PCM.
  Axiom logical_ghost: forall (ghost : PCM) (guard : In ghost guard_container)  (gl : ghost) (gv : val), mpred.
*)

  (* Parameter wp_ghst : Expr -> (val -> mpred) -> mpred. *)

   (*
     {P} E {Q}
    ------------
    {P} E {Q * exists l. l:g} //ghost location l carries the ghost resource g
   *)

  (* a "weakest pre-condition" for view shifts
   *
   * [mask] is the invariants that are *open* now
   * [to] is the invariants that are *open* afterwards
   *
   * note(gmm): in this style, we don't need to explicitly quantify over the
   * final open invariants.
   *)
  Parameter wp_shift : forall (mask : list (iname * Inv_type)),
      (forall to : list (iname * Inv_type), mpred) -> mpred.

  Axiom wp_shift_done : forall Q mask,
      Q mask |-- wp_shift mask Q.

  Axiom wp_shift_vs : forall P from to Q,
    shift from to P Q
    |-- (* persistent *) Forall Z, ((P ** (Q -* wp_shift from Z)) -* wp_shift to Z).

  (* the next 5 theorems give rules for "primitive" view shifts and [wp_shift] *)
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
    t.
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
    t.
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
    t.
  Qed.
  Theorem wp_shift_closeT : forall (q : Fp) Q hide n I,
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
    t.
  Qed.
  Theorem wp_shift_deleteT : forall (q : Fp) Q hide n I,
      ~In n (map fst hide) ->
      TInv n I ** (OPerm q n -* OPerm Fp.Fp_full n ** DPerm Fp.Fp_full n) ** wp_shift hide Q
      |-- wp_shift ((n, Tracked q) :: hide) Q.
  Proof.
    intros.
    rewrite shift_deletet.
    erewrite lforall_specialize.
    erewrite shift_frame with (e':=hide) (S:=empSP).
    2:{ simpl. constructor. }
    2:{ subst. simpl. constructor; [ | constructor ]; auto. }
    simpl.
    rewrite wp_shift_vs.
    t.
  Qed.

  (* View shifts are sound as long as invariants are always re-established after
   * any atomic step. This means that it is sound to open invariants before
   * (and after) any evaluation provided that all of the invariants are
   * closed before any computation actually occurs.
   * We can express this generically through the following:
   *)
  Axiom shift_anywhere : forall P,
      wp_shift nil (fun to => [| to = nil |] ** P) |-- P.

  Definition wrap_shift (F : (val -> mpred) -> mpred) (Q : val -> mpred) : mpred :=
    wp_shift nil (fun to => F (fun result => wp_shift to (fun to => [| to = nil |] ** Q result))).


  (****** Wp Semantics for atomic operations
   * These are given in the style of function call axioms
   *)
  Parameter wp_atom : AtomicOp -> list val -> type -> (val -> mpred) -> mpred.

  (* note that this rule captures all of the interesting reasoning about atomics
   * through the use of [wp_shift]
   *)
  Monomorphic Axiom wp_rhs_atomic: forall rslv ti r ao es ty Q,
      wps (wpAnys (resolve:=rslv) ti r) es  (fun (vs : list val) (free : FreeTemps) =>
           wrap_shift (wp_atom ao vs ty) (fun v => Q v free)) empSP
      |-- wp_rhs (resolve:=rslv) ti r (Eatomic ao es ty) Q.

  (* Ideas adopted from the paper:
   * Relaxed Separation Logic: A program logic for C11 Concurrency -- Vefeiadis et al.
   *)

  (*Memory Ordering Patterns: Now we only have _SEQ_CST *)
  Definition _SEQ_CST := Vint 5.

  (* note(gmm): these are used for reading and writing values shared between
   * threads.
   * note(gmm): these look exactly like the standard read and write assertions
   * because all of the invariant reasoning is encapsulated in [wp_shift].
   *)
  Axiom wp_atom_load_cst
  : forall memorder (acc_type:type) (l : val) (Q : val -> mpred),
      [| memorder = _SEQ_CST |] **
      (Exists v, (_at (_eq l) (tprim acc_type v) ** ltrue //\\ Q v))
      |-- wp_atom AO__atomic_load_n (l :: memorder :: nil) acc_type Q.

  Axiom wp_atom_store_cst
  : forall memorder (acc_type:type) l Q val,
      [| memorder = _SEQ_CST |] **
      (Exists val, _at (_eq l) (tprim acc_type val)) **
      (_at (_eq l) (tprim acc_type val) -* Exists void, Q void)
      |-- wp_atom AO__atomic_store_n (l :: memorder :: val :: nil) (Qmut Tvoid) Q.

  (* atomic compare and exchange n *)
  Axiom wp_atom_compare_exchange_n:
    forall val_p expected_p desired wk succmemord failmemord Q'
           (ty : type)
           expected,
      ([|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
      Exists v,
         _at (_eq expected_p) (tprim ty expected) **
         _at (_eq val_p) (tprim ty v) **
         (([| v = expected |] -*
          _at (_eq expected_p) (tprim ty expected) **
          _at (_eq val_p) (tprim ty desired) -* Q' (Vbool true)) //\\
         ([| v <> expected |] -*
          _at (_eq expected_p) (tprim ty v) **
          _at (_eq val_p) (tprim ty v) -* Q' (Vbool false))))
       |-- wp_atom AO__atomic_compare_exchange_n
                   (val_p::succmemord::expected_p::failmemord::desired::wk::nil) (Qmut Tbool) Q'.
  (* ^ note(gmm): this states that *both pointers are read atomically*.
   *)

  (* atomic compare and exchange rule
   *)
  Axiom wp_atom_compare_exchange:
    forall P val_p expected_p desired_p wk succmemord failmemord Q
      (ty : type)
      expected desired,
         (_at (_eq expected_p) (tprim ty expected) **
         _at (_eq desired_p) (tprim ty desired) **
         Exists val, _at (_eq val_p) (tprim ty val) **
         [|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
         ((((* success *)
            [| val = expected |] **
            _at (_eq expected_p) (tprim ty expected) **
            _at (_eq desired_p) (tprim ty desired) **
            _at (_eq val_p) (tprim ty desired) -* Q (Vbool true))) //\\
          (((* failure *)
            [| val <> expected |] **
              _at (_eq expected_p) (tprim ty val) **
              _at (_eq desired_p) (tprim ty desired) **
              _at (_eq val_p) (tprim ty val) **
              P) -* Q (Vbool false))))
       |-- wp_atom AO__atomic_compare_exchange
                   (val_p::succmemord::expected_p::failmemord::desired::wk::nil) (Qmut Tbool) Q.

  (* atomic fetch and xxx rule *)
  Definition wp_fetch_xxx ao op : Prop :=
    forall E pls memorder Q (acc_type : type),
      [| memorder = _SEQ_CST |] **
         (Exists v,
          _at (_eq E) (tprim acc_type v) **
          Exists v', [| eval_binop op (drop_qualifiers acc_type) (drop_qualifiers acc_type) (drop_qualifiers acc_type) v pls v' |] **
                     (_at (_eq E) (tprim acc_type v') -* Q v))
      |-- wp_atom ao (E::memorder::pls::nil) acc_type Q.

(*
  Definition wp_fetch_xxx ao op : Prop :=
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
*)

  Ltac fetch_xxx ao op :=
    let G := eval unfold wp_fetch_xxx in (wp_fetch_xxx ao op) in exact G.

  Axiom wp_atom_fetch_add : ltac:(fetch_xxx AO__atomic_fetch_add Badd).
  Axiom wp_atom_fetch_sub : ltac:(fetch_xxx AO__atomic_fetch_sub Bsub).
  Axiom wp_atom_fetch_and : ltac:(fetch_xxx AO__atomic_fetch_and Band).
  Axiom wp_atom_fetch_xor : ltac:(fetch_xxx AO__atomic_fetch_xor Bxor).
  Axiom wp_atom_fetch_or  : ltac:(fetch_xxx AO__atomic_fetch_or  Bor).

  (* atomic xxx and fetch rule *)
  Definition wp_xxx_fetch ao op : Prop :=
    forall E pls memorder Q (acc_type : type),
      [| memorder = _SEQ_CST |] **
         (Exists v,
          _at (_eq E) (tprim acc_type v) **
          Exists v', [| eval_binop op (drop_qualifiers acc_type) (drop_qualifiers acc_type) (drop_qualifiers acc_type) v pls v' |] **
                     (_at (_eq E) (tprim acc_type v') -* Q v'))
      |-- wp_atom ao (E::memorder::pls::nil) acc_type Q.

(*
  Definition wp_xxx_fetch ao op : Prop :=
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
*)

  Ltac xxx_fetch ao op :=
    let G := eval unfold wp_xxx_fetch in (wp_xxx_fetch ao op) in exact G.

  Axiom wp_atom_add_fetch : ltac:(xxx_fetch AO__atomic_add_fetch Badd).
  Axiom wp_atom_sub_fetch : ltac:(xxx_fetch AO__atomic_sub_fetch Bsub).
  Axiom wp_atom_and_fetch : ltac:(xxx_fetch AO__atomic_and_fetch Band).
  Axiom wp_atom_xor_fetch : ltac:(xxx_fetch AO__atomic_xor_fetch Bxor).
  Axiom wp_atom_or_fetch  : ltac:(xxx_fetch AO__atomic_or_fetch  Bor).

End cclogic.

Declare Module CCL : cclogic.

Export CCL.

Global Opaque p_compose p_valid p_bot.
