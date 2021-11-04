(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
 * Definitions for the semantics
 *)
Require Import bedrock.prelude.base.

Require Import stdpp.coPset.
Require Import iris.bi.monpred.
From iris.proofmode Require Import tactics classes.

From bedrock.lang.cpp Require Import
     ast semantics logic.pred.

Set Primitive Projections.

(* expression continuations
 * - in full C++, this includes exceptions, but our current semantics
 *   doesn't treat those.
 *)
Definition epred `{Σ : cpp_logic thread_info} := mpred.
Notation epredO := mpredO (only parsing).

Module FreeTemps.
Section FreeTemps.
  Context `{Σ : cpp_logic thread_info}.

  Inductive t : Type :=
  | id (* = fun x => x *)
  | delete (ty : type) (p : ptr) (* = delete_val ty p  *)
  | seq (f g : t) (* = fun x => f $ g x *)
  | par (f g : t)
    (* = fun x => Exists Qf Qg, f Qf ** g Qg ** (Qf -* Qg -* x)
     *)
  .

  Inductive t_eq : t -> t -> Prop :=
  | refl l : t_eq l l
  | sym l r : t_eq l r -> t_eq r l
  | trans a b c : t_eq a b -> t_eq b c -> t_eq a c

  | seqA x y z : t_eq (seq x (seq y z)) (seq (seq x y) z)
  | seq_id_unitR l : t_eq (seq l id) l
  | seq_id_unitL l : t_eq (seq id l) l

  | parC r l : t_eq (par l r) (par r l)
  | parA x y z : t_eq (par x (par y z)) (par (par x y) z)
  | par_id_unitR l : t_eq (par l id) l
  | par_id_unitL l : t_eq (par id l) l.

  #[global] Instance t_Equiv : Equiv t := t_eq.

  #[global] Instance t_Equivalence : Equivalence (@equiv t _).
  Proof.
    constructor.
    - red; eapply refl.
    - red; eapply sym.
    - red; eapply trans.
  Qed.

  #[global] Instance : Assoc equiv seq.
  Proof. red; apply seqA. Qed.
  #[global] Instance : LeftId equiv id seq.
  Proof. red; apply seq_id_unitL. Qed.
  #[global] Instance : RightId equiv id seq.
  Proof. red; apply seq_id_unitR. Qed.

  #[global] Instance : Comm equiv par.
  Proof. red; intros; apply parC. Qed.
  #[global] Instance : Assoc equiv par.
  Proof. red; apply parA. Qed.
  #[global] Instance : LeftId equiv id par.
  Proof. red; apply par_id_unitL. Qed.
  #[global] Instance : RightId equiv id par.
  Proof. red; apply par_id_unitR. Qed.

  (** [pars ls] is the [FreeTemp] representing the destruction
      of each element in [ls] *in non-deterministic order*.
   *)
  Definition pars : list t -> t := fold_right FreeTemps.par FreeTemps.id.

  (** [seqs ls] is the [FreeTemp] representing the destruction
      of each element in [ls] sequentially from left-to-right, i.e.
      the first element in the list is run first.
   *)
  Definition seqs : list t -> t := fold_right FreeTemps.seq FreeTemps.id.

  (** [seqsR ls] is the [FreeTemp] representing the destruction
      of each element in [ls] sequentially from right-to-left, i.e.
      the first element in the list is destructed last.
   *)
  Definition seqsR : list t -> t := foldl (fun a b => FreeTemps.seq b a) FreeTemps.id.

End FreeTemps.
End FreeTemps.
Notation FreeTemps := FreeTemps.t.
Notation FreeTemp := FreeTemps.t (only parsing).

(* Notations *)
Declare Scope free_scope.
Delimit Scope free_scope with free.
Infix "|*|" := FreeTemps.par (at level 30) : free_scope.
Infix ">*>" := FreeTemps.seq (at level 30) : free_scope.
Bind Scope free_scope with FreeTemps.t.

(* continuations
 * C++ statements can terminate in 4 ways.
 *
 * note(gmm): technically, they can also raise exceptions; however,
 * our current semantics doesn't capture this. if we want to support
 * exceptions, we should be able to add another case,
 * `k_throw : val -> mpred`.
 *)
Variant ReturnType : Set :=
| Normal
| Break
| Continue
| ReturnVal (_ : val)
| ReturnVoid
.

Definition rt_biIndex : biIndex :=
  {| bi_index_type := ReturnType
   ; bi_index_inhabited := populate Normal
   ; bi_index_rel := @eq ReturnType
   ; bi_index_rel_preorder := _ |}.

Section Kpred.
  Context `{Σ : cpp_logic thread_info}.

  Definition KpredI : bi := monPredI rt_biIndex mpredI.
  #[local] Notation Kpred := KpredI.
  Definition KP (P : _) : KpredI := @MonPred rt_biIndex _ P _.
  Arguments KP _%I.

  Instance Kpred_fupd: FUpd KpredI :=
    funI l r Q => KP (fun v => |={l,r}=> Q v).

  Definition void_return (P : mpred) : KpredI :=
    KP (funI rt =>
          match rt with
          | Normal | ReturnVoid => P
          | _ => False
          end).

  Definition val_return (P : val -> mpred) : KpredI :=
    KP (funI rt =>
        match rt with
        | ReturnVal v => P v
        | _ => False
        end).

  Definition Kseq (Q : Kpred -> mpred) (k : Kpred) : Kpred :=
    KP (funI rt =>
        match rt with
        | Normal => Q k
        | rt => k rt
        end).

  (* loop with invariant `I` *)
  Definition Kloop (I : mpred) (Q : Kpred) : Kpred :=
    KP (funI rt =>
        match rt with
        | Break | Normal => Q Normal
        | Continue => I
        | rt => Q rt
        end).

  Definition Kat_exit (Q : mpred -> mpred) (k : Kpred) : Kpred :=
    KP (funI rt => Q (k rt)).

  Theorem Kat_exit_frame Q Q' (k k' : KpredI) :
    Forall x y, (x -* y) -* Q x -* Q' y |-- Forall rt, (k rt -* k' rt) -* Kat_exit Q k rt -* Kat_exit Q' k' rt.
  Proof.
    rewrite /Kat_exit. iIntros "A" (?) "B" =>/=. iApply "A"; iApply "B".
  Qed.

  #[global] Instance mpred_Kpred_BiEmbed : BiEmbed mpredI KpredI := _.

  (* NOTE KpredI does not embed into mpredI because it doesn't respect
     existentials.
   *)
End Kpred.
#[global] Notation Kpred := (bi_car KpredI).
#[global,deprecated(since="2021-02-15",note="use KpredI")] Notation KpredsI := KpredI (only parsing).
#[global,deprecated(since="2021-02-15",note="use Kpred")] Notation Kpreds := Kpred (only parsing).

(** * Regions
    To model the stack frame in separation logic, we use a notion of regions
    that are threaded through the semantics.

    We instantiate [region] as a finite map from variables to their addresses
    (implemented as an association list).
*)
Inductive region : Type :=
| Remp (this : option ptr) (_ : type)
| Rbind (_ : localname) (_ : ptr) (_ : region).

Definition Rbind_check (x : ident) (p : ptr) (r : region) : region :=
  if decide (x = ""%bs)
  then r
  else Rbind x p r.

Fixpoint get_location (ρ : region) (b : localname) : option ptr :=
  match ρ with
  | Remp _ _ => None
  | Rbind x p rs =>
    if decide (b = x) then Some p
    else get_location rs b
  end.

Fixpoint get_this (ρ : region) : option ptr :=
  match ρ with
  | Remp this _ => this
  | Rbind _ _ rs => get_this rs
  end.

Fixpoint get_return_type (ρ : region) : type :=
  match ρ with
  | Remp _ ty => ty
  | Rbind _ _ rs => get_return_type rs
  end.

(** [_local ρ b] returns the [ptr] that stores the local variable [b].
 *)
Definition _local (ρ : region) (b : ident) : ptr :=
  match get_location ρ b with
  | Some p => p
  | _ => invalid_ptr
  end.
Arguments _local !_ !_ / : simpl nomatch, assert.

(** [_this ρ] returns the [ptr] that [this] is bound to.

    NOTE because [this] is [const], we actually store the value directly
    rather than indirectly representing it in memory.
 *)
Definition _this (ρ : region) : ptr :=
  match get_this ρ with
  | Some p => p
  | _ => invalid_ptr
  end.
Arguments _this !_ / : assert.

Module WPE.
Section with_cpp.
  Context `{Σ : cpp_logic thread_info}.

  (* The expressions in the C++ language are categorized into five
   * "value categories" as defined in:
   *    http://eel.is/c++draft/expr.prop#basic.lval-1
   *
   * - "A glvalue is an expression whose evaluation determines the identity of
   *    an object or function."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.1
   * - "A prvalue is an expression whose evaluation initializes an object or
   *    computes the value of an operand of an operator, as specified by the
   *    context in which it appears, or an expression that has type cv void."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.2
   * - "An xvalue is a glvalue that denotes an object whose resources can be
   *    reused (usually because it is near the end of its lifetime)."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.3
   * - "An lvalue is a glvalue that is not an xvalue."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.4
   * - "An rvalue is a prvalue or an xvalue."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.5
   *)

  (** lvalues *)
  (* [wp_lval σ E ρ e Q] evaluates the expression [e] in region [ρ]
   * with mask [E] and continutation [Q].
   *)
  Parameter wp_lval
    : forall {resolve:genv}, coPset -> region ->
        Expr ->
        (ptr -> FreeTemps -> epred) -> (* result -> free -> post *)
        mpred. (* pre-condition *)

  Axiom wp_lval_shift : forall σ M ρ e Q,
      (|={M}=> wp_lval (resolve:=σ) M ρ e (fun v free => |={M}=> Q v free))
    ⊢ wp_lval (resolve:=σ) M ρ e Q.

  Axiom wp_lval_frame :
    forall σ1 σ2 M ρ e k1 k2,
      genv_leq σ1 σ2 ->
      Forall v f, k1 v f -* k2 v f |-- @wp_lval σ1 M ρ e k1 -* @wp_lval σ2 M ρ e k2.
  #[global] Instance Proper_wp_lval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_lval).
  Proof.
    repeat red. intros; subst.
    iIntros "X". iRevert "X".
    iApply wp_lval_frame; eauto.
    iIntros (v). iIntros (f). iApply H3.
  Qed.

  Section wp_lval.
    Context {σ : genv} (M : coPset) (ρ : region) (e : Expr).
    Local Notation WP := (wp_lval M ρ e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : ptr → FreeTemps → epred.

    Lemma wp_lval_wand Q1 Q2 : WP Q1 |-- (∀ v f, Q1 v f -* Q2 v f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_lval_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_lval Q : (|={M}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_lval_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_lval_wand with "Hwp"). auto.
    Qed.
    Lemma wp_lval_fupd Q : WP (λ v f, |={M}=> Q v f) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_lval_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_lval p P Q :
      ElimModal True p false (|={M}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_lval.
    Qed.
    #[global] Instance elim_modal_bupd_wp_lval p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp_lval.
    Qed.
    #[global] Instance add_modal_fupd_wp_lval P Q : AddModal (|={M}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_lval.
    Qed.
  End wp_lval.

  (** * prvalue *)
  (*
   * there are two distinct weakest pre-conditions for this corresponding to the
   * standard text:
   * "A prvalue is an expression whose evaluation...
   * 1. initializes an object, or
   * 2. computes the value of an operand of an operator,
   * as specified by the context in which it appears,..."
   *)

  (* evaluate a prvalue that "initializes an object".
     The memory that is being initialized is already owned by the C++ abstract machine.
     Therefore, schematically, a [wp_init ty addr e Q] looks like the following:
       [[
          addr |-> R ... 1 -* Q
       ]]
     This choice means that a thread needs to give up the memory to the abstract
     machine when it transitions to running a [wp_init]. In the case of
     stack allocation, there is nothing to do here, but in the case of [new],
     the memory must be given up.

     Note: <https://eel.is/c++draft/dcl.init#general-15>:
     | (15) The initialization that occurs
     | (15.1) for an initializer that is a parenthesized expression-list or a braced-init-list,
     | (15.2) for a new-initializer ([expr.new]),
     | (15.3) in a static_­cast expression ([expr.static.cast]),
     | (15.4) in a functional notation type conversion ([expr.type.conv]), and
     | (15.5) in the braced-init-list form of a condition
     | is called direct-initialization.
     and [wp_init] corresponds to [direct-initialization] as described above.
   *)
  Parameter wp_init
    : forall {resolve:genv}, coPset -> region ->
                        type -> ptr -> Expr ->
                        (FreeTemps -> epred) -> (* free -> post *)
                        mpred. (* pre-condition *)

  Axiom wp_init_shift : forall σ M ρ ty v e Q,
      (|={M}=> wp_init (resolve:=σ) M ρ ty v e (fun free => |={M}=> Q free))
    ⊢ wp_init (resolve:=σ) M ρ ty v e Q.

  Axiom wp_init_frame :
    forall σ1 σ2 M ρ t v e k1 k2,
      genv_leq σ1 σ2 ->
      Forall f, k1 f -* k2 f |-- @wp_init σ1 M ρ t v e k1 -* @wp_init σ2 M ρ t v e k2.

  #[global] Instance Proper_wp_init :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ lentails ==> lentails)
           (@wp_init).
  Proof.
    repeat red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wp_init_frame; eauto.
    iIntros (f); iApply H5.
  Qed.

  Section wp_init.
    Context {σ : genv} (M : coPset) (ρ : region)
      (t : type) (p : ptr) (e : Expr).
    Local Notation WP := (wp_init M ρ t p e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : FreeTemps → epred.

    Lemma wp_init_wand Q1 Q2 : WP Q1 |-- (∀ f, Q1 f -* Q2 f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_init_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_init Q : (|={M}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_init_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_init_wand with "Hwp"). auto.
    Qed.
    Lemma wp_init_fupd Q : WP (λ f, |={M}=> Q f) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_init_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_init q P Q :
      ElimModal True q false (|={M}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_init.
    Qed.
    #[global] Instance elim_modal_bupd_wp_init q P Q :
      ElimModal True q false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp_init.
    Qed.
    #[global] Instance add_modal_fupd_wp_init P Q : AddModal (|={M}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_init.
    Qed.
  End wp_init.

  (* evaluate a prvalue that "computes the value of an operand of an operator"
   *)
  Parameter wp_prval
    : forall {resolve:genv}, coPset -> region ->
        Expr ->
        (val -> FreeTemps -> epred) -> (* result -> free -> post *)
        (* ^^ TODO the biggest question is what does this [val] represent
         *)
        mpred. (* pre-condition *)

  Axiom wp_prval_shift : forall σ M ρ e Q,
      (|={M}=> wp_prval (resolve:=σ) M ρ e (fun v free => |={M}=> Q v free))
    ⊢ wp_prval (resolve:=σ) M ρ e Q.

  Axiom wp_prval_frame :
    forall σ1 σ2 M ρ e k1 k2,
      genv_leq σ1 σ2 ->
      Forall v f, k1 v f -* k2 v f |-- @wp_prval σ1 M ρ e k1 -* @wp_prval σ2 M ρ e k2.

  #[global] Instance Proper_wp_prval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_prval).
  Proof. repeat red; intros; subst.
         iIntros "X"; iRevert "X".
         iApply wp_prval_frame; eauto.
         iIntros (v); iIntros (f); iApply H3.
  Qed.

  Section wp_prval.
    Context {σ : genv} (M : coPset) (ρ : region) (e : Expr).
    Local Notation WP := (wp_prval M ρ e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : val → FreeTemps → epred.

    Lemma wp_prval_wand Q1 Q2 : WP Q1 |-- (∀ v f, Q1 v f -* Q2 v f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_prval_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_prval Q : (|={M}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_prval_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_prval_wand with "Hwp"). auto.
    Qed.
    Lemma wp_prval_fupd Q : WP (λ v f, |={M}=> Q v f) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_prval_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_prval p P Q :
      ElimModal True p false (|={M}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_prval.
    Qed.
    #[global] Instance elim_modal_bupd_wp_prval p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp_prval.
    Qed.
    #[global] Instance add_modal_fupd_wp_prval P Q : AddModal (|={M}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_prval.
    Qed.
  End wp_prval.

  (** * xvalues *)

  (* evaluate an expression as an xvalue *)
  Parameter wp_xval
    : forall {resolve:genv}, coPset -> region ->
                        Expr ->
                        (ptr -> FreeTemps -> epred) -> (* result -> free -> post *)
                        mpred. (* pre-condition *)

  Axiom wp_xval_shift : forall σ M ρ e Q,
      (|={M}=> wp_xval (resolve:=σ) M ρ e (fun v free => |={M}=> Q v free))
    ⊢ wp_xval (resolve:=σ) M ρ e Q.

  Axiom wp_xval_frame :
    forall σ1 σ2 M ρ e k1 k2,
      genv_leq σ1 σ2 ->
      Forall v f, k1 v f -* k2 v f |-- @wp_xval σ1 M ρ e k1 -* @wp_xval σ2 M ρ e k2.
  #[global] Instance Proper_wp_xval :
    Proper (genv_leq ==> eq ==> eq ==> eq ==>
            pointwise_relation _ (pointwise_relation _ lentails) ==> lentails)
           (@wp_xval).
  Proof. repeat red; intros; subst.
         iIntros "X"; iRevert "X".
         iApply wp_xval_frame; eauto.
         iIntros (v); iIntros (f); iApply H3.
  Qed.

  Section wp_xval.
    Context {σ : genv} (M : coPset) (ρ : region) (e : Expr).
    Local Notation WP := (wp_xval M ρ e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : ptr → FreeTemps → epred.

    Lemma wp_xval_wand Q1 Q2 : WP Q1 |-- (∀ v f, Q1 v f -* Q2 v f) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_xval_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_xval Q : (|={M}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_xval_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_xval_wand with "Hwp"). auto.
    Qed.
    Lemma wp_xval_fupd Q : WP (λ v f, |={M}=> Q v f) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_xval_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_xval p P Q :
      ElimModal True p false (|={M}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_xval.
    Qed.
    #[global] Instance elim_modal_bupd_wp_xval p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp_xval.
    Qed.
    #[global] Instance add_modal_fupd_wp_xval P Q : AddModal (|={M}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_xval.
    Qed.
  End wp_xval.

  (* Opaque wrapper of [False]: this represents a [False] obtained by a [ValCat] mismatch in [wp_glval]. *)
  Definition wp_glval_mismatch {resolve : genv} (M : coPset) (r : region) (vc : ValCat) (e : Expr) : (ptr -> FreeTemps -> mpred) -> mpred := funI _ => False.
  #[global] Arguments wp_glval_mismatch : simpl never.

  (* evaluate an expression as a generalized lvalue *)

  (* in some cases we need to evaluate a glvalue but we know the
     the underlying primitive value category. This makes some weakest
     pre-condition axioms a bit shorter
   *)
  Definition wp_glval {resolve} M r (vc : ValCat) (e : Expr) : (ptr -> FreeTemps -> mpred) -> mpred :=
      match vc with
      | Lvalue => wp_lval (resolve:=resolve) M r e
      | Xvalue => wp_xval (resolve:=resolve) M r e
      | _ => wp_glval_mismatch M r vc e
      end%I.

  Theorem wp_glval_frame {resolve : genv} M r vc e Q Q' :
    (Forall v free, Q v free -* Q' v free) |-- wp_glval M r vc e Q -* wp_glval M r vc e Q'.
  Proof.
    destruct vc; simpl.
    - apply wp_lval_frame; reflexivity.
    - eauto.
    - apply wp_xval_frame; reflexivity.
  Qed.

  Theorem wp_glval_wand {resolve : genv} M r vc e Q Q' :
    wp_glval M r vc e Q |-- (Forall v free, Q v free -* Q' v free) -* wp_glval M r vc e Q'.
  Proof.
    iIntros "A B"; iRevert "A"; iApply wp_glval_frame; eauto.
  Qed.

  (** Bundled evaluation, this enables us slightly more concisely
      represent some weakest-precondition rules.
   *)
  Section wpe.
    Context {resolve:genv}.
    Variable (M : coPset) (ρ : region).

    Definition wpe (vc : ValCat) (e : Expr) (Q :val -> FreeTemps -> mpred) : mpred :=
      match vc with
      | Lvalue => @wp_lval resolve M ρ e (fun p => Q (Vptr p))
      | Prvalue => @wp_prval resolve M ρ e Q
      | Xvalue => @wp_xval resolve M ρ e (fun p => Q (Vptr p))
      end.

    Definition wpAny (vce : ValCat * Expr)
      : (val -> FreeTemps -> mpred) -> mpred :=
      let '(vc,e) := vce in
      wpe vc e.

    Definition wpAnys := fun ve Q free => wpAny ve (fun v f => Q v (f >*> free)%free).
  End wpe.

  Lemma wpe_frame σ1 σ2 M ρ vc e k1 k2:
    genv_leq σ1 σ2 ->
    Forall v f, k1 v f -* k2 v f |-- wpe (resolve := σ1) M ρ vc e k1 -* wpe (resolve:=σ2) M ρ vc e k2.
  Proof.
    destruct vc => /=; [ | apply wp_prval_frame | ].
    - intros. rewrite -wp_lval_frame; eauto.
      iIntros "h" (v f) "x"; iApply "h"; iFrame.
    - intros. rewrite -wp_xval_frame; eauto.
      iIntros "h" (v f) "x"; iApply "h"; iFrame.
  Qed.

  #[global] Instance Proper_wpe :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> (eq ==> (≡) ==> (⊢)) ==> (⊢))
           (@wpe).
  Proof.
    repeat red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wpe_frame; eauto.
    iIntros (v f); iApply H4; reflexivity.
  Qed.

  #[global] Instance Proper_wpe' :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> eq ==> (pointwise_relation _ (pointwise_relation _ lentails)) ==> lentails)
           (@wpe).
  Proof.
    repeat red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wpe_frame; eauto.
    iIntros (v f); iApply H4; reflexivity.
  Qed.

  Lemma wpAny_frame σ1 σ2 M ρ e k1 k2:
    genv_leq σ1 σ2 ->
    Forall v f, k1 v f -* k2 v f |-- wpAny (resolve := σ1) M ρ e k1 -* wpAny (resolve:=σ2) M ρ e k2.
  Proof. destruct e; apply: wpe_frame. Qed.

  #[global] Instance Proper_wpAny :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> (eq ==> (≡) ==> (⊢)) ==> (⊢))
           (@wpAny).
  Proof.
    repeat red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wpAny_frame; eauto.
    iIntros (v f); iApply H3; reflexivity.
  Qed.

  #[global] Instance Proper_wpAny' :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> (pointwise_relation _ (pointwise_relation _ lentails)) ==> lentails)
           (@wpAny).
  Proof.
    repeat red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wpAny_frame; eauto.
    iIntros (v f); iApply H3; reflexivity.
  Qed.

  (** * Statements *)

  (* evaluate a statement *)
  Parameter wp
    : forall {resolve:genv}, coPset -> region -> Stmt -> KpredI -> mpred.

  Axiom wp_shift : forall σ M ρ s Q,
      (|={M}=> wp (resolve:=σ) M ρ s (|={M}=> Q))
    ⊢ wp (resolve:=σ) M ρ s Q.

  Axiom wp_frame :
    forall σ1 σ2 M ρ s (k1 k2 : KpredI),
      genv_leq σ1 σ2 ->
      (Forall rt, k1 rt -* k2 rt) |-- @wp σ1 M ρ s k1 -* @wp σ2 M ρ s k2.

  #[global] Instance Proper_wp :
    Proper (genv_leq ==> eq ==> eq ==> eq ==> (⊢) ==> (⊢))
           (@wp).
  Proof.
    repeat red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wp_frame; eauto.
    by iIntros (rt); iApply monPred_in_entails.
  Qed.

  Section wp.
    Context {σ : genv} (M : coPset) (ρ : region) (s : Stmt).
    Local Notation WP := (wp M ρ s) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : KpredI.

    Lemma wp_wand (k1 k2 : KpredI) :
      WP k1 |-- (Forall rt, k1 rt -* k2 rt) -* WP k2.
    Proof.
      iIntros "Hwp Hk". by iApply (wp_frame σ _ _ _ _ k1 with "[$Hk] Hwp").
    Qed.
    Lemma fupd_wp k : (|={M}=> WP k) |-- WP k.
    Proof.
      rewrite -{2}wp_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_wand with "Hwp").
      iIntros (?) "X". iModIntro; eauto.
    Qed.
    Lemma wp_fupd k : WP (|={M}=> k) |-- WP k.
    Proof. iIntros "Hwp". by iApply (wp_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp p P k :
      ElimModal True p false (|={M}=> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp.
    Qed.
    #[global] Instance elim_modal_bupd_wp p P k :
      ElimModal True p false (|==> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal (bupd_fupd M). exact: elim_modal_fupd_wp.
    Qed.
    #[global] Instance add_modal_fupd_wp P k : AddModal (|={M}=> P) P (WP k).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp.
    Qed.
  End wp.

  (* this is the low-level specification of C++ code blocks.
   *
   * [addr] represents the address of the entry point of the code.
   * note: the [list val] will be related to the register set.
   *)
  Parameter fspec
    : forall (tt : type_table) (fun_type : type)
        (addr : val) (ls : list val) (Q : val -> epred), mpred.

  Axiom fspec_complete_type : forall te ft a ls Q,
      fspec te ft a ls Q
      |-- fspec te ft a ls Q **
          [| exists cc tret targs, ft = Tfunction (cc:=cc) tret targs |].

  (* this axiom states that the type environment for an [fspec] can be
     narrowed as long as the new type environment [small]/[tt2] is smaller than
     the old type environment ([big]/[tt1]), and [ft]
     is still a *complete type* in the new type environment [small]/[tt2].

     NOTE: This is informally justified by the fact that (in the absence
     of ODR) the implementation of the function is encapsulated and only
     the public interface (the type) is need to know how to call the function.
   *)
  Axiom fspec_strengthen : forall tt1 tt2 ft a ls Q,
      complete_type tt2.(globals) ft ->
      (* TODO(PG): even if [ft] is complete, the argument/return types might not be
      complete. That would make a call impossible, but does might not be
      enough to justify [fspec_strengthen] locally (tho I expect it suffices globally). *)
      sub_module tt2 tt1 ->
      fspec tt1.(globals) ft a ls Q |-- fspec tt2.(globals) ft a ls Q.

  (* this axiom is the standard rule of consequence for weakest
     pre-condition.
   *)
  Axiom fspec_frame : forall tt ft a ls Q1 Q2,
      Forall v, Q1 v -* Q2 v |-- @fspec tt ft a ls Q1 -* @fspec tt ft a ls Q2.

  #[global] Instance Proper_fspec : forall tt ft a ls,
      Proper (pointwise_relation _ lentails ==> lentails) (@fspec tt ft a ls).
  Proof. repeat red; intros.
         rewrite fspec_complete_type.
         iIntros "[X %]"; iRevert "X"; iApply fspec_frame; auto.
         iIntros (v); iApply H.
  Qed.

  Section fspec.
    Context {tt : type_table} {tf : type} (addr : val) (ls : list val).
    Local Notation WP := (fspec tt tf addr ls) (only parsing).
    Implicit Types Q : val → epred.

    Lemma fspec_wand Q1 Q2 : WP Q1 |-- (∀ v, Q1 v -* Q2 v) -* WP Q2.
    Proof. iIntros "Hwp HK".
           iDestruct (fspec_complete_type with "Hwp") as "[Hwp %]".
           iApply (fspec_frame with "HK Hwp").
    Qed.
  End fspec.

  (** [mspec tt this_ty fty ..] is the analogue of [fspec] for member functions.

      NOTE this includes constructors and destructors.

      NOTE the current implementation desugars this to [fspec] but this is not
           accurate according to the standard because a member function can not
           be cast to a regular function that takes an extra parameter.
           We could fix this by splitting [fspec] more, but we are deferring that
           for now.

           In practice we assume that the AST is well-typed, so the only way to
           exploit this is to use [reinterpret_cast< >] to cast a function pointer
           to an member pointer or vice versa.
   *)
  Definition mspec (tt : type_table) (this_type : type) (fun_type : type)
    : val -> list val -> (val -> epred) -> mpred :=
    fspec tt (Tmember_func this_type fun_type).

  Lemma mspec_frame:
    ∀ (t : type) (l : list val) (v : val) (t0 : type) (t1 : type_table) (Q Q' : val -> _),
      Forall v, Q v -* Q' v |-- mspec t1 t t0 v l Q -* mspec t1 t t0 v l Q'.
  Proof. intros; apply fspec_frame. Qed.

End with_cpp.
End WPE.

Export WPE.
Export stdpp.coPset.
