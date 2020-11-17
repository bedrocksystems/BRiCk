(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import stdpp.fin_maps.
From bedrock.lang.prelude Require Import base avl.
Require Import bedrock.lang.cpp.syntax.translation_unit.
Require Import bedrock.lang.cpp.ast.
Require Import ExtLib.Tactics.

Definition require_eq `{EqDecision T} (a b : T) {U} (r : option U) : option U :=
  if decide (a = b) then r else None.

Lemma require_eq_refl `{EqDecision T} : forall (a : T){U} (X : option U), require_eq a a X = X.
Proof.
  unfold require_eq. intros.
  destruct (decide (a = a)); auto.
  exfalso; auto.
Qed.

Lemma require_eq_success `{EqDecision T} {U} {a b : T} {c} {d : U}:
    require_eq a b c = Some d ->
    a = b /\ c = Some d.
Proof. unfold require_eq. by case_decide. Qed.

Definition ObjValue_le (a b : ObjValue) : option unit :=
  match a , b with
  | Ovar t oe , Ovar t' oe' =>
    require_eq t t' $
    match oe , oe' with
    | None , _ => Some tt
    | Some l , Some r => require_eq l r $ Some tt
    | _ , _ => None
    end
  | Ofunction f , Ofunction f' =>
    require_eq (normalize_type f.(f_return)) (normalize_type f'.(f_return)) $
    require_eq (List.map (fun '(_,b) => normalize_type b) f.(f_params))
               (List.map (fun '(_,b) => normalize_type b) f'.(f_params)) $
    match f.(f_body) , f'.(f_body) with
    | None , _ => Some tt
    | Some b , Some b' =>
      require_eq b b' $
      require_eq (List.map (fun '(a,b) => (a,normalize_type b)) f.(f_params))
                 (List.map (fun '(a,b) => (a,normalize_type b)) f'.(f_params)) $
      Some tt
    | _ , None => None
    end
  | Omethod m , Omethod m' =>
    require_eq m.(m_class) m'.(m_class) $
    require_eq m.(m_this_qual) m'.(m_this_qual) $
    require_eq (normalize_type m.(m_return)) (normalize_type m'.(m_return)) $
    require_eq (List.map (fun '(_,b) => normalize_type b) m.(m_params))
               (List.map (fun '(_,b) => normalize_type b) m'.(m_params)) $
    match m.(m_body) , m'.(m_body) with
    | None , _ => Some tt
    | Some b , Some b' =>
      require_eq (List.map (fun '(a,b) => (a,normalize_type b)) m.(m_params))
                 (List.map (fun '(a,b) => (a,normalize_type b)) m'.(m_params)) $
      require_eq b b' $
      Some tt
    | _ , None => None
    end
  | Oconstructor c , Oconstructor c' =>
    require_eq c.(c_class) c'.(c_class) $

    require_eq (List.map (fun x => normalize_type (snd x)) c.(c_params))
               (List.map (fun x => normalize_type (snd x)) c'.(c_params)) $
    match c.(c_body) , c'.(c_body) with
    | None , _ => Some tt
    | _ , None => None
    | Some x , Some y =>
    require_eq (List.map (fun '(a,b) => (a,normalize_type b)) c.(c_params))
               (List.map (fun '(a,b) => (a,normalize_type b)) c'.(c_params)) $
      require_eq x y $ Some tt
    end
  | Odestructor dd , Odestructor dd' =>
    require_eq dd.(d_class) dd'.(d_class) $
    match dd.(d_body) , dd'.(d_body) with
    | None , _ => Some tt
    | _ , None => None
    | Some x , Some y =>
      require_eq x y $ Some tt
    end
  | _ , _ => None
  end.
Definition ObjValue_ler : relation ObjValue := λ g1 g2, ObjValue_le g1 g2 = Some ().
Arguments ObjValue_ler !_ _ /.

Definition GlobDecl_le (a b : GlobDecl) : option unit :=
  match a , b with
  | Gtype , Gtype
  | Gtype , Gunion _
  | Gtype , Gstruct _ => Some tt
  | Gunion _ , Gtype
  | Gstruct _ , Gtype => None
  | Gunion u , Gunion u' =>
    require_eq u u' $
    Some tt
  | Gstruct s , Gstruct s' =>
    require_eq s s' $
    Some tt
  | Genum e _ , Genum e' _ =>
    require_eq e e' $
    Some tt
  | Gconstant t (Some e) , Gconstant t' (Some e') =>
    require_eq t t' $
    require_eq e e' $
    Some tt
  | Gconstant t (Some _) , Gconstant t' None => None
  | Gconstant t None , Gconstant t' (Some e') =>
    require_eq t t' $
    Some tt
  | Gconstant t None , Gconstant t' None =>
    require_eq t t' $
    Some tt
  | Gtypedef t , Gtypedef t' =>
    require_eq t t' $
    Some tt
  | _ , _ => None
  end.
Definition GlobDecl_ler : relation GlobDecl := λ g1 g2, GlobDecl_le g1 g2 = Some ().
Arguments GlobDecl_ler !_ _ /.

Section GlobDecl_ler.
  Local Instance GlobDecl_le_refl : Reflexive GlobDecl_ler.
  Proof.
    intros []; rewrite /= ?require_eq_refl; eauto.
    destruct o => //.
    by rewrite !require_eq_refl.
  Qed.

  Local Instance GlobDecl_le_trans : Transitive GlobDecl_ler.
  Proof.
    intros a b c.
    destruct a, b; simpl => //; destruct c; simpl => //; intros;
      repeat (match goal with
              | H : require_eq _ _ _ = _ |- _ =>
                  eapply require_eq_success in H; destruct H; subst
              | H : context [ match ?X with _ => _ end ] |- _ =>
                lazymatch X with
                | context [ match _ with _ => _ end ] => fail
                | _ =>
                  destruct X eqn:? => //
                end
              end || rewrite ?require_eq_refl //).
  Qed.

  Global Instance: PreOrder GlobDecl_ler := {}.
End GlobDecl_ler.

Section ObjValue_ler.
  Local Instance ObjValue_le_refl : Reflexive ObjValue_ler.
  Proof.
    intros []; rewrite /= ?require_eq_refl;
      case_match; rewrite ?require_eq_refl //.
  Qed.

  Local Instance ObjValue_le_trans : Transitive ObjValue_ler.
  Proof.
    intros a b c.
    destruct a, b => //=;
      destruct c => //=; intros;
        repeat (match goal with
              | H : require_eq _ _ _ = _ |- _ =>
                eapply require_eq_success in H; destruct H; subst
              | H : context [ match ?X with _ => _ end ] |- _ =>
                destruct X => //
              | H : _ = _ |- _ => rewrite H
              end || rewrite ?require_eq_refl //).
  Qed.

  Global Instance: PreOrder ObjValue_ler := {}.
End ObjValue_ler.

(* TODO: consider replacing [type_table_le]'s definition with [type_table_le_alt] *)
Definition type_table_le_alt : type_table -> type_table -> Prop :=
  map_included GlobDecl_ler.
Instance: PreOrder type_table_le_alt := _.

Definition type_table_le (te1 te2 : type_table) : Prop :=
  forall (gn : globname) gv,
    te1 !! gn = Some gv ->
    exists gv', te2 !! gn = Some gv' /\ GlobDecl_ler gv gv'.

(* Ditto. *)
Definition syms_table_le_alt : symbol_table -> symbol_table -> Prop :=
  map_included ObjValue_ler.
Instance: PreOrder syms_table_le_alt := _.

Definition syms_table_le (a b : symbol_table) :=
  forall (on : obj_name) v,
      a !! on = Some v ->
      exists v', b !! on = Some v' /\
            ObjValue_ler v v'.

Lemma type_table_le_equiv te1 te2 : type_table_le te1 te2 <-> type_table_le_alt te1 te2.
Proof.
  apply iff_forall => i; unfold option_relation.
  (* XXX TC inference produces different results here. Hacky fix. *)
  unfold globname, ident, type_table.
  repeat case_match; naive_solver.
Qed.

Lemma syms_table_le_equiv te1 te2 : syms_table_le te1 te2 <-> syms_table_le_alt te1 te2.
Proof.
  apply iff_forall => i; unfold option_relation.
  (* XXX TC inference produces different results here. Hacky fix, as above. *)
  unfold obj_name, symbol_table.
  repeat case_match; naive_solver.
Qed.

Instance: PreOrder type_table_le.
Proof.
  eapply preorder_proper.
  apply: type_table_le_equiv.
  apply _.
Qed.

Instance: PreOrder syms_table_le.
Proof.
  eapply preorder_proper.
  apply: syms_table_le_equiv.
  apply _.
Qed.

Local Hint Constructors complete_decl complete_basic_type complete_type complete_pointee_type complete_pointee_types : core.

Lemma complete_decl_respects_GlobDecl_le {te g1 g2} :
  GlobDecl_ler g1 g2 ->
  complete_decl te g1 ->
  complete_decl te g2.
Proof.
  intros Hle Hct; inversion Hct; simplify_eq; destruct g2 => //=;
    apply require_eq_success in Hle;
    destruct_and!; simplify_eq; auto.
Qed.

Local Definition complete_decl_respects te2 g := ∀ te1,
  type_table_le te2 te1 ->
  complete_decl te1 g.
Local Definition complete_basic_type_respects te2 t := ∀ te1,
  type_table_le te2 te1 ->
  complete_basic_type te1 t.
Local Definition complete_pointee_type_respects te2 t := ∀ te1,
  type_table_le te2 te1 ->
  complete_pointee_type te1 t.
Local Definition complete_pointee_types_respects te2 ts := ∀ te1,
  type_table_le te2 te1 ->
  complete_pointee_types te1 ts.
Local Definition complete_type_respects te2 t := ∀ te1,
  type_table_le te2 te1 ->
  complete_type te1 t.

(* Actual mutual induction. *)
Lemma complete_respects_sub_table_mut te2 :
  (∀ g : GlobDecl, complete_decl te2 g → complete_decl_respects te2 g) ∧
  (∀ t : type, complete_basic_type te2 t → complete_basic_type_respects te2 t) ∧
  (∀ t : type, complete_pointee_type te2 t → complete_pointee_type_respects te2 t) ∧
  (∀ l : list type, complete_pointee_types te2 l → complete_pointee_types_respects te2 l) ∧
  (∀ t : type, complete_type te2 t → complete_type_respects te2 t).
Proof.
  apply complete_mut_ind; try solve [intros; red; repeat_on_hyps (fun H => red in H); eauto].
  intros * Hlook Hct IH ? Hsub.
  destruct (Hsub _ _ Hlook) as (st1 & Hlook1 & Hle).
  apply (complete_named_struct _ Hlook1).
  apply (complete_decl_respects_GlobDecl_le Hle), IH, Hsub.
Qed.

Lemma complete_type_respects_sub_table te1 te2 t :
  type_table_le te2 te1 ->
  complete_type te2 t → complete_type te1 t.
Proof. intros. by eapply complete_respects_sub_table_mut. Qed.

(* TODO: reuse [type_table_le] for types_compat. *)
Record sub_module (a b : translation_unit) : Prop :=
{ types_compat : type_table_le a.(globals) b.(globals)
; syms_compat : syms_table_le a.(symbols) b.(symbols)
; byte_order_compat : a.(byte_order) = b.(byte_order) }.

Section sub_module.
  Local Instance: Reflexive sub_module.
  Proof. done. Qed.

  Local Instance: Transitive sub_module.
  Proof. intros ??? [] []; split; by etrans. Qed.

  Global Instance: PreOrder sub_module := {}.
End sub_module.
Instance: RewriteRelation sub_module := {}.

Instance byte_order_proper : Proper (sub_module ==> eq) byte_order.
Proof. by destruct 1. Qed.
Instance byte_order_flip_proper : Proper (flip sub_module ==> eq) byte_order.
Proof. by destruct 1. Qed.

Definition compat_le {T}
           (f : option T -> option T -> bool) (l r : IM.t T)
  : bool :=
  negb (find_any (fun k v => negb (f (Some v) (r !! k))) l ||
        find_any (fun k v => negb (f (l !! k) (Some v))) r).

Lemma compat_le_sound : forall {T} (f : option T -> _) l r,
    (forall x, f None x = true) ->
    if compat_le f l r then
      forall k : ident, f (l !! k) (r !! k) = true
    else
      exists k : ident, f (l !! k) (r !! k) = false.
Proof.
  intros.
  unfold compat_le.
  generalize (find_any_ok (λ (k : bs) (v : T), negb (f (Some v) (r !! k))) l).
  generalize (find_any_ok (λ (k : bs) (v : T), negb (f (l !! k) (Some v))) r).
  generalize (find_any (λ (k : bs) (v : T), negb (f (Some v) (r !! k))) l).
  generalize (find_any (λ (k : bs) (v : T), negb (f (l !! k) (Some v))) r).
  destruct b0; simpl; intros.
  - simpl.
    destruct H1 as [ k [ v [ ? ? ] ] ].
    exists k. apply negb_true_iff in H2.
    unfold lookup, IM_lookup.
    erewrite IM.find_1; eauto.
  - destruct b.
    + destruct H0 as [ k [ v [ ? ? ] ] ].
      exists k. apply negb_true_iff in H2.
      destruct H2. f_equal. unfold lookup, IM_lookup.
      erewrite IM.find_1; eauto.
    + simpl. intros.
      destruct (l !! k) eqn:?; auto.
      eapply IM.find_2 in Heqo.
      apply H1 in Heqo.
      apply negb_false_iff in Heqo.
      auto.
Qed.

Lemma complete_type_respects_sub_module tt1 tt2 t :
  sub_module tt2 tt1 ->
  complete_type tt2.(globals) t -> complete_type tt1.(globals) t.
Proof. move=> /types_compat Hsub Hct. exact: complete_type_respects_sub_table. Qed.

Definition module_le (a b : translation_unit) : bool :=
  bool_decide (a.(byte_order) = b.(byte_order)) &&
  compat_le (fun l r => match l , r with
                     | None , _ => true
                     | Some _ , None => false
                     | Some l , Some r =>
                       match GlobDecl_le l r with
                       | None => false
                       | Some _ => true
                       end
                     end) a.(globals) b.(globals) &&
  compat_le (fun l r => match l , r with
                      | None , _ => true
                      | Some _ , None => false
                      | Some l , Some r =>
                        match ObjValue_le l r with
                        | None => false
                        | Some _ => true
                        end
                      end) a.(symbols) b.(symbols).

Theorem module_le_sound : forall a b, if module_le a b then
                                   sub_module a b
                                 else
                                   ~sub_module a b.
Proof.
  unfold module_le; intros.
  destruct (bool_decide_reflect (byte_order a = byte_order b)); simpl.
  2:{ red. destruct 1. congruence. }
  match goal with
  | |- context [ compat_le ?f ?l ?r && _ ] =>
    generalize (@compat_le_sound _ f l r (fun _ => eq_refl)); destruct (@compat_le _ f l r)
  end.
  { intros.
    match goal with
    | |- context [ compat_le ?f ?l ?r ] =>
      generalize (@compat_le_sound _ f l r (fun _ => eq_refl)); destruct (@compat_le _ f l r)
    end; intros; simpl.
    constructor; auto.
    { unfold type_table_le. intros. specialize (H gn).
      change_rewrite_in H1 H.
      clear - H H1.
      match goal with
      | H : context [ match ?X with _ => _ end ] |- context [ ?A ] =>
        change X with A in H ; destruct A
      end => //.
      eexists; split; auto.
      unfold GlobDecl_ler.
      by destruct (GlobDecl_le _ _) as [[]|]. }
    { unfold syms_table_le. intros. specialize (H0 on).
      change_rewrite_in H1 H0.
      clear - H0 H1.
      match goal with
      | H : context [ match ?X with _ => _ end ] |- context [ ?A ] =>
        change X with A in H ; destruct A
      end => //.
      eexists; split; eauto.
      unfold ObjValue_ler.
      by destruct (ObjValue_le _ _) as [[]|]. }
    { simpl. clear H. intro.
      destruct H as [_ H].
      forward_reason.
      destruct (symbols a !! x) eqn:Heq; try congruence.
      { specialize (H _ _ Heq).
        forward_reason.
        change_rewrite_in H H0.
        forward.
        assert (Some o = Some o0) as [= ->] by by etrans.
        congruence. }
      { by change_rewrite_in Heq H0. } } }
  { intros; simpl; intros [ Hs _ ].
    destruct H.
    forward.
    specialize (Hs _ _ H).
    destruct Hs as [ ? [ ? ? ] ].
    change_rewrite_in H1 H0.
    forward. }
Qed.

Theorem module_le_spec : forall a b,
    Bool.reflect (sub_module a b) (module_le a b).
Proof.
  intros. generalize (module_le_sound a b).
  destruct (module_le a b); constructor; eauto.
Qed.

Instance sub_module_dec : RelDecision sub_module :=
  fun l r => match module_le l r as X
                return (if X then
                          sub_module l r
                        else ~sub_module l r) -> {_} + {_}
          with
          | true => fun pf => left pf
          | false => fun pf => right pf
          end (module_le_sound l r) .

(* [class_compatible a b c] states that translation units [a] and [b] have
 * the same definitions for the class [cls] (including all transitive
 * base classes)
 *
 * this is necessary, e.g. when code in translation unit [a] wants to call
 * via a virtual table that was constructed in translation unit [b]
 *)
Inductive class_compatible (a b : translation_unit) (cls : globname) : Prop :=
| Class_compat {st}
               (_ : a !! cls = Some (Gstruct st))
               (_ : b !! cls = Some (Gstruct st))
               (_ : forall base, In base (map fst st.(s_bases)) ->
                            class_compatible a b base).

(** * global environments *)

(** [genv_leq a b] states that [b] is an extension of [a] *)
Record genv_leq {l r : genv} : Prop :=
{ tu_le : sub_module l.(genv_tu) r.(genv_tu)
; pointer_size_le : l.(pointer_size_bitsize) = r.(pointer_size_bitsize) }.
Arguments genv_leq _ _ : clear implicits.

Instance PreOrder_genv_leq : PreOrder genv_leq.
Proof.
  constructor.
  { constructor; auto; reflexivity. }
  { red. destruct 1; destruct 1; constructor; try etransitivity; eauto. }
Qed.
Instance: RewriteRelation genv_leq := {}.

Definition glob_def (g : genv) (gn : globname) : option GlobDecl :=
  g.(genv_tu).(globals) !! gn.

Definition genv_eq (l r : genv) : Prop :=
  genv_leq l r /\ genv_leq r l.

Instance genv_tu_proper : Proper (genv_leq ==> sub_module) genv_tu.
Proof. solve_proper. Qed.
Instance genv_tu_flip_proper : Proper (flip genv_leq ==> flip sub_module) genv_tu.
Proof. solve_proper. Qed.

(* Sadly, neither instance is picked up by [f_equiv]. *)
Instance pointer_size_bitsize_proper : Proper (genv_leq ==> eq) pointer_size_bitsize.
Proof. solve_proper. Qed.
Instance pointer_size_bitsize_flip_proper : Proper (flip genv_leq ==> eq) pointer_size_bitsize.
Proof. by intros ?? <-. Qed.
Instance pointer_size_proper : Proper (genv_leq ==> eq) pointer_size.
Proof. unfold pointer_size; intros ???. f_equiv. exact: pointer_size_bitsize_proper. Qed.
Instance pointer_size_flip_proper : Proper (flip genv_leq ==> eq) pointer_size.
Proof. by intros ?? <-. Qed.

Instance genv_byte_order_proper : Proper (genv_leq ==> eq) genv_byte_order.
Proof. intros ???. apply sub_module.byte_order_proper. solve_proper. Qed.
Instance genv_byte_order_flip_proper : Proper (flip genv_leq ==> eq) genv_byte_order.
Proof. by intros ?? <-. Qed.
(* this states that the [genv] is compatible with the given [translation_unit]
 * it essentially means that the [genv] records all the types from the
 * compilation unit and that the [genv] contains addresses for all globals
 * defined in the [translation_unit]
 *)
Class genv_compat {tu : translation_unit} {g : genv} : Prop :=
{ tu_compat : sub_module tu g.(genv_tu) }.
Arguments genv_compat _ _ : clear implicits.
Infix "⊧" := genv_compat (at level 1).

Theorem genv_byte_order_tu tu g :
    tu ⊧ g ->
    genv_byte_order g = translation_unit.byte_order tu.
Proof. intros. apply byte_order_flip_proper, tu_compat. Qed.

Theorem genv_compat_submodule : forall m σ, m ⊧ σ -> sub_module m σ.(genv_tu).
Proof. by destruct 1. Qed.

Instance genv_compat_proper : Proper (flip sub_module ==> genv_leq ==> impl) genv_compat.
Proof.
  intros ?? Heq1 ?? [Heq2 _] [Heq3]; constructor.
  by rewrite Heq1 Heq3.
Qed.
Instance genv_compat_flip_proper : Proper (sub_module ==> flip genv_leq ==> flip impl) genv_compat.
Proof. solve_proper. Qed.

(* XXX rename/deprecate? *)
Theorem subModuleModels a b σ : b ⊧ σ -> sub_module a b -> a ⊧ σ.
Proof. by intros ? ->. Qed.
