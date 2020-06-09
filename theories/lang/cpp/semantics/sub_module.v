(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import stdpp.base.
Require Import bedrock.lang.cpp.syntax.translation_unit.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.avl.
Require Import ExtLib.Tactics.

Set Default Proof Using "Type".

Definition require_eq `{EqDecision T} (a b : T) {U} (r : option U) : option U :=
  if decide (a = b) then r else None.

Lemma require_eq_refl `{EqDecision T} : forall (a : T){U} (X : option U), require_eq a a X = X.
Proof.
  unfold require_eq. intros.
  destruct (decide (a = a)); auto.
  exfalso; auto.
Qed.

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

Theorem GlobDecl_le_refl : forall a, GlobDecl_le a a = Some tt.
Proof.
  destruct a; simpl; repeat rewrite require_eq_refl; eauto.
  destruct o; eauto.
  repeat rewrite require_eq_refl.
  reflexivity.
Qed.

Lemma require_eq_success `{EqDecision T} {U} : forall (a b : T) c (d : U),
    require_eq a b c = Some d ->
    a = b /\ c = Some d.
Proof.
  unfold require_eq; intros.
  destruct (decide (a = b)); try congruence; eauto.
Qed.

Theorem GlobDecl_le_trans : forall a b c,
    GlobDecl_le a b = Some tt ->
    GlobDecl_le b c = Some tt ->
    GlobDecl_le a c = Some tt.
Proof.
  destruct a; destruct b; simpl; intros; try congruence;
    destruct c; simpl in *; try congruence;
  repeat match goal with
             | H : require_eq _ _ _ = _ |- _ =>
               eapply require_eq_success in H; destruct H
             | H : context [ match ?X with _ => _ end ] |- _ =>
               lazymatch X with
               | context [ match _ with _ => _ end ] => fail
               | _ =>
                 destruct X eqn:?; try congruence
               end
             end; subst.
  all: repeat rewrite require_eq_refl; eauto; try congruence.
Qed.

Theorem ObjValue_le_refl : forall a, ObjValue_le a a = Some tt.
Proof.
  destruct a; simpl; repeat rewrite require_eq_refl; eauto.
  all: match goal with
       | |- context [ match ?X with _ => _ end ] => destruct X
       end; repeat rewrite require_eq_refl; eauto.
Qed.

Theorem ObjValue_le_trans : forall a b c, ObjValue_le a b = Some tt -> ObjValue_le b c = Some tt -> ObjValue_le a c = Some tt.
Proof.
  destruct a; destruct b; simpl; intros; try congruence;
    destruct c; simpl in *; try congruence;
      repeat match goal with
             | H : require_eq _ _ _ = _ |- _ =>
               eapply require_eq_success in H; destruct H
             | H : context [ match ?X with _ => _ end ] |- _ =>
               destruct X; try congruence
             | H : _ = _ |- _ => rewrite H
             end; subst.
  all: repeat rewrite require_eq_refl; eauto; try congruence.
Qed.

Definition sub_module (a b : translation_unit) : Prop :=
  (forall (gn : globname) gv,
      a.(globals) !! gn = Some gv ->
      exists gv', b.(globals) !! gn = Some gv' /\
             GlobDecl_le gv gv' = Some tt) /\
  (forall (on : obj_name) v,
      a.(symbols) !! on = Some v ->
      exists v', b.(symbols) !! on = Some v' /\
            ObjValue_le v v' = Some tt).

Instance: Reflexive sub_module.
Proof.
  split; intros; eauto; eexists; split; eauto.
  rewrite GlobDecl_le_refl. reflexivity.
  rewrite ObjValue_le_refl. reflexivity.
Qed.

Instance: Transitive sub_module.
Proof.
  red. destruct 1; destruct 1.
  split; intros.
  { apply H in H3. destruct H3 as [? [H3 ?]].
    apply H1 in H3. destruct H3 as [? [H3 ?]].
    eexists; split; eauto.
    clear - H4 H5.
    eapply GlobDecl_le_trans; eauto. }
  { apply H0 in H3. destruct H3 as [? [H3 ?]].
    apply H2 in H3. destruct H3 as [? [H3 ?]].
    eexists; split; eauto.
    clear - H4 H5.
    eapply ObjValue_le_trans; eauto. }
Qed.

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

Definition module_le (a b : translation_unit) : bool :=
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
  match goal with
  | |- context [ compat_le ?f ?l ?r && _ ] =>
    generalize (@compat_le_sound _ f l r (fun _ => eq_refl)); destruct (@compat_le _ f l r)
  end.
  { intros.
    match goal with
    | |- context [ compat_le ?f ?l ?r ] =>
      generalize (@compat_le_sound _ f l r (fun _ => eq_refl)); destruct (@compat_le _ f l r)
    end; intros.
    simpl.
    red. split.
    { intros. specialize (H gn).
      change_rewrite_in H1 H.
      clear - H H1.
      match goal with
      | H : context [ match ?X with _ => _ end ] |- context [ ?A ] =>
        change X with A in H ; destruct A
      end; try congruence.
      exists g. split; auto.
      destruct (GlobDecl_le gv g); try congruence.
      destruct u; reflexivity. }
    { intros.
      intros. specialize (H0 on).
      change_rewrite_in H1 H0.
      clear - H0 H1.
      match goal with
      | H : context [ match ?X with _ => _ end ] |- context [ ?A ] =>
        change X with A in H ; destruct A
      end; try congruence.
      eexists; split; eauto.
      destruct (ObjValue_le v o); try congruence.
      destruct u; reflexivity. }
    { simpl. clear H. intro.
      destruct H as [_ H].
      forward_reason.
      destruct (symbols a !! x) eqn:Heq; try congruence.
      { specialize (H _ _ Heq).
        forward_reason.
        change_rewrite_in H H0.
        forward.
        assert (Some o = Some o0).
        { rewrite <- Heq. rewrite <- H0. reflexivity. }
        inversion H4. subst.
        congruence. }
      { change_rewrite_in Heq H0. congruence. } } }
  { intros; unfold sub_module; simpl; intros [ Hs _ ].
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
