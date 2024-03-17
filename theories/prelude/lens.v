(*
 * Copyright (C) 2021-2022 BedRock Systems, Inc.
 * All rights reserved.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** This defines several useful lenses.
Some of them, however, do not satisfy all lens laws ("fake lenses").
*)

Require Import elpi.apps.NES.NES.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.finite.
Require Import bedrock.prelude.functions.
Require Export Lens.Lens.

Export LensNotations.
#[local] Open Scope lens_scope.

Definition _bit (n : N) : N -l> bool :=
  {| view := fun x => N.testbit x n
   ; over := fun (f : bool -> bool) x =>
              if f (N.testbit x n) then N.setbit x n else N.clearbit x n |}.

Notation "X ~l> Y" := (X -l> Y)
  (at level 99, Y at level 200, right associativity, only parsing) : type_scope.
(** ^^ Notation to be used for "partial" lenses that do _not_ respect lens laws.
Their existence is controversial, but inconvenient to avoid without supporting more optics.
*)

(* XXX To upstream somewhere; it belongs upstream and/or in coq-lens. *)
#[local] Arguments Build_Lens {_ _ _ _}.

NES.Begin lens.
  Definition of_get_set {s t a b} (get : s -> a) (set : s -> b -> t) : Lens s t a b :=
    Build_Lens get (λ (upd : a -> b) (x : s), set x (upd (get x))).

  (* For this to produce a lawful lens, it suffices that [get] and [put] are
  inverses, as in [iso2lens]. *)
  Definition of_get_put {X Y} (get : X -> Y) (put : Y -> X) : X -l> Y :=
    of_get_set get (fun _ => put).
NES.End lens.

Definition _id {A} : A -l> A := lens.of_get_put id id.
Definition _fst {A B} : A * B -l> A :=
  {| view := fst; over f p := (f p.1, p.2) |}.
Definition _snd {A B} : A * B -l> B :=
  {| view := snd; over f p := (p.1, f p.2) |}.
Definition _const {A B} (b : B) : A ~l> B := Build_Lens (const b) (λ _ a, a).
(* For this lens to be lawful, it suffices that [get] and [set] are inverses on the
image of [l.(set)] i*)
Definition _lift {A B C} (get : A -> B) (set : B -> A) (l : B -l> C) : A -l> C :=
  lens_compose (lens.of_get_put get set) l.

Definition _map_apply {K V M} `{Insert K V M} `{LookupTotal K V M} (k : K) : M -l> V :=
  {| view f := f !!! k
   ; over upd_f whole_f :=
    <[ k := upd_f (whole_f !!! k) ]> whole_f
  |}.

Definition _apply {A B} `{EqDecision A} (a : A) : (A -> B) -l> B :=
  _map_apply a.

(** If you can lens values [V] for any key [K] out of state [S],
you can also lens an entire [K -> V] out of [S], as long as [K] is finite. *)
Definition _total_fun `{Finite K} {V S} (_key_lens : K -> (S -l> V)) : S -l> (K -> V) :=
  lens.of_get_set
    (λ (s : S) (k : K), s .^ _key_lens k)
    (λ (s0 : S) (kv : K -> V),
      let set_one_key (k : K) (s : S) : S := s &: _key_lens k .= kv k in
      foldr set_one_key s0 (enum K)).

(* Show that we can remove the abstractions in [_apply] and get the old definition. *)
Section _apply_unfold.
  Lemma view_apply {A B} `{EqDecision A} (a : A) (f : A -> B) : view (_apply a) f = f a.
  Proof. done. Qed.

  #[local] Lemma over_apply_raw {A B} `{EqDecision A} (a : A) (upd_f : B -> B) whole_f (x : A) :
    over (_apply a) upd_f whole_f x =
      if decide (a = x) then upd_f (whole_f a) else whole_f x.
  Proof. done. Qed.

  Lemma over_apply {A B} `{EqDecision A} (a : A) (upd_f : B -> B) whole_f (x : A) :
    over (_apply a) upd_f whole_f x =
      if bool_decide (a = x) then upd_f (whole_f a) else whole_f x.
  Proof. by rewrite over_apply_raw decide_bool_decide. Qed.
End _apply_unfold.

(*
Beware: this is unlikely to satisfy lens laws unless we're dealing with
"disjoint" lenses. And we'd need a PCM to formalize that.
Even monoid axioms seem tricky.

But _my_ concrete uses seem well-behaved.
*)
Section monoid.
  Context {A : Type} `{!Empty M} `{!Union M}.
  #[global] Instance lens_unit : Empty (A -l> M) := _const ∅.

  #[global] Instance lens_union : Union (A -l> M) := λ l1 l2,
    Build_Lens
      (λ a, a .^ l1 ∪ a .^ l2)
      (λ upd s, s &: l1 %= upd &: l2 %= upd).

  Import bedrock.prelude.axioms.funext.

  #[global] Instance lens_left_id `{!LeftId (=@{M}) ∅ (∪)} :
    LeftId (=@{A -l> M}) ∅ (∪).
  Proof.
    rewrite /lens_unit /lens_union /empty /union /=.
    move=>[v o] /=; f_equiv; funext; last done.
    intros; by rewrite left_id_L.
  Qed.

  #[global] Instance lens_right_id `{!RightId (=@{M}) ∅ (∪)} :
    RightId (=@{A -l> M}) ∅ (∪).
  Proof.
    rewrite /lens_unit /lens_union /empty /union /=.
    move=>[v o] /=; f_equiv; funext; last done.
    intros; by rewrite right_id_L.
  Qed.

  #[global] Instance lens_assoc `{!Assoc (=@{M}) (∪)} :
    Assoc (=@{A -l> M}) (∪).
  Proof.
    rewrite /lens_unit /lens_union /empty /union /=.
    move=>a b c /=; f_equiv; funext.
    intros; by rewrite assoc_L.
  Qed.
End monoid.

Module iso.
  Record t {A B} := Mk { f : A -> B ; g : B -> A }.
  #[global] Arguments t : clear implicits.
  #[global] Arguments Mk {A B} _ _ : assert.

  (* TODO: these should be [Cancel] instances. *)
  Record lawsT {A B} (l : iso.t A B) : Prop := MkLaws
  { f_g : ∀ b, l.(f) $ l.(g) b = b
  ; g_f : ∀ a, l.(g) $ l.(f) a = a
  }.

  Definition inv {A B} (iso : iso.t A B) : iso.t B A :=
    Mk iso.(g) iso.(f).
End iso.
Definition iso2lens {A B} (i : iso.t A B) : A -l> B :=
  lens.of_get_put (iso.f i) (iso.g i).

(**
Lens laws for monomorphic lenses [A -l> B].
Provisional; these are useful as a sanity checks, but no inference convenience
is provided.

TODO FM-1193 for a proper solution.
*)
Record LensLaws' {A B} {R : relation A} {S : relation B} {l : A -l> B} := MkLensLaws
{ view_over upd x : S (view l (over l upd x)) (upd (view l x))
; view_set x v : S (view l (set l v x)) v
; set_view x : R (set l (view l x) x) x
; set_set x v v' : R (set l v' (set l v x)) (set l v' x)
}.
Arguments LensLaws' {A B} R S l.

Lemma iso2lens_laws {A B} (i : iso.t A B) (Hl : iso.lawsT i) :
  LensLaws' eq eq (iso2lens i).
Proof.
  by case: i Hl => f g [/= f_g g_f]; split; simpl.
Qed.

Section _constr.
  Context {A1 A2 B : Type} (constr : A1 -> A2) (inv : A2 -> option A1).

  Definition _constr : (A2 -> B) -l> (A1 -> B) :=
    {| view f r := f (constr r)
    ; over upd_f whole_f r :=
        match inv r with
        | Some gr => upd_f (λ r, whole_f (constr r)) gr
        | _ => whole_f r
        end |}.
  (*
  As a test, prove lens laws from
  https://hackage.haskell.org/package/lens-5.0.1/docs/Control-Lens-Lens.html
  *)

  Lemma constr_view_over f upd a1
    (Hinv1 : ∀ x, inv (constr x) = Some x) :
    view _constr (over _constr upd f) a1 = upd (view _constr f) a1.
  Proof. cbv. move: Hinv1 => /(_ a1). by case: (inv _) => [a [->]|]. Qed.

  (* view l (set l v s)  ≡ v *)
  Lemma constr_view_set f a1 v
    (Hinv1 : ∀ x, inv (constr x) = Some x) :
    view _constr (set _constr v f) a1 = v a1.
  Proof. apply constr_view_over, Hinv1. Qed.

  (* set l (view l s) s ≡ s *)
  Lemma constr_set_view f a2
    (Hinv2 : ∀ a1 a2, inv a2 = Some a1 -> constr a1 = a2) :
    set _constr (view _constr f) f a2 = f a2.
  Proof. cbv. case E: (inv _) => [a1|//]. by rewrite (Hinv2 a1 a2). Qed.

  (* set l v' (set l v s) ≡ set l v' s *)
  Lemma constr_set_set f v v' a2 :
    set _constr v' (set _constr v f) a2 = set _constr v' f a2.
  Proof. cbv. by case_match. Qed.

  Lemma constr_laws
      (Hinv1 : ∀ x, inv (constr x) = Some x)
      (Hinv2 : ∀ a1 a2, inv a2 = Some a1 -> constr a1 = a2) :
    LensLaws' (pointwise_relation _ eq) (pointwise_relation _ eq) _constr.
  Proof.
    split; intros * ?.
    { exact: constr_view_over. }
    { exact: constr_view_set. }
    { exact: constr_set_view. }
    { apply: constr_set_set. }
  Qed.
End _constr.
