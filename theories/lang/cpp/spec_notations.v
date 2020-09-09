(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import stdpp.telescopes.
Require Import bedrock.bytestring.
Require Import bedrock.lang.cpp.logic.

Declare Scope fspec_scope.
Delimit Scope fspec_scope with fspec.
Bind Scope fspec_scope with WithPrePost.

Set Universe Polymorphism.

Fixpoint tele_append (t : tele) {struct t}: (t -t> tele) -> tele :=
  match t as t return (t -t> tele) -> tele with
  | TeleO => fun x : tele => x
  | @TeleS T f => fun x => @TeleS T (fun t => tele_append (f t) (x t))
  end.

Section with_Σ.
  Context `{PROP : bi}.

  Local Notation WithPrePost := (WithPrePost PROP) (only parsing).

  Definition add_pre (P : PROP) (wpp : WithPrePost) : WithPrePost :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre  := tele_map (fun '(args,X) => (args, P ** X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
     |}.

  Definition add_args (ls : list val) (wpp : WithPrePost) : WithPrePost :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre  := tele_map (fun '(args,X) => (ls ++ args, X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
    |}.

  Definition add_arg (s : names.ident) (v : val) (wpp : WithPrePost) : WithPrePost :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre  := tele_map (fun '(args,X) => (v :: args, X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
    |}.

  Definition add_post (P : PROP) (wpp : WithPrePost) : WithPrePost :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre  := wpp.(wpp_pre)
     ; wpp_post :=
         tele_map (WithEx_map (fun r Q => (r,P ** Q))) wpp.(wpp_post)
    |}.

  Definition add_require (P : Prop) (wpp : WithPrePost) : WithPrePost :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre := tele_map (fun '(args,X) => (args, [| P |] ** X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
    |}.

  Definition add_prepost (P : PROP) (wpp : WithPrePost) : WithPrePost :=
    add_pre P (add_post P wpp).

  Definition post_void (t : tele) (Q : t -t> PROP) : WithPrePost :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, empSP)
     ; wpp_post := {| we_ex := t
                    ; we_post := tele_map (fun Q => (Vvoid, Q)) Q |} |}.

  Definition post_ret (t : tele) (Q : t -t> val * PROP) : WithPrePost :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, empSP)
     ; wpp_post := {| we_ex := t
                    ; we_post := Q |} |}.

  Definition add_with {t : tele} (wpp : t -t> WithPrePost) : WithPrePost.
  refine
    {| wpp_with := tele_append t (tele_map wpp_with wpp)
     ; wpp_pre  := _
     ; wpp_post := _
     |}.
  { refine ((fix go (t : tele)  :=
              match t as t
                    return forall (wpp : t -t> WithPrePost),
                  tele_append t (tele_map wpp_with wpp) -t> list val * PROP
              with
              | TeleO => fun wpp => wpp.(wpp_pre)
              | TeleS rst => fun wpp => _
              end) t wpp). simpl.
    intro x.
    eapply go. }
  { refine ((fix go (t : tele)  :=
              match t as t
                    return forall (wpp : t -t> WithPrePost),
                  tele_append t (tele_map wpp_with wpp) -t> _
              with
              | TeleO => fun wpp => wpp.(wpp_post)
              | TeleS rst => fun wpp0 => _
              end) t wpp). simpl.
    intro x.
    eapply go. }
  Defined.

  Definition let_fspec (X : WithPrePost) : WithPrePost := X.

  Definition with_arg_fspec (X : WithPrePost) : WithPrePost := X.

  Definition with_pre_fspec (X : WithPrePost) : WithPrePost := X.

  Definition with_prepost_fspec (X : WithPrePost) : WithPrePost := X.

  Definition with_tele (t : telescopes.tele) (f : telescopes.tele_arg t -> WithPrePost)
  : WithPrePost :=
    @add_with (telescopes.TeleS (fun x : telescopes.tele_arg t => telescopes.TeleO)) f.

  Definition exactWpp (wpp : WithPrePost) : WithPrePost := wpp.

End with_Σ.

Arguments with_tele _ _ _ : clear implicits.

Strategy expand
   [ add_pre add_args add_require add_arg add_post add_prepost let_fspec
     with_tele with_arg_fspec ].

Notation "'\with' x .. y X" :=
  (@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
            (fun x => .. (fun y => X%fspec) ..))
  (at level 10, x closed binder, y closed binder, X at level 200, right associativity,
   format "'[v' '\with'     '[hv' x  ..  y ']'  '//' X ']'").

Notation "'\withT' ts <- t X" := (@with_tele _ t (fun ts => X))
  (at level 200, ts ident, X at level 200, right associativity,
   format "'[v' '\withT'     ts <- t  '//' X ']'").

Notation "'\prepost' pp X" :=
  (@add_prepost _ pp%I X%fspec)
  (at level 10, pp at level 100, X at level 200, right associativity,
   format "'[v' '\prepost'  '[hv' pp ']' '//' X ']'").

Notation "'\prepost{' x .. y '}' pp X" :=
  (with_prepost_fspec ((@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) .. ))
                                (fun x => .. (fun y => @add_prepost _ pp%I X%fspec) .. ))))
  (at level 10, x binder, y binder, pp at level 100, X at level 200, right associativity,
   format "'[v' '\prepost{' x .. y '}'  '[hv' pp ']' '//' X ']'").

Notation "'\let' x ':=' e X" :=
  (let_fspec (let x := e in X%fspec))
  (at level 10, x pattern, e at level 150, X at level 200, right associativity,
   format "'[v' '\let'      x  ':='  '[hv' e ']' '//' X ']'").

Notation "'\args' ls X" :=
  (@add_args _ ls%list X%fspec)
  (at level 10, X at level 200, right associativity,
   format "'[v' '\args'     ls  '//' X ']'").

Notation "'\args{' x .. y '}' ls X" :=
  (@with_arg_fspec _ (@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) .. ))
                                (fun x => .. (fun y => (@add_args _ ls%list X%fspec)) .. )))
  (at level 10, x binder, y binder, X at level 200, right associativity,
   format "'[v' '\args{' x  ..  y '}'  ls  '//' X ']'").

Notation "'\arg' nm v X" :=
  (@add_arg _ nm%bs v X%fspec)
  (at level 10, nm at level 0, X at level 200, right associativity,
   format "'[v' '\arg'  nm  v  '//' X ']'").

Notation "'\arg{' x .. y } nm v X" :=
  (@with_arg_fspec _ (@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
                                (fun x => .. (fun y => (@add_arg _ nm%bs v X%fspec)) .. )))
  (at level 10, nm at level 0, x binder, y binder, X at level 200, right associativity,
   format "'[v' '\arg{' x  ..  y '}'  nm  v  '//' X ']'").

Notation "'\require' pre X" :=
  (@add_require _ pre X%fspec)
  (at level 10, pre at level 200, X at level 200, left associativity,
   format "'[v' '\require'  pre  '//' X ']'").

Notation "'\pre' pre X" :=
  (@add_pre _ pre%I X%fspec)
  (at level 10, pre at level 200, X at level 200, left associativity,
   format "'[v' '\pre'  pre  '//' X ']'").

Notation "'\pre{' x .. y '}' pp X" :=
  (with_pre_fspec ((@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) .. ))
                                (fun x => .. (fun y => @add_pre _ pp%I X%fspec) .. ))))
  (at level 10, x binder, y binder, pp at level 100, X at level 200, right associativity,
   format "'[v' '\pre{' x .. y '}'  '[hv' pp ']' '//' X ']'").

Notation "'\post' { x .. y } [ r ] post" :=
  (@post_ret _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
             (fun x => .. (fun y => (r, post%I)) ..))
  (at level 10, r at level 200, no associativity, x binder, y binder,
   post at level 200,
   format "'[v' '\post' { x  ..  y } [ r ]  '//'          '[hv ' post ']' ']'").

Notation "'\post' { } [ r ] post" :=
  (@post_ret _ TeleO (r, post%I))
  (at level 10, r at level 200, no associativity,
   post at level 200,
   format "'[v' '\post' { } [ r ]  '//'          '[hv ' post ']' ']'").

Notation "'\post' [ r ] post" :=
  (@post_ret _ (TeleS (fun r : val => TeleO))
               (fun r => (r, post%I)))
  (at level 10, r at level 200, no associativity,
   post at level 200,
   format "'[v' '\post' [ r ]  '[hv ' post ']' ']'").

Notation "'\post' post" :=
  (@post_void _ TeleO post%I)
  (at level 10, no associativity,
   post at level 200,
   format "'[v' '\post'     '[hv ' post ']' ']'").

Notation "'\exact' wpp" := (exactWpp wpp)
  (at level 10, wpp at level 200).

Section with_Σ.
  Context `{Σ : cpp_logic ti}.

Goal WithPrePost mpredI.
refine (
  \pre empSP
  \post  empSP
).
(* Show Proof. *)
Abort.

Goal WithPrePost mpredI.
refine (
   \with (I J : mpred) (p : ptr) (R : Qp -> Qp -> nat -> Rep)
   \prepost empSP
   \require True
   \arg{n (nn: nat)} "foo" (Vint n)
   \args{a} [Vint (Z.of_nat a)]
   \with (z : nat)
   \prepost empSP
   \prepost{q1 q2} _at (_eq p) (R q1 q2 0)
   \pre{q3 q4} _at (_eq p) (R q3 q4 0)
   \pre empSP ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post {x} [ Vint x ] empSP).
(* Show Proof. *)
Abort.

Goal WithPrePost mpredI.
refine (
   \with (I J : mpred)
   \with  (a : nat)
   \prepost empSP
   \with (z : nat)
   \prepost empSP
   \pre empSP ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post{r}[ r ] empSP).
(* Show Proof. *)
Abort.

Goal WithPrePost mpredI.
refine (
   \with (I J : mpred) (n : nat)
   \with  (a : nat)
   \let x := 3%nat
   \with (lm : nat * nat)
   \let (l,m) := lm
   \require l+m = 3
   \prepost empSP
   \with (z : nat)
   \arg{(zz : Z)} "foo" zz
   \prepost empSP
   \pre empSP ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post empSP).
(* Show Proof. *)
Abort.

Goal WithPrePost mpredI.
refine (
    \pre empSP ** Exists y : nat, [| y = 3 |]
    \post{} [ Vptr nullptr ] empSP).
(* Show Proof. *)
Abort.


Goal WithPrePost mpredI.
refine (
    \pre |==> True ** |={∅,⊤}=> False
    \post{} [ Vptr nullptr ] empSP).
(* Show Proof. *)
Abort.

End with_Σ.
