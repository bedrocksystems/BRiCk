(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Functionality to elaborate specifications that are written to take
    operands (i.e. [val]) and convert them to take materialized values.

    We implement this in an ad-hoc manner (i.e. using type classes) because:
    1. the implementation requires matching under lambdas.
    2. the implementation is complex due to the telescopes.
 *)

Require Import bedrock.prelude.telescopes.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.logic.
Require Import bedrock.lang.cpp.specs.with_pre_post.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.

  #[local] Set Universe Polymorphism.
  Polymorphic Universes X Z Y.
  Let PROP := mpredI.

  Section with_AR.

    Polymorphic Universes A R.
    Context {A : Type@{A}} {R : Type@{R}}.
    Definition add_with {t : tele} (wpp : t -t> WithPrePostG@{X Z Y A R} PROP A R) : WithPrePostG@{X Z Y A R} PROP A R.
      refine
        {| wpp_with := tele_append t (tele_map wpp_with wpp)
           ; wpp_pre  := _
           ; wpp_post := _
        |}.
      { refine ((fix go (t : tele)  :=
                   match t as t
                         return forall (wpp : t -t> WithPrePostG PROP A R),
                       tele_append t (tele_map wpp_with wpp) -t> A * PROP
                   with
                   | TeleO => fun wpp => wpp.(wpp_pre)
                   | TeleS rst => fun wpp x => go (rst x) (wpp x)
                   end) t wpp).
      }
      { refine ((fix go (t : tele)  :=
                   match t as t
                         return forall (wpp : t -t> WithPrePostG PROP A R),
                       tele_append t (tele_map wpp_with wpp) -t> _
                   with
                   | TeleO => fun wpp => wpp.(wpp_post)
                   | TeleS rst => fun wpp x => go (rst x) (wpp x)
                   end) t wpp).
      }
    Defined.

    Definition add_pre (P : PROP) (wpp : WithPrePostG PROP A R) : WithPrePostG PROP A R :=
      {| wpp_with := wpp.(wpp_with)
       ; wpp_pre  := tele_map (fun '(args,X) => (args, P ** X)) wpp.(wpp_pre)
       ; wpp_post := wpp.(wpp_post)
      |}.

    Definition add_post (P : PROP) (wpp : WithPrePostG PROP A R) : WithPrePostG PROP A R :=
      {| wpp_with := wpp.(wpp_with)
       ; wpp_pre  := wpp.(wpp_pre)
       ; wpp_post :=
           tele_map (WithExG_map (fun r Q => (r,P ** Q))) wpp.(wpp_post)
      |}.
    Definition add_require (P : Prop) (wpp : WithPrePostG mpredI A R) : WithPrePostG mpredI A R :=
      {| wpp_with := wpp.(wpp_with)
         ; wpp_pre := tele_map (fun '(args,X) => (args, [| P |] ** X)) wpp.(wpp_pre)
         ; wpp_post := wpp.(wpp_post)
      |}.

    Definition add_persist (P : mpredI) (wpp : WithPrePostG mpredI A R) : WithPrePostG mpredI A R :=
      {| wpp_with := wpp.(wpp_with)
       ; wpp_pre := tele_map (fun '(args,X) => (args, □ P ** X)) wpp.(wpp_pre)
       ; wpp_post := wpp.(wpp_post)
       |}.

    Definition add_prepost (P : mpredI) (wpp : WithPrePostG mpredI A R) : WithPrePostG mpredI A R :=
      add_pre P (add_post P wpp).
  End with_AR.

  Definition add_arg {val : Type} {R} (s : names.ident) (v : val)
             (wpp : WithPrePostG mpredI (list val) R) : WithPrePostG mpredI (list val) R :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre  := tele_map (fun '(args,X) => (v :: args, X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
    |}.

  Definition add_prim_arg {R} (t : type) (s : names.ident) (v : val)
             (wpp : WithPrePostG mpredI (list ptr) R) : WithPrePostG mpredI (list ptr) R :=
    @add_with _ _ (TeleS (fun _ : ptr => TeleO))
              (fun p : ptr => add_arg (val:=ptr) s p (add_pre (_at p (primR t 1 v))
                                                           (add_post (_at p (anyR t 1)) wpp))).

  Definition post_ret {val : Type} {A} (t : tele) (Q : t -t> val * PROP) : WithPrePostG mpredI (list A) val :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, emp)%I
     ; wpp_post := {| we_ex := t
                    ; we_post := Q |} |}.

  Definition post_prim_ret {A} (ty : type) (t : tele@{X}) (Q : t -t> val * PROP) : WithPrePostG mpredI (list A) ptr :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, emp)%I
     ; wpp_post := {| we_ex := TeleS (fun _ : ptr => t)
                    ; we_post := fun p => tele_map (fun '(v,Q) => (p, _at p (primR ty 1 v) ** Q)) Q |} |}.

  Class Elaborate (ts : list type) (rt : type) (wpp : WithPrePost@{X Z Y} mpredI) : Type :=
    elaborated : WithPrePostG@{X Z Y Set Set} mpredI (list ptr) ptr.

  Section parametric.
    Variables (ts : list type) (rt : type).
    #[local] Notation Elaborate := (Elaborate ts rt).

    #[program] Instance add_require_Elaborate {P} `{Elaborate wpp} : Elaborate (add_require P wpp) :=
      add_require P elaborated.

    #[program] Instance add_pre_Elaborate {P} `{Elaborate wpp} : Elaborate (add_pre P wpp) :=
      add_pre P elaborated.

    #[program] Instance add_post_Elaborate {P} `{Elaborate wpp} : Elaborate (add_post P wpp) :=
      add_post P elaborated.

    #[program] Instance add_prepost_Elaborate {P} `{Elaborate wpp} : Elaborate (add_prepost P wpp) :=
      add_prepost P elaborated.

  End parametric.

  Class ElaborateArg R (ty : type) (x : names.ident) (v : val) : Type :=
    elaborated_arg : WithPrePostG mpredI (list ptr) R -> WithPrePostG mpredI (list ptr) R.
  Instance Tint_ElaborateArg {R sz sgn x v} : @ElaborateArg R (Tint sz sgn) x v :=
    add_prim_arg (Tint sz sgn) x v.
  Instance Tptr_ElaborateArg {R ty x v} : @ElaborateArg R (Tptr ty) x v :=
    add_prim_arg (Tptr ty) x v.
  Instance Tbool_ElaborateArg {R x v} : @ElaborateArg R Tbool x v :=
    add_prim_arg Tbool x v.
  Instance Tnamed_ElaborateArg {R cls x p} : @ElaborateArg R (Tnamed cls) x (Vptr p) :=
    add_arg x p.
  Instance Tref_ElaborateArg {R ty x p} : @ElaborateArg R (Tref ty) x (Vptr p) :=
    add_arg x p.
  Instance Trv_ref_ElaborateArg {R ty x p} : @ElaborateArg R (Trv_ref ty) x (Vptr p) :=
    add_arg x p.

  #[program] Instance add_arg_Elaborate_Tint {ty ts rt} {x} {v : val} `{@ElaborateArg _ ty x v} `{Elaborate ts rt wpp}
    : Elaborate (ty :: ts) rt (add_arg x v wpp) :=
    elaborated_arg elaborated.

  #[program] Instance post_ret_Elaborate {sz sgn} t Q
    : Elaborate nil (Tint sz sgn) (post_ret t Q) :=
    @post_prim_ret _ (Tint sz sgn) t Q.

  Arguments elaborated _ _ _ {_}.

  Goal forall p z q OPAQUE, ⊢@{mpredI} OPAQUE (elaborated (Tint W64 Signed :: Tptr (Tnamed "X") :: nil) (Tint W64 Signed)
                                    (add_arg "x" (Vint z) (add_arg "y" (Vptr p) (@post_ret _ _ TeleO (Vint q, emp%I))))).
  Proof.
    rewrite /WppGD/add_arg_Elaborate_Tint/post_ret_Elaborate/elaborated/=.
  Abort.

End with_cpp.



