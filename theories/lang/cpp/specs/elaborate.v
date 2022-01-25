(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Functionality to elaborate specifications that are written to take
    operands (i.e. [val]) and convert them to take materialized values.

    We implement this using ad-hoc polymorphism (i.e. type classes) because:
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

  #[local] Notation WPP := (WithPrePostG@{X Z Y _ (*Set*) Set} mpredI).

  Definition add_prim_arg {R} (t : type) (s : names.ident) (v : val)
             (wpp : WPP (list ptr) R) : WPP (list ptr) R :=
    add_with (t:=TeleS (fun _ : ptr => TeleO))
             (fun p : ptr => add_arg (A:=ptr) s p (add_pre (_at p (primR t 1 v))
                                                        (add_post (_at p (anyR t 1)) wpp))).

  Definition post_prim_ret {A} (ty : type) (t : tele@{X}) (Q : t -t> val * mpredI) : WPP (list A) ptr :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, emp)%I
     ; wpp_post := {| we_ex := TeleS (fun _ : ptr => t)
                    ; we_post := fun p => tele_map (fun '(v,Q) => (p, _at p (primR ty 1 v) ** Q)) Q |} |}.

  Class Elaborate (ts : list type) (rt : type) (wpp : WithPrePost@{X Z Y} mpredI) : Type :=
    elaborated : WPP (list ptr) ptr.

  Section parametric.
    Variables (ts : list type) (rt : type).
    #[local] Notation Elaborate := (Elaborate ts rt).


    #[global] Instance add_with_Elaborate {t} `{X : tforallT (fun args => Elaborate (tele_app wpp args))}
      : Elaborate (add_with (t:=t) wpp) :=
      add_with (t:=t) (tele_bind (fun args => @elaborated _ _ _ (tapplyT _ X args))).

    #[global] Instance add_require_Elaborate {P} `{Elaborate wpp} : Elaborate (add_require P wpp) :=
      add_require P elaborated.

    #[global] Instance add_pre_Elaborate {P} `{Elaborate wpp} : Elaborate (add_pre P wpp) :=
      add_pre P elaborated.

    #[global] Instance add_post_Elaborate {P} `{Elaborate wpp} : Elaborate (add_post P wpp) :=
      add_post P elaborated.

    #[global] Instance add_prepost_Elaborate {P} `{Elaborate wpp} : Elaborate (add_prepost P wpp) :=
      add_prepost P elaborated.

  End parametric.

(*  #[global] Existing Instances add_with_Elaborate add_require_Elaborate add_pre_Elaborate add_post_Elaborate add_prepost_Elaborate. *)

  Class ElaborateArg R (ty : type) (x : names.ident) (v : val) : Type :=
    elaborated_arg : WPP (list ptr) R -> WPP (list ptr) R.
  #[global] Instance Tint_ElaborateArg {R sz sgn x v} : @ElaborateArg R (Tint sz sgn) x v :=
    add_prim_arg (Tint sz sgn) x v.
  #[global] Instance Tptr_ElaborateArg {R ty x v} : @ElaborateArg R (Tptr ty) x v :=
    add_prim_arg (Tptr ty) x v.
  #[global] Instance Tbool_ElaborateArg {R x v} : @ElaborateArg R Tbool x v :=
    add_prim_arg Tbool x v.
  #[global] Instance Tnamed_ElaborateArg {R cls x p} : @ElaborateArg R (Tnamed cls) x (Vptr p) :=
    add_arg x p.
  #[global] Instance Tref_ElaborateArg {R ty x p} : @ElaborateArg R (Tref ty) x (Vptr p) :=
    add_arg x p.
  #[global] Instance Trv_ref_ElaborateArg {R ty x p} : @ElaborateArg R (Trv_ref ty) x (Vptr p) :=
    add_arg x p.

  #[global] Instance add_arg_Elaborate {ty ts rt} {x} {v : val} `{@ElaborateArg _ ty x v} `{Elaborate ts rt wpp}
    : Elaborate (ty :: ts) rt (add_arg x v wpp) :=
    elaborated_arg elaborated.

  #[global] Instance post_ret_Elaborate {sz sgn} t Q
    : Elaborate nil (Tint sz sgn) (post_ret (t:=t) Q) :=
    @post_prim_ret _ (Tint sz sgn) t Q.

End with_cpp.

Arguments elaborated {_ Σ} ts rt wpp {_}.

#[global] Hint Extern 0 (tforallT ?X) => simpl; intros : typeclass_instances.

Section tests.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.

  Goal forall p q OPAQUE,
      OPAQUE (elaborated (Tint W64 Signed :: Tptr (Tnamed "X") :: nil) (Tint W64 Signed)
                         (add_arg "x" (Vint 0) (add_arg "y" (Vptr p) (post_ret (t:=TeleO) (Vint q, emp%I))))).
  Proof.
    rewrite /add_arg_Elaborate/post_ret_Elaborate/elaborated/elaborated_arg/Tint_ElaborateArg/Tptr_ElaborateArg/=.
  Abort.

  Goal forall p q OPAQUE,
      OPAQUE (elaborated (Tint W64 Signed :: Tptr (Tnamed "X") :: nil) (Tint W64 Signed)
                         (add_with (t:=TeleS (fun _ => TeleO))
                                   (fun z => add_arg "x" (Vint z)
                                                  (add_arg "y" (Vptr p) (post_ret (t:=TeleO) (Vint q, emp%I)))))).
  Proof.
    rewrite /add_with_Elaborate/add_arg_Elaborate/post_ret_Elaborate/elaborated/elaborated_arg/Tint_ElaborateArg/Tptr_ElaborateArg/=.
  Abort.

End tests.
