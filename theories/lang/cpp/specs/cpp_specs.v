(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import bytestring telescopes.
From bedrock.lang.cpp.semantics Require Import values.
From bedrock.lang.cpp.logic Require Import pred.
From bedrock.lang.cpp.specs Require Import spec_notations classy.

Require Import bedrock.lang.cpp.specs.wp_spec_compat.

Set Printing Universes.

#[global] Instance val_HasVoid : HasVoid val := { _void := Vvoid }.

#[deprecated(since="2022-02-13",note="use [WpSpec]")]
Notation WithPrePostG := WpSpec (only parsing).
Bind Scope pre_spec_scope with WpSpec.

Notation WpSpec_cpp_val := (WpSpec mpredI val val) (only parsing).
Notation WpSpec_cpp_ptr := (WpSpec mpredI ptr ptr) (only parsing).

#[deprecated(since="2022-02-13",note="use [WpSpec_cpp_ptr]")]
Notation WithPrePost PROP := (WpSpec PROP ptr ptr) (only parsing).

(* These two classes provide automatic coercions between [ptr] and [val] and [Z] and [val]
 *)
#[global] Instance val_ptr_WithArg {spec} (WA : WithArg spec val) : WithArg spec ptr :=
  {| classy.add_arg p := classy.add_arg (Vptr p)
   ; classy.add_args p := classy.add_args (List.map Vptr p) |}.
#[global] Instance val_Z_WithArg {spec} (WA : WithArg spec val) : WithArg spec Z :=
  {| classy.add_arg p := classy.add_arg (Vint p)
   ; classy.add_args p := classy.add_args (List.map Vint p) |}.

(* only needed for examples *)
Require Import bedrock.lang.cpp.logic.

Section with_Σ.
  Context `{Σ : cpp_logic ti}.

  #[local] Notation WPP := (WpSpec_cpp_val).

  Succeed Definition _1 : WPP :=
    \pre emp
    \post  emp.

  Succeed Definition _2 : WPP :=
    \with (I J : mpred) (p : ptr) (R : Qp -> Qp -> nat -> Rep)
    \prepost emp
    \require True
    \require{x} x = 1
    \arg{n (nn: nat)} "foo" (Vint n)
    \with (z : nat) (a : nat)
    \prepost emp
    \prepost{q1 q2} p |-> R q1 q2 0
    \pre{q3 q4} p |-> R q3 q4 0
    \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
    \post {x} [ Vint x ] emp.

  Succeed Definition _3 : WPP :=
   \with (I J : mpred)
   \with  (a : nat)
   \prepost emp
   \with (z : nat)
   \prepost emp
   \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post{r}[ r ] emp.

  Succeed Definition _4 : WPP :=
   \with (I J : mpred) (n : nat)
   \with  (a : nat)
   \let x := 3%nat
   \with (lm : nat * nat)
   \let (l,m) := lm
   \require l+m = 3
   \prepost emp
   \persist emp
   \persist{n1} [| n1 = 1 |]
   \persist{n2} [| n2 = 1 |]%N
   \persist{z} [| z = 1 |]%Z
   \with (z : nat)
   \arg{(zz : Z)} "foo" (Vint zz)
   \prepost emp
   \with (zzz : Type)
   \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post emp.

  Succeed Definition _5 : WPP :=
    \pre emp ** Exists y : nat, [| y = 3 |]
    \post{}[Vptr nullptr] emp.

  Succeed Definition _6 : WPP :=
    \pre |==> True ** |={∅,⊤}=> False
    \post{}[Vptr nullptr] emp.

End with_Σ.

Export classy.
Export bedrock.lang.cpp.specs.wp_spec_compat.
