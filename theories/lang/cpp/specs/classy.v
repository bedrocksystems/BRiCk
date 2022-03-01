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

Require Import iris.bi.bi.
Require Import bedrock.prelude.bytestring_core.
Require Import bedrock.lang.bi.only_provable.
Require Import bedrock.lang.cpp.specs.spec_notations.

Section with_prop.
  Context {PROP : bi} {spec_car : Type}.

  Class SpecGen : Type :=
    { add_pre : PROP -> spec_car -> spec_car
    ; add_post : PROP -> spec_car -> spec_car
    ; add_with : forall {T : Type@{bi.u2}}, (T -> spec_car) -> spec_car
    ; add_prepost (P : PROP) (S : spec_car) : spec_car :=
      add_pre P (add_post P S)
    ; add_require (P : Prop) : spec_car -> spec_car :=
      add_pre (only_provable P)
    ; add_persist (P : PROP) : spec_car -> spec_car :=
      add_pre (bi_intuitionistically P)
    }.

  Class WithArg {ARG : Type} : Type :=
    { add_arg : ARG -> spec_car -> spec_car
    ; add_args : list ARG -> spec_car -> spec_car
    }.

  Class WithPost {RESULT : Type} : Type :=
    { post_car : Type
    ; start_post : post_car -> spec_car
    ; post_with : forall T : Type@{bi.u2}, (T -> post_car) -> post_car
    ; post_ret : RESULT -> PROP -> post_car
    }.

  (** [HasVoid T] means that the type [T] has an interpretation for
    [\post ..] (i.e. something to fill in the return value)
   *)
  Class HasVoid (T : Type) : Type := { _void : T }.

  Definition post_void {RESULT} {WP : @WithPost RESULT} {HV : HasVoid RESULT} (P : PROP) : post_car :=
    post_ret _void P.

  Definition add_named_arg `{WA : WithArg ARG} (nm : bs) : ARG -> spec_car -> spec_car :=
    add_arg.

  Definition let_pre_spec {T : Type} (x : T) : T := x.
  Definition exact_spec {T : Type} (x : T) : T := x.

End with_prop.
Arguments SpecGen : clear implicits.
Arguments WithArg : clear implicits.
Arguments WithPost : clear implicits.

Arguments post_with {PROP spec RESULT _} [T] _ : rename.
Arguments add_with {PROP spec _} [T] _ : rename.

#[global] Instance unit_HasVoid : HasVoid unit := { _void := tt }.

Strategy expand
   [ add_pre add_require add_arg add_args add_post add_prepost start_post post_with post_ret post_void ].
(** Make sure to list all identity functions above. And in the same order, for clarity. *)
Strategy expand
   [ let_pre_spec exact_spec ].

Declare Scope pre_spec_scope.
Delimit Scope pre_spec_scope with fspec.
Delimit Scope pre_spec_scope with pre_spec.

Notation "'\with' x .. y X" :=
  (add_with (fun x => .. (add_with (fun y => X%pre_spec)) ..)).

Notation "'\prepost' pp X" := (add_prepost pp%I X%pre_spec).

Notation "'\prepost{' x .. y '}' pp X" :=
  (add_with (fun x => .. (add_with (fun y => add_prepost pp%I X%pre_spec)) ..)).

Notation "'\let' x ':=' e X" := (let_pre_spec (let x := e in X%pre_spec)).

Notation "'\arg' nm v X" := (add_named_arg nm%bs v X%pre_spec).

Notation "'\arg{' x .. y } nm v X" :=
  (add_with (fun x => .. (add_with (fun y => add_named_arg nm%bs v X%pre_spec)) ..)).

Notation "'\args' v X" := (add_args v X%pre_spec).

Notation "'\args{' x .. y } v X" :=
  (add_with (fun x => .. (add_with (fun y => add_args v X%pre_spec)) ..)).

Notation "'\require' pre X" := (add_require pre X%pre_spec).

Notation "'\require{' x .. y } pre X" :=
  (add_with (fun x => .. (add_with (fun y => add_require pre X%pre_spec)) ..)).

Notation "'\persist' pre X" := (add_persist pre%I X%pre_spec).

Notation "'\persist{' x .. y } pre X" :=
  (add_with (fun x => .. (add_with (fun y => add_persist pre%I X%pre_spec)) ..)).

Notation "'\pre' pre X" := (add_pre pre%I X%pre_spec).

Notation "'\pre{' x .. y '}' pp X" :=
  (add_with (fun x => .. (add_with (fun y => add_pre pp%I X%pre_spec)) ..)).

Notation "'\post*{' x .. y '}' post X" :=
  (add_with (fun x => .. (add_with (fun y => add_post post%I X%pre_spec)) ..)).

Notation "'\post*' post X" := (add_post post%I X%pre_spec).

Notation "'\post' { x .. y } [ r ] post" :=
  (start_post (post_with (fun x => .. (post_with (fun y => post_ret r post%I)) ..))).

Notation "'\post' [ r ] post" :=
  (start_post (post_ret r post%I)).

Notation "'\post' { } [ r ]  post" := (\post[r] post).

Notation "'\post' post" := (start_post (post_void post%I)).

Notation "'\exact' wpp" := (exact_spec wpp).
