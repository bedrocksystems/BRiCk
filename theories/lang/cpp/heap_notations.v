(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred.

Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic}.


  (* "points to" *)
  Structure AT : Type :=
  { AT_lhs    : Type
  ; AT_rhs    : Type
  ; AT_result : Type
  ; #[canonical=no] AT_at     :> AT_lhs -> AT_rhs -> AT_result
  }.
  #[global] Arguments AT_at {!AT} _ _ : rename.

  Canonical Structure mpred_ptr_AT : AT :=
    {| AT_lhs := ptr; AT_rhs := Rep; AT_result := mpred; AT_at := _at |}.

  Canonical Structure Rep_AT : AT :=
    {| AT_lhs := offset; AT_rhs := Rep; AT_result := Rep; AT_at o := _offsetR o |}.

  Canonical Structure mpred_val_AT : AT :=
    {| AT_lhs := val; AT_rhs := Rep; AT_result := mpred; AT_at v := _at (_eqv v) |}.

  Canonical Structure Rep_field_AT {σ : genv} : AT :=
    {| AT_lhs := field; AT_rhs := Rep; AT_result := Rep; AT_at v := _offsetR (o_field σ v) |}.

  (* coercions to [offset] *)
  Structure TO_OFFSET : Type :=
  { TO_OFFSET_from :> Type
  ; #[canonical=no] _to_offset : TO_OFFSET_from -> offset
  }.
  #[global] Arguments _to_offset {!TO_OFFSET} _ : rename.

  Canonical Structure TO_OFFSET_field {σ : genv} := {| TO_OFFSET_from := field; _to_offset := o_field σ |}.
  Canonical Structure TO_OFFSET_offset := {| TO_OFFSET_from := offset; _to_offset o := o |}.

  (* paths *)
  Structure DOT : Type :=
  { DOT_from : Type
  ; DOT_to : Type
  ; #[canonical=no] DOT_dot : offset -> DOT_from -> DOT_to
  }.
  #[global] Arguments DOT_dot {!DOT} _ _ : rename.

  Canonical Structure DOT_offset_loc : DOT :=
    {| DOT_from := ptr; DOT_to := ptr; DOT_dot o p := _offset_ptr p o |}.
  Canonical Structure DOT_field_offset {σ : genv} : DOT :=
    {| DOT_from := field; DOT_to := offset; DOT_dot o f := o_dot (o_field σ f) o |}.
  Canonical Structure DOT_offset_offset : DOT :=
    {| DOT_from := offset; DOT_to := offset; DOT_dot o1 o2 := o_dot o2 o1 |}.

  Canonical Structure DOT_val_offset : DOT :=
    {| DOT_from := val; DOT_to := ptr; DOT_dot o p := _offset_ptr (_eqv p) o |}.

End with_cpp.

(* notations *)
Local Ltac simple_refine ____x :=
  let x' := eval cbv beta iota delta
                 [ ____x id
                   AT_lhs AT_rhs AT_result  AT_at
                   Rep_AT mpred_val_AT mpred_ptr_AT Rep_field_AT
                   TO_OFFSET_from  _to_offset
                   TO_OFFSET_field TO_OFFSET_offset
                   DOT_from DOT_to DOT_dot
                   DOT_offset_loc DOT_field_offset DOT_offset_offset (* DOT_ptr_offset *) DOT_val_offset ] in ____x in
  exact x'.

Notation "l |-> r" := (match AT_at l r with
                       | ____x => ltac:(simple_refine ____x)
                       end)
  (at level 15, r at level 20, right associativity, only parsing).
Notation "l |-> r" := (_at l r)
  (at level 15, r at level 20, right associativity, only printing).
Notation "l |-> r" := (_offsetR l r)
  (at level 15, r at level 20, right associativity, only printing).

Notation "p ., o" := (match DOT_dot (_to_offset o) p with
                      | ____x => ltac:(simple_refine ____x)
                      end)
  (at level 11, left associativity, only parsing).

Notation "p .[ t ! n ]" := (match DOT_dot (o_sub _ t n) p with
                            | ____x => ltac:(simple_refine ____x)
                            end)
  (at level 11, left associativity, only parsing).
Notation ".[ t ! n ]" := ((o_sub _ t n))
  (at level 11, only parsing).

Notation "p ., o" := (_offset_ptr p o)
  (at level 11, left associativity, only printing,
   format "p  .,  o").
Notation "p ., o" := (o_dot p o)
  (at level 11, left associativity, only printing,
   format "p  .,  o").

Notation ".[ t ! n ]" := ((o_sub _ t n))
  (at level 11, no associativity, only printing, format ".[  t  !  n  ]").
Notation "p .[ t ! n ]" := (_offset_ptr (o_sub _ t n) p)
  (at level 11, left associativity, only printing, format "p  .[  t  '!'  n  ]").

(* Test suite *)
Section test_suite.

  Context {σ : genv} `{Σ : cpp_logic} (R : Rep) (f g : field) (o : offset) (l : ptr) (p : ptr) (v : val).

  Example _0 := |> l |-> R.

  Example _1 := |> l ., f |-> R.

  Example _2 := l |-> f |-> R.

  Example _3 := l .[ T_int ! 0 ] |-> R.

  Example _4 := l |-> f .[ T_int ! 0 ] |-> R.

  Example _5 := l .[ T_int ! 0 ] .[ T_int ! 3 ] |-> R.

  Example _6 := l ., f .[ T_int ! 0 ] ., g |-> R.

  Example _7 := l ., g ., f .[ T_int ! 1 ] .[ T_int ! 0 ] ., f |-> f |-> R.

  Example _8 := p ., g ., f .[ T_int ! 1 ] .[ T_int ! 0 ] ., f |-> .[ T_int ! 1 ] |-> R.

  Example _9 := o ., g ., f .[ T_int ! 1 ] .[ T_int ! 0 ] ., f |-> R.

  Example _10 := o ., g ., f .[ T_int ! 1 ] .[ T_int ! 0 ] ., f |-> R.

  Example _11 := o .[ T_int ! 1 ] |-> R.

  Example _12 := o .[ T_int ! 1 ] |-> R.

  Example _13 := v .[ T_int ! 1 ] |-> R.

  Example _14 := .[ T_int ! 1 ] |-> R.

  Example _15 := |> .[ T_int ! 1 ] |-> |> R.

  Fail Example _16 := l |-> ▷ R ∗ R.
  Fail Example _16 := l |-> |> R ** R. (* requires parsing as [(l |-> |> R) ** R] *)

  Fail Example _f := l |-> R ** R. (* requires parsing as [(l |-> R) ** R] *)

  Fail Example _BAD := l |-> R q.

End test_suite.
