(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import bytestring.


(** Generic Notation *)
Reserved Notation "'\with' x .. y X"
   (at level 10, x closed binder, y closed binder, X at level 200, right associativity,
    format "'[v' '\with'     '[hv' x  ..  y ']'  '//' X ']'").

Reserved Notation "'\withT' ts <- t X"
  (at level 200, ts name, X at level 200, right associativity,
   format "'[v' '\withT'     ts <- t  '//' X ']'").

Reserved Notation "'\prepost' pp X"
  (at level 10, pp at level 100, X at level 200, right associativity,
   format "'[v' '[hv  ' '\prepost'  '/' pp ']' '//' X ']'").

Reserved Notation "'\prepost{' x .. y '}' pp X"
  (at level 10, x binder, y binder, pp at level 100, X at level 200, right associativity,
   format "'[v' '[hv  ' '\prepost{' x  ..  y '}'  '/' pp ']' '//' X ']'").

Reserved Notation "'\let' x ':=' e X"
  (at level 10, x pattern, e at level 150, X at level 200, right associativity,
   format "'[v' '[hv  ' '\let'      x  ':='  '/' e ']' '//' X ']'").

Reserved Notation "'\require' pre X"
  (at level 10, pre at level 200, X at level 200, left associativity,
   format "'[v' '[' '\require'  pre ']' '//' X ']'").

Reserved Notation "'\require{' x .. y } pre X"
  (at level 10, pre at level 200, x binder, y binder, X at level 200, left associativity,
   format "'[v' '\require{' x  ..  y '}'  pre  '//' X ']'").

Reserved Notation "'\persist' pre X"
  (at level 10, pre at level 200, X at level 200, left associativity,
   format "'[v' '[' '\persist'  pre ']' '//' X ']'").

Reserved Notation "'\persist{' x .. y } pre X"
  (at level 10, pre at level 200, x binder, y binder, X at level 200, left associativity,
   format "'[v' '\persist{' x  ..  y '}'  pre  '//' X ']'").

Reserved Notation "'\pre' pre X"
  (at level 10, pre at level 200, X at level 200, left associativity,
   format "'[v' '[  ' '\pre'  '/' pre  ']' '//' X ']'").

Reserved Notation "'\pre{' x .. y '}' pp X"
  (at level 10, x binder, y binder, pp at level 100, X at level 200, right associativity,
   format "'[v' '[hv  ' '\pre{' x  ..  y '}'  '/' pp ']' '//' X ']'").

Reserved Notation "'\post*' post X"
  (at level 10, post at level 200, X at level 200, left associativity,
   format "'[v' '[  ' '\post*'  '/' post  ']' '//' X ']'").

Reserved Notation "'\post*{' x .. y '}' post X"
  (at level 10, x binder, y binder, post at level 100, X at level 200, right associativity,
   format "'[v' '[hv  ' '\post*{' x  ..  y '}'  '/' post ']' '//' X ']'").

(** Post-conditions with Return *)
Reserved Notation "'\post' { x .. y } [ r ] post"
  (at level 10, r at level 200, no associativity, x binder, y binder,
   post at level 200,
   format "'[v' '\post' { x  ..  y } [ r ]  '//'          '[hv ' post ']' ']'").

Reserved Notation "'\post' { } [ r ] post"
  (at level 10, r at level 200, no associativity,
   post at level 200).

Reserved Notation "'\post' [ r ] post"
  (at level 10, r at level 200, no associativity,
   post at level 200,
   format "'[v' '\post' [ r ]  '//'          '[hv ' post ']' ']'").

Reserved Notation "'\post' post"
  (at level 10, no associativity,
   post at level 200,
   format "'[v' '\post'     '[hv ' post ']' ']'").

Reserved Notation "'\exact' wpp"
  (at level 10, wpp at level 200).

(** Arguments *)
Reserved Notation "'\args' ls X"
  (at level 10, X at level 200, right associativity,
   format "'[v' '[hv  ' '\args'     '/' ls  ']' '//' X ']'").

Reserved Notation "'\args{' x .. y '}' ls X"
  (at level 10, x binder, y binder, X at level 200, right associativity,
   format "'[v' '[hv  ' '\args{' x  ..  y '}'  '/' ls  ']' '//' X ']'").

Reserved Notation "'\arg' nm v X"
  (at level 10, nm at level 0, v at level 0, X at level 200, right associativity,
   format "'[v' '\arg'  nm  v  '//' X ']'").

Reserved Notation "'\arg{' x .. y } nm v X"
  (at level 10, nm at level 0, v at level 0, x binder, y binder, X at level 200, right associativity,
   format "'[v' '\arg{' x  ..  y '}'  nm  v  '//' X ']'").
