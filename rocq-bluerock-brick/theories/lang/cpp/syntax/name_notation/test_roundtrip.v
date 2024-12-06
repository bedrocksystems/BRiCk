(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.syntax.prelude.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.name_notation.parser.
Require Import bedrock.lang.cpp.syntax.name_notation.printer.
Require Import bedrock.lang.cpp.syntax.name_notation.test_cases.

Module Type TEST.
  Record RESULT (IN OUT : Set) : Set :=
  { input : IN ; expected : OUT ; observed : OUT }.

  Definition print_parse (nm : name) (str : bs) : list (RESULT _ _) :=
    let result : option (list Byte.byte)  := print_name nm in
    if bool_decide (result = Some (BS.print str)) then nil
    else {| input := nm ; expected := Some str ; observed := BS.parse <$> result |} :: nil.

  Definition parse_print (nm : name) (str : bs) : list (RESULT _ _) :=
    let result : option name := parse_name (BS.print str) in
    if bool_decide (result = Some nm) then nil
    else {| input := str ; expected := Some nm ; observed := result |} :: nil.

  Example TEST_print_parse : concat ((fun '(b,a) => print_parse a b) <$> canonical) = [].
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_parse_print : concat ((fun '(b,a) => parse_print a b) <$> (canonical ++ parse_only)) = [].
  Proof. vm_compute. reflexivity. Qed.
End TEST.
