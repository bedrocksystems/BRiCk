(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From Cpp Require Import
     Auto.
From Cpp.lib Require Import
     array main trace.

Require C.main_c.



Variant PutStr : Type -> Type :=
| putstr (_ : string) : PutStr unit.



Definition putstr_spec : function_spec' :=
  SFunction (Qmut Tvoid) (Qmut (Tpointer (Qmut T_char)) :: nil)
            (fun p =>
               {| wpp_with := string * itree PutStr unit
                ; wpp_pre '(s,k) := c_string s p **
                                    trace (Vis (putstr s) (fun _ => k))
                ; wpp_post '(s,k) _ := c_string s p ** trace k
                |}).

Fixpoint printEach (ls : list string) : itree PutStr unit :=
  match ls with
  | nil => Ret tt
  | l :: ls => Vis (putstr l) (fun _ => printEach ls)
  end.

Definition main_spec : function_spec' :=
  main.main_spec (fun m =>
                    {| wpp_with := unit
                     ; wpp_pre _ := trace (printEach m)
                     ; wpp_post _ r := @trace PutStr (Ret tt)
                     |}).

Definition spec (resolve : _) :=
  ti_cglob' (resolve:=resolve) "putstr" putstr_spec -*
  ti_cglob' (resolve:=resolve) "main" main_spec.

Export lib.array lib.trace.