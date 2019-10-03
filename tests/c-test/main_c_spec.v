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

Section with_Σ.
Context {Σ:gFunctors}.

Local Notation trace := (trace (Σ:=Σ)) (only parsing).
Local Notation function_spec := (function_spec Σ) (only parsing).

Definition putstr_spec := ltac:(
  specify (exact "putstr") main_c.module
          (fun p =>
               \with (s : string) (k : itree PutStr unit)
               \pre _at (_eq p) (c_string s) **
                    trace (Vis (putstr s) (fun _ => k))
               \post _at (_eq p) (c_string s) ** trace k)).

Fixpoint printEach (ls : list string) : itree PutStr unit :=
  match ls with
  | nil => Ret tt
  | l :: ls => Vis (putstr l) (fun _ => printEach ls)
  end.

Definition main_spec : function_spec :=
  main.main_spec (fun m =>
                    \pre trace (printEach m)
                    \post @trace.trace _ PutStr (Ret tt)).

Definition spec :=
  Linking.module putstr_spec (_at (_global "main") (ticptr main_spec)).

Export lib.array lib.trace.

End with_Σ.
