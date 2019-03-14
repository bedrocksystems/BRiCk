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

Require C.main_c.
Require Import C.array.

Inductive itree (E : Type -> Type) (T : Type) : Type :=
| Ret (_ : T)
| Vis {u} (_ : E u) (_ : u -> itree E T)
| Tau (_ : itree E T).
Arguments Ret {_ _} _.
Arguments Vis {_ _ _} _ _.
Arguments Tau {_ _} _.

Parameter trace : forall {E : Type -> Type}, itree E unit -> mpred.

Variant PutStr : Type -> Type :=
| putstr (_ : string) : PutStr unit.

Definition args_array (p : val) (ls : list string) : mpred :=
  tarray (Tpointer (Qmut T_char))
    (fun (p : val) (v : string) =>
       Exists s : val,
         tptsto (Tpointer (Qmut T_char)) p s ** c_string s v) p
    ls.


Definition putstr_spec : function_spec' :=
  SFunction (Qmut Tvoid) (Qmut (Tpointer (Qmut T_char)) :: nil)
            (fun p =>
               {| wpp_with := string * itree PutStr unit
                ; wpp_pre '(s,k) := c_string p s **
                                    trace (Vis (putstr s) (fun _ => k))
                ; wpp_post '(s,k) _ := c_string p s ** trace k
                |}).

Fixpoint printEach (ls : list string) : itree PutStr unit :=
  match ls with
  | nil => Ret tt
  | l :: ls => Vis (putstr l) (fun _ => printEach ls)
  end.

Definition main_spec : function_spec' :=
  SFunction (Qmut T_int)
            (Qmut T_int :: Qmut
                  (Qconst (Tpointer
                             (Qmut
                                (Tpointer
                                   (Qmut T_char))))) :: nil)
      (fun argc argv =>
         {| wpp_with := list string
          ; wpp_pre m :=
              [| Vint (Z.of_nat (length m)) = argc |] **
              args_array argv m **
              trace (printEach m) **
              [| has_type argc T_int |]
          ; wpp_post m (r : val) := [| r = Vint 0 |] **
              args_array argv m ** @trace PutStr (Ret tt)
         |}).

Definition spec (resolve : _) :=
  ti_cglob' (resolve:=resolve) "_Z6putstr" putstr_spec -*
  ti_cglob' (resolve:=resolve) "_Z4main" main_spec.

Export C.array.