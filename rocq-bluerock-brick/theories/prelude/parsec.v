(*
 * Copyright (C) BlueRock Security Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.prelude.
Require Import bedrock.prelude.bytestring.

Require Export bedrock.upoly.upoly.
Require Export bedrock.upoly.parsec.

#[local] Set Universe Polymorphism.
#[local] Unset Universe Minimization ToSet.

Import UPoly.
Section char_parsec.
  Context {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.
  Notation M := (M Byte.byte F).

  Definition run_bs {T} (p : M T) (b : bs) : F (option (bs * T)) :=
    fmap (M:=eta option) (fun '(a,b) => (BS.parse a, b)) <$> run p (BS.print b).

  Definition run_full_bs {T} (p : M T) (b : bs) : F (option T) :=
    run_full p (BS.print b).

  Definition digit : M Byte.byte :=
    char (fun x => bool_decide (Byte.to_N "0" ≤ Byte.to_N x ≤ Byte.to_N "9")%N).

  Definition exact_bs (b : bs) : M unit :=
    exact $ BS.print b.

  Definition exact_char (b : Byte.byte) : M unit :=
    fmap (fun _ => ()) $ char (fun b' => bool_decide (b = b')).

  Definition quoted {U V T} (pre : M U) (post : M V) (p : M T) : M T :=
    (fun _ x _ => x) <$> pre <*> p <*> post.

  Definition ws : M unit :=
    const () <$> (star $ char (fun x => strings.Ascii.is_space $ Ascii.ascii_of_byte x)).

  Definition ignore_ws {T} (p : M T) : M T :=
    quoted ws ws p.

  (* A note about effects:
     [not p] will roll-back monadic changes of parsec, but will *not* roll back
     monadic changes in [F]. Therefore, users should be careful about [F] effects
     in [p]. Generally, [p] should be effect free in [F].
   *)
End char_parsec.
