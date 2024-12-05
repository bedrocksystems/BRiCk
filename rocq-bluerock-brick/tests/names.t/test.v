Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.syntax.
Require bedrock.lang.cpp.syntax.supported.


Require test.test_cpp.

Eval vm_compute in supported.check.translation_unit test_cpp.module.

Definition is_Some {T} (a : option T) : Prop :=
  match a with
  | None => False
  | Some _ => True
  end.

(* check that the function exists *)
Goal is_Some $ test_cpp.module.(symbols) !!
        (Ninst (Nscoped (Nscoped (Ninst (Nglobal (Nfunction function_qualifiers.N (Nf "run") ( Tint :: Tnullptr :: nil)))
              ((Atype Tint) :: (Atype Tnullptr) :: nil)) (Nanon 0)) (Nfunction function_qualifiers.Nc (Nop OOCall) (Tlong :: Tint :: Tnullptr :: nil)))
        ((Atype Tlong) :: nil)).
Proof. exact I. Qed.
