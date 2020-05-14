Require Import stdpp.base.

(* note: this can be more easily defined with [Applicative] *)
Class Traversable (T : Type -> Type) : Type :=
{ traverse : forall `{MBind M, MRet M} {A B}, (A -> M B) -> T A -> M (T B) }.
