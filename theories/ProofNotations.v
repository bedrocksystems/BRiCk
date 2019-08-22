(* Notations for verification conditions
 *)
Require Import Cpp.Sem.Wp.

Notation "'wp_rhs' ( e )" := (@wp_rhs _ _ _ e _)
         (at level 0, only printing).
Notation "'wp_lhs' ( e )" := (@wp_lhs _ _ _ e _)
         (at level 0, only printing).
Notation "'wp' ( e )" := (@wp _ _ _ e _)
         (at level 0, only printing).
Notation "'wpe' ( e )" := (@wpe _ _ _ _ e _)
         (at level 0, only printing).
