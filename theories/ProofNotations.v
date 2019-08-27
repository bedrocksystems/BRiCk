(* Notations for verification conditions
 *)
Require Import Cpp.Sem.Wp.

Notation "'::wpR' ( e )" := (@wp_rhs _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpL' ( e )" := (@wp_lhs _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpS' ( e )" := (@wp _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpE' ( e )" := (@wpe _ _ _ _ e _)
         (at level 0, only printing).

Definition wp_lhs' := @wp_lhs.
Definition wp_rhs' := @wp_rhs.
Definition wp' := @wp.
Definition wpe' := @wpe.

Ltac show :=
  change @wp_lhs with @wp_lhs';
  change @wp_rhs with @wp_rhs';
  change @wpe with @wpe';
  change @wp with @wp'.

(* note: tactics such as [simplifying] will not work in "visible"
 * mode
 *)
Ltac hide :=
  change @wp_lhs' with @wp_lhs;
  change @wp_rhs' with @wp_rhs;
  change @wpe' with @wpe;
  change @wp' with @wp.
