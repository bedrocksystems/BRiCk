(* Notations for verification conditions
 *)
Require Import Cpp.Sem.Wp.
Require Import Cpp.Sem.

Notation "'::wpL' ( e )" := (@wp_lval _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpX' ( e )" := (@wp_xval _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpPR' ( e )" := (@wp_prval _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpPRᵢ' ( e )" := (@wp_init _ _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpGL' ( e )" := (@wp_glval _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpR' ( e )" := (@wp_rval _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpS' ( e )" := (@wp _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpE' ( e )" := (@wpe _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpD' ( t n = e )" := (@wp_decl _ _ _ n t e _ _ _)
         (at level 0, only printing).

Definition wp_lval' := @wp_lval.
Definition wp_prval' := @wp_prval.
Definition wp_xval' := @wp_xval.
Definition wp_glval' := @wp_glval.
Definition wp_rval' := @wp_rval.
Definition wp_init' := @wp_init.
Definition wp' := @wp.
Definition wpe' := @wpe.
Definition wp_decl' := @wp_decl.

Ltac show :=
  change @wp_lval with @wp_lval';
  change @wp_rval with @wp_rval';
  change @wp_glval with @wp_glval';
  change @wp_init with @wp_init';
  change @wp_decl with @wp_decl';
  change @wp_prval with @wp_prval';
  change @wp_xval with @wp_xval';
  change @wpe with @wpe';
  change @wp with @wp'.

(* note: tactics such as [simplifying] will not work in "visible"
 * mode
 *)
Ltac hide :=
  change @wp_lval' with @wp_lval;
  change @wp_rval' with @wp_rval;
  change @wp_glval' with @wp_glval;
  change @wp_prval' with @wp_prval;
  change @wp_xval' with @wp_xval;
  change @wp_init' with @wp_init;
  change @wp_decl' with @wp_decl;
  change @wpe' with @wpe;
  change @wp' with @wp.
