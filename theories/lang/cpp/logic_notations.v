(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(* Notations for verification conditions
 *)
Require Import bedrock.lang.cpp.logic.

Module Compact.
Notation "'::wpL' { e }" := (@wp_lval _ _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpX' { e }" := (@wp_xval _ _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpPR' { e }" := (@wp_prval _ _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpPRᵢ' { e }" := (@wp_init _ _ _ _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpGL' { e }" := (@wp_glval _ _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpR' { e }" := (@wp_rval _ _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpS' { e }" := (@wp _ _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpE' { e }" := (@wpe _ _ _ _ _ _ e _)
         (at level 0, only printing).
Notation "'::wpD' { t n = e }" := (@wp_decl _ _ _ _ _ n t e _ _ _)
         (at level 0, only printing).
End Compact.

Module Verbose.
Notation "'::wpL' { e } Q" := (@wp_lval _ _ _ _ _ e Q)
         (at level 0, Q at level 200, only printing).
Notation "'::wpX' { e } Q" := (@wp_xval _ _ _ _ _ e Q)
         (at level 0, Q at level 200, only printing).
Notation "'::wpPR' { e } Q" := (@wp_prval _ _ _ _ _ e Q)
         (at level 0, Q at level 200, only printing).
Notation "'::wpPRᵢ' { e } Q" := (@wp_init _ _ _ _ _ _ _ e Q)
         (at level 0, Q at level 200, only printing).
Notation "'::wpGL' { e } Q" := (@wp_glval _ _ _ _ _ e Q)
         (at level 0, Q at level 200, only printing).
Notation "'::wpR' { e } Q" := (@wp_rval _ _ _ _ _ e Q)
         (at level 0, Q at level 200, only printing).
Notation "'::wpS' { e } Q" := (@wp _ _ _ _ _ e Q)
         (at level 0, Q at level 200, only printing).
Notation "'::wpE' { e } Q" := (@wpe _ _ _ _ _ _ e Q)
         (at level 0, Q at level 200, only printing).
Notation "'::wpD' { t n = e } Q" := (@wp_decl _ _ _ _ _ n t e _ _ Q)
         (at level 0, Q at level 200, only printing).
End Verbose.
