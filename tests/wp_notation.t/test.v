(*
 * Copyright (c) 2022-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import ZArith.

From bedrock.lang.cpp Require Import notations code_notations logic logic.builtins.

Module WpTestDefns.
  Context (ti : biIndex) (Σ : cpp_logic ti) (σ : genv) (tu : translation_unit) (q_c : bool) (ρ : region)
          (v : val) (p p' p'' p''' this : ptr)
          (free : FreeTemps) (E : epred) (K : Kpred).
  #[local] Notation cv := (types.QC).
  #[local] Notation ty := (types.Tptr types.Tvoid).
  #[local] Notation e := (expr.Ebinop expr.Badd
                                      (expr.Evar (expr.Lname "foo") types.Tint)
                                      (expr.Evar (expr.Lname "bar") types.Tint)
                                      types.Tint).
  #[local] Notation s := (stmt.Sseq [ stmt.Sexpr e
                                    ; stmt.Sbreak
                                    ; stmt.Scontinue
                                    ; stmt.Sexpr e
                                    ; stmt.Sexpr e
                                    ; stmt.Sreturn None
                                    ; stmt.Sreturn (Some e)]%list).

  Section Statements.
    Definition NOTATION_wp_nowrap :=
      wp tu (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))) s K.
    Definition NOTATION_wp_wrap :=
      wp tu (Rbind "qux" p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) (Sseq [s; s; s; s]) K.

    Definition NOTATION_wp_decl_nowrap (decl : VarDecl) Q :=
      wp_decl tu (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty)))
                  decl Q.
  End Statements.

  Section Special.
    Definition NOTATION_wp_atomic_nil M Q :=
      wp_atom M expr.AO__atomic_load ty [] Q.
    Definition NOTATION_wp_atomic_cons_nowrap M Q :=
      wp_atom M expr.AO__atomic_load ty [Vundef; Vundef; Vundef] Q.
    Definition NOTATION_wp_atomic_cons_wrap M Q :=
      wp_atom M expr.AO__atomic_load ty [Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vint 1123784018923740981723509817230984710298374098123740981723490817230984710293840891273489012734089] Q.

    Definition NOTATION_wp_builtin_nil Q :=
      wp_builtin expr.Bin_popcount ty [] Q.
    Definition NOTATION_wp_builtin_cons_nowrap Q :=
      wp_builtin expr.Bin_popcount ty [Vundef; Vundef; Vundef] Q.
    Definition NOTATION_wp_builtin_cons_wrap Q :=
      wp_builtin expr.Bin_popcount ty [Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vint 1123784018923740981723509817230984710298374098123740981723490817230984710293840891273489012734089] Q.
  End Special.

  Section Cleanup.
    Definition NOTATION_wp_destroy_val_nowrap :=
      wp_destroy_val tu cv ty p E.
    Definition NOTATION_wp_destroy_val_wrap (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : ptr) :=
      wp_destroy_val tu cv ty aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa E.

    Definition NOTATION_destroy_val_nowrap :=
      destroy_val tu ty p E.
    Definition NOTATION_destroy_val_wrap (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : ptr) :=
      destroy_val tu ty aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa E.

    Definition NOTATION_interp_nowrap :=
      interp tu free E.
    Definition NOTATION_interp_wrap :=
      interp tu (FreeTemps.id |*| FreeTemps.id |*| FreeTemps.id |*| FreeTemps.id |*| FreeTemps.id |*| FreeTemps.id |*| FreeTemps.id |*| FreeTemps.id |*| FreeTemps.id |*| FreeTemps.id |*| FreeTemps.id)%free E.
  End Cleanup.

  Section Expressions.
    Definition NOTATION_wp_lval_nowrap Q :=
      wp_lval tu (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))) e Q.
    Definition NOTATION_wp_lval_wrap Q :=
      wp_lval tu (Rbind "qux" p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) e Q.

    Definition NOTATION_wp_init_nowrap Q :=
      wp_init tu (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))) ty this e Q.
    Definition NOTATION_wp_init_wrap Q :=
      wp_init tu (Rbind "qux" p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) ty this e Q.

    Definition NOTATION_wp_prval_nowrap Q :=
      wp_prval tu (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))) e Q.
    Definition NOTATION_wp_prval_wrap Q :=
      wp_prval tu (Rbind "qux" p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) e Q.

    Definition NOTATION_wp_operand_nowrap Q :=
      wp_operand tu (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))) e Q.
    Definition NOTATION_wp_operand_wrap Q :=
      wp_operand tu (Rbind "qux" p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) e Q.

    Definition NOTATION_wp_xval_nowrap Q :=
      wp_xval tu (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))) e Q.
    Definition NOTATION_wp_xval_wrap Q :=
      wp_xval tu (Rbind "qux" p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) e Q.

    Definition NOTATION_wp_glval_nowrap Q :=
      wp_glval tu (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))) e Q.
    Definition NOTATION_wp_glval_wrap Q :=
      wp_glval tu (Rbind "qux" p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) e Q.

    Definition NOTATION_wp_discard_nowrap Q :=
      wp_discard tu (Rbind "foo" p (Remp (Some this) None ty)) e Q.
    Definition NOTATION_wp_discard_wrap Q :=
      wp_discard tu (Rbind "qux" p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) e Q.

    Definition NOTATION_wp_func tu F ls Q :=
      wp_func tu F ls Q.

    Definition NOTATION_wp_method tu M ls Q :=
      wp_method tu M ls Q.

    Definition NOTATION_wp_ctor tu C ls Q :=
      wp_ctor tu C ls Q.

    Definition NOTATION_wp_dtor tu D ls Q :=
      wp_dtor tu D ls Q.

    Definition NOTATION_wp_args_nowrap tys_ar es Q :=
      wp_args tu (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))) tys_ar es Q.
    Definition NOTATION_wp_args_wrap tys_ar es Q :=
      wp_args tu (Rbind "qux"%bs p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) tys_ar es Q.

    Definition NOTATION_wp_initialize_nowrap Q :=
      wp_initialize tu (Rbind "foo" p (Remp (Some this) None ty)) ty p e Q.
    Definition NOTATION_wp_initialize_wrap Q :=
      wp_initialize tu (Rbind "qux"%bs p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) ty p e Q.

    Definition NOTATION_wp_cond_nowrap T Q :=
      @wp_cond _ _ _ tu (Rbind "foo" p (Remp (Some this) None ty)) T Q.
    Definition NOTATION_wp_cond_wrap T Q :=
      @wp_cond _ _ _ tu (Rbind "qux"%bs p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty)))))T Q.

    Definition NOTATION_wp_call_nowrap ls Q :=
      wp_call tu (Rbind "foo" p (Remp (Some this) None ty)) ty Vundef ls Q.
    Definition NOTATION_wp_call_wrap ls Q :=
      wp_call tu (Rbind "qux"%bs p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) ty Vundef ls Q.

    Definition NOTATION_wp_mcall_nowrap ls Q :=
      wp_mcall tu (Rbind "foo" p (Remp (Some this) None ty)) Vundef p ty ty ls Q.
    Definition NOTATION_wp_mcall_wrap ls Q :=
      wp_mcall tu (Rbind "qux"%bs p''' (Rbind "baz"%bs p'' (Rbind "bar"%bs p' (Rbind "foo" p (Remp (Some this) None ty))))) Vundef p ty ty ls Q.
  End Expressions.
End WpTestDefns.

(* NOTE (JH): This doesn't test the printing of particular statements/expressions, but
   it does fix a concrete [region] to test the integration with those notations.
 *)
Section TEST_COMPACT_WP_NOTATIONS.
  Import Compact. Import WpTestDefns.
  Check "~~~TESTING COMPACT NOTATIONS~~~"%bs.

  Print NOTATION_wp_nowrap. Print NOTATION_wp_wrap.
  Print NOTATION_wp_decl_nowrap.

  Print NOTATION_wp_atomic_nil. Print NOTATION_wp_atomic_cons_nowrap. Print NOTATION_wp_atomic_cons_wrap.
  Print NOTATION_wp_builtin_nil. Print NOTATION_wp_builtin_cons_nowrap. Print NOTATION_wp_builtin_cons_wrap.

  Print NOTATION_wp_destroy_val_nowrap. Print NOTATION_wp_destroy_val_wrap.
  Print NOTATION_destroy_val_nowrap. Print NOTATION_destroy_val_wrap.
  Print NOTATION_interp_nowrap. Print NOTATION_interp_wrap.

  Print NOTATION_wp_lval_nowrap. Print NOTATION_wp_lval_wrap.
  Print NOTATION_wp_init_nowrap. Print NOTATION_wp_init_wrap.
  Print NOTATION_wp_prval_nowrap. Print NOTATION_wp_prval_wrap.
  Print NOTATION_wp_operand_nowrap. Print NOTATION_wp_operand_wrap.
  Print NOTATION_wp_xval_nowrap. Print NOTATION_wp_xval_wrap.
  Print NOTATION_wp_glval_nowrap. Print NOTATION_wp_glval_wrap.
  Print NOTATION_wp_discard_nowrap. Print NOTATION_wp_discard_nowrap.

  Print NOTATION_wp_func. Print NOTATION_wp_method. Print NOTATION_wp_ctor. Print NOTATION_wp_dtor.

  Print NOTATION_wp_args_nowrap. Print NOTATION_wp_args_wrap.
  Print NOTATION_wp_initialize_nowrap. Print NOTATION_wp_initialize_wrap.
  Print NOTATION_wp_call_nowrap. Print NOTATION_wp_call_wrap.
  Print NOTATION_wp_mcall_nowrap. Print NOTATION_wp_mcall_wrap.
End TEST_COMPACT_WP_NOTATIONS.

Section TEST_VERBOSE_WP_NOTATIONS.
  Import Verbose. Import WpTestDefns.
  Check "~~~TESTING Verbose NOTATIONS~~~"%bs.

  Print NOTATION_wp_nowrap. Print NOTATION_wp_wrap.
  Print NOTATION_wp_decl_nowrap.

  Print NOTATION_wp_atomic_nil. Print NOTATION_wp_atomic_cons_nowrap. Print NOTATION_wp_atomic_cons_wrap.
  Print NOTATION_wp_builtin_nil. Print NOTATION_wp_builtin_cons_nowrap. Print NOTATION_wp_builtin_cons_wrap.

  Print NOTATION_destroy_val_nowrap. Print NOTATION_destroy_val_wrap.
  Print NOTATION_interp_nowrap. Print NOTATION_interp_wrap.

  Print NOTATION_wp_lval_nowrap. Print NOTATION_wp_lval_wrap.
  Print NOTATION_wp_init_nowrap. Print NOTATION_wp_init_wrap.
  Print NOTATION_wp_prval_nowrap. Print NOTATION_wp_prval_wrap.
  Print NOTATION_wp_operand_nowrap. Print NOTATION_wp_operand_wrap.
  Print NOTATION_wp_xval_nowrap. Print NOTATION_wp_xval_wrap.
  Print NOTATION_wp_glval_nowrap. Print NOTATION_wp_glval_wrap.
  Print NOTATION_wp_discard_nowrap. Print NOTATION_wp_discard_nowrap.

  Print NOTATION_wp_func. Print NOTATION_wp_method. Print NOTATION_wp_ctor. Print NOTATION_wp_dtor.

  Print NOTATION_wp_args_nowrap. Print NOTATION_wp_args_wrap.
  Print NOTATION_wp_initialize_nowrap. Print NOTATION_wp_initialize_wrap.
  Print NOTATION_wp_call_nowrap. Print NOTATION_wp_call_wrap.
  Print NOTATION_wp_mcall_nowrap. Print NOTATION_wp_mcall_wrap.
End TEST_VERBOSE_WP_NOTATIONS.
