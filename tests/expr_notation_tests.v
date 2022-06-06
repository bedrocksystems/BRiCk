(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Ascii ZArith.

Require Import bedrock.prelude.base.
From bedrock.lang.cpp Require Import ast notations code_notations.

Section TestExprNotations.
  Context (ty : type) (e : Expr).

  #[local] Definition Econst_ref_lname : Expr := Econst_ref (Lname "FooBarBaz") ty.
  #[local] Definition Econst_ref_gname : Expr := Econst_ref (Gname "FooBarBaz") ty.
  Print Econst_ref_lname. Print Econst_ref_gname.

  #[local] Definition Evar_lname : Expr := Evar (Lname "FooBarBaz") ty.
  #[local] Definition Evar_gname : Expr := Evar (Gname "FooBarBaz") ty.
  Print Evar_lname. Print Evar_gname.

  #[local] Definition A_ascii : Z := Evaluate (Z.of_N (Ascii.N_of_ascii "A"%char)).
  #[local] Definition newline_ascii : Z := Evaluate (Z.of_N (Ascii.N_of_ascii "010"%char)).
  #[local] Definition Echar_letter : Expr := Echar (Unfold A_ascii A_ascii) ty.
  #[local] Definition Echar_newline : Expr := Echar (Unfold newline_ascii newline_ascii) ty.
  Print Echar_letter. Print Echar_newline.

  #[local] Definition Estring_1 : Expr := Estring "FooBarBazQux" ty.
  Print Estring_1.

  #[local] Definition Eint_1 : Expr := Eint 42 ty.
  #[local] Definition Eint_2 : Expr := Eint 314 ty.
  Print Eint_1. Print Eint_2.

  #[local] Definition Ebool_true : Expr := Ebool true.
  #[local] Definition Ebool_false : Expr := Ebool false.
  Print Ebool_true. Print Ebool_false.

  Check Uminus. Check Unot. Check Ubnot. Check (Uother "FooBarBaz").

  #[local] Definition Eunop_1 : Expr := Eunop Uminus (Eint 42 ty) ty.
  #[local] Definition Eunop_2 : Expr := Eunop Unot (Ebool false) ty.
  #[local] Definition Eunop_3 : Expr := Eunop Ubnot (Eint 314 ty) ty.
  #[local] Definition Eunop_4 : Expr := Eunop (Uother "FooBarBaz") e ty.
  Print Eunop_1. Print Eunop_2. Print Eunop_3. Print Eunop_4.

  Check Badd. Check Band. Check Bcmp. Check Bdiv. Check Beq. Check Bge.
  Check Bgt. Check Ble. Check Blt. Check Bmul. Check Bneq.
  Check Bor. Check Bmod. Check Bshl. Check Bsub.
  Check Bxor. Check Bdotp. Check Bdotip.

  #[local] Definition Ebinop_custom_Bdotp_nowrap
    : Expr := Ebinop Bdotp
                     (Evar (Lname "FooBarBaz") ty)
                     (Evar (Lname "Qux") ty)
                     ty.
  #[local] Definition Ebinop_custom_Bdotip_nowrap
    : Expr := Ebinop Bdotip
                     (Evar (Lname "FooBarBaz") ty)
                     (Evar (Lname "Qux") ty)
                     ty.
  #[local] Definition Ebinop_custom_Bshr_nowrap
    : Expr := Ebinop Bshr
                     (Eint 314 ty)
                     (Eint 42 ty)
                     ty.
  Print Ebinop_custom_Bdotp_nowrap.
  Print Ebinop_custom_Bdotip_nowrap.
  Print Ebinop_custom_Bshr_nowrap.

  #[local] Definition Ebinop_custom_Bdotp_wrap
    : Expr := Ebinop Bdotp
                     (Evar (Lname "FooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBaz") ty)
                     (Evar (Lname "Qux") ty)
                     ty.
  #[local] Definition Ebinop_custom_Bdotip_wrap
    : Expr := Ebinop Bdotip
                     (Evar (Lname "FooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBaz") ty)
                     (Evar (Lname "Qux") ty)
                     ty.
  #[local] Definition Ebinop_custom_Bshr_wrap
    : Expr := Ebinop Bshr
                     (Eint 31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679 ty)
                     (Eint 42 ty)
                     ty.
  Print Ebinop_custom_Bdotp_wrap.
  Print Ebinop_custom_Bdotip_wrap.
  Print Ebinop_custom_Bshr_wrap.

  #[local] Definition Ebinop_default_Badd
    : Expr := Ebinop Badd (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Band
    : Expr := Ebinop Band (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bcmp
    : Expr := Ebinop Bcmp (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bdiv
    : Expr := Ebinop Bdiv (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Beq
    : Expr := Ebinop Beq (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bge
    : Expr := Ebinop Bge (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bgt
    : Expr := Ebinop Bgt (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Ble
    : Expr := Ebinop Ble (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Blt
    : Expr := Ebinop Blt (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bmul
    : Expr := Ebinop Bmul (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bneq
    : Expr := Ebinop Bneq (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bor
    : Expr := Ebinop Bor (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bmod
    : Expr := Ebinop Bmod (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bshl
    : Expr := Ebinop Bshl (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bsub
    : Expr := Ebinop Bsub (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Ebinop_default_Bxor
    : Expr := Ebinop Bxor (Eint 42 ty) (Eint 314 ty) ty.
  Print Ebinop_default_Badd. Print Ebinop_default_Band. Print Ebinop_default_Bcmp.
  Print Ebinop_default_Bdiv. Print Ebinop_default_Beq. Print Ebinop_default_Bge.
  Print Ebinop_default_Bgt. Print Ebinop_default_Ble. Print Ebinop_default_Blt.
  Print Ebinop_default_Bmul. Print Ebinop_default_Bneq. Print Ebinop_default_Bor.
  Print Ebinop_default_Bmod. Print Ebinop_default_Bshl.
  Print Ebinop_default_Bsub. Print Ebinop_default_Bxor.

  #[local] Definition Ebinop_compound_1
    : Expr := Ebinop Bshl
                     (Ebinop Bshr
                             (Eint 42 ty)
                             (Eint 2 ty) ty)
                     (Eint 314 ty) ty.
  #[local] Definition Ebinop_compound_2
    : Expr := Ebinop Bmul
                     (Eint (-1)%Z ty)
                     (Ebinop Bsub
                             (Ebinop Bxor
                                     (Evar (Gname "FOOBAR") ty)
                                     (Ebinop Bdiv
                                             (Eint 42 ty)
                                             (Eint 2 ty) ty)
                                     ty)
                             (Eint 314 ty) ty)
                     ty.
  Print Ebinop_compound_1. Print Ebinop_compound_2.

  #[local] Definition Eread_ref_lname : Expr := Eread_ref (Evar (Lname "FooBarBaz") ty).
  #[local] Definition Eread_ref_gname : Expr := Eread_ref (Evar (Gname "FooBarBaz") ty).
  Print Eread_ref_lname. Print Eread_ref_gname.

  #[local] Definition Ederef_Evar : Expr := Ederef (Evar (Lname "Qux") ty) ty.
  #[local] Definition Ederef_Enull : Expr := Ederef Enull ty.
  Print Ederef_Evar. Print Ederef_Enull.

  #[local] Definition Eaddrof_Evar_lname : Expr := Eaddrof (Evar (Lname "Qux") ty).
  #[local] Definition Eaddrof_Evar_gname : Expr := Eaddrof (Evar (Gname "Qux") ty).
  Print Eaddrof_Evar_lname. Print Eaddrof_Evar_gname.

  #[local] Definition Eassign_1 : Expr := Eassign (Evar (Lname "pi") ty) (Eint 314 ty) ty.
  Print Eassign_1.

  #[local] Definition Eassign_op_custom_Bshr : Expr
    := Eassign_op Bshr (Evar (Lname "foo") ty) (Eint 21 ty) ty.
  Print Eassign_op_custom_Bshr.

  #[local] Definition Eassign_op_default_Badd
    : Expr := Eassign_op Badd (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Eassign_op_default_Band
    : Expr := Eassign_op Band (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Eassign_op_default_Bdiv
    : Expr := Eassign_op Bdiv (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Eassign_op_default_Bmul
    : Expr := Eassign_op Bmul (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Eassign_op_default_Bor
    : Expr := Eassign_op Bor (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Eassign_op_default_Bmod
    : Expr := Eassign_op Bmod (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Eassign_op_default_Bshl
    : Expr := Eassign_op Bshl (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Eassign_op_default_Bsub
    : Expr := Eassign_op Bsub (Eint 42 ty) (Eint 314 ty) ty.
  #[local] Definition Eassign_op_default_Bxor
    : Expr := Eassign_op Bxor (Eint 42 ty) (Eint 314 ty) ty.
  Print Eassign_op_default_Badd. Print Eassign_op_default_Band. Print Eassign_op_default_Bdiv.
  Print Eassign_op_default_Bmul. Print Eassign_op_default_Bor. Print Eassign_op_default_Bmod.
  Print Eassign_op_default_Bshl. Print Eassign_op_default_Bsub. Print Eassign_op_default_Bxor.

  #[local] Definition Epreinc_1 : Expr := Epreinc e ty.
  #[local] Definition Epreinc_2 : Expr := Epreinc (Eint 41 ty) ty.
  Print Epreinc_1. Print Epreinc_2.

  #[local] Definition Epostinc_1 : Expr := Epostinc e ty.
  #[local] Definition Epostinc_2 : Expr := Epostinc (Eint 41 ty) ty.
  Print Epostinc_1. Print Epostinc_2.

  #[local] Definition Epredec_1 : Expr := Epredec e ty.
  #[local] Definition Epredec_2 : Expr := Epredec (Eint 41 ty) ty.
  Print Epredec_1. Print Epredec_2.

  #[local] Definition Epostdec_1 : Expr := Epostdec e ty.
  #[local] Definition Epostdec_2 : Expr := Epostdec (Eint 41 ty) ty.
  Print Epostdec_1. Print Epostdec_2.

  #[local] Definition Eseqand_1 : Expr := Eseqand (Ebool true) (Ebool false).
  #[local] Definition Eseqand_2 : Expr := Eseqand (Ebool true) (Eseqand (Ebool false) (Ebool true)).
  Print Eseqand_1. Print Eseqand_2.

  #[local] Definition Eseqor_1 : Expr := Eseqor (Ebool true) (Ebool false).
  #[local] Definition Eseqor_2 : Expr := Eseqor (Ebool true) (Eseqor (Ebool false) (Ebool true)).
  Print Eseqor_1. Print Eseqor_2.

  #[local] Definition Ecomma_1 : Expr := Ecomma Lvalue e e.
  #[local] Definition Ecomma_2 : Expr := Ecomma Lvalue (Epreinc (Evar (Lname "baz") ty) ty) e.
  Print Ecomma_1. Print Ecomma_2.

  #[local] Definition Ecall_nil_1 : Expr := Ecall e []%list ty.
  #[local] Definition Ecall_nil_2 : Expr := Ecall (Evar (Gname "fn") ty) []%list ty.
  Print Ecall_nil_1. Print Ecall_nil_2.

  #[local] Definition Ecall_cons_nowrap_1 : Expr := Ecall e [Eint 42 ty; Ebool false]%list ty.
  #[local] Definition Ecall_cons_nowrap_2 : Expr := Ecall (Evar (Gname "fn") ty) [Eint 42 ty; Ebool false]%list ty.
  Print Ecall_cons_nowrap_1. Print Ecall_cons_nowrap_2.

  (* TODO (JH): Fix up the printing boxes s.t. the widths/splits correspond (and extra
     breaks aren't inserted; cf. [Ecall_cons_wrap_2].
   *)
  #[local] Definition Ecall_cons_wrap_1 : Expr := Ecall e [Eint 42 ty; Ebool false; Estring "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz" ty]%list ty.
  #[local] Definition Ecall_cons_wrap_2 : Expr := Ecall (Evar (Gname "fn") ty) [Eint 42 ty; Ebool false; Estring "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz" ty]%list ty.
  Print Ecall_cons_wrap_1. Print Ecall_cons_wrap_2.

  #[local] Definition Ecast_elide_1 (cast : Cast) (vc : ValCat) := Ecast cast vc e ty.
  #[local] Definition Ecast_elide_2 (cast : Cast) (vc : ValCat) := Ecast cast vc (Eint 314 ty) ty.
  Print Ecast_elide_1. Print Ecast_elide_2.

  #[local] Definition Emember_1 : Expr := Emember Lvalue (Evar (Lname "foo") (Tnamed "foo")) (Build_field "foo" "bar") ty.
  Print Emember_1.

  #[local] Definition Emember_call_nil_1 : Expr := Emember_call (inl ("fn"%bs, Direct, ty)) Lvalue e []%list ty.
  #[local] Definition Emember_call_nil_2 : Expr := Emember_call (inl ("fn"%bs, Direct, ty)) Lvalue (Evar (Gname "foo") ty) []%list ty.
  Print Emember_call_nil_1. Print Emember_call_nil_2.

  #[local] Definition Emember_call_cons_nowrap_1 : Expr := Emember_call (inl ("fn"%bs, Direct, ty)) Lvalue e [Eint 42 ty; Ebool false]%list ty.
  #[local] Definition Emember_call_cons_nowrap_2 : Expr := Emember_call (inl ("fn"%bs, Direct, ty)) Lvalue (Evar (Gname "foo") ty) [Eint 42 ty; Ebool false]%list ty.
  Print Emember_call_cons_nowrap_1. Print Emember_call_cons_nowrap_2.

  (* TODO (JH): Fix up the printing boxes s.t. the widths/splits correspond (and extra
     breaks aren't inserted; cf. [Ecall_cons_wrap_2].
   *)
  #[local] Definition Emember_call_cons_wrap_1 : Expr := Emember_call (inl ("fn"%bs, Direct, ty)) Lvalue e [Eint 42 ty; Ebool false; Estring "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz" ty]%list ty.
  #[local] Definition Emember_call_cons_wrap_2 : Expr := Emember_call (inl ("fn"%bs, Direct, ty)) Lvalue (Evar (Gname "foo") ty) [Eint 42 ty; Ebool false; Estring "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz" ty]%list ty.
  Print Emember_call_cons_wrap_1. Print Emember_call_cons_wrap_2.

  #[local] Definition Esubscript_1 : Expr := Esubscript e (Eint 42 ty) ty.
  #[local] Definition Esubscript_2 : Expr := Esubscript (Evar (Lname "foo") ty) (Eint 314 ty) ty.
  Print Esubscript_1. Print Esubscript_2.

  #[local] Definition Esize_of_type_1 : Expr := Esize_of (inl ty) ty.
  #[local] Definition Esize_of_type_2 : Expr := Esize_of (inl (Tptr (Tnum W8 Unsigned))) ty.
  #[local] Definition Esize_of_type_3 : Expr := Esize_of (inl (Tnamed "Foo")) ty.
  Print Esize_of_type_1. Print Esize_of_type_2. Print Esize_of_type_3.

  #[local] Definition Esize_of_Expr_1 : Expr := Esize_of (inr e) ty.
  #[local] Definition Esize_of_Expr_2 : Expr := Esize_of (inr (Eint 314 ty)) ty.
  #[local] Definition Esize_of_Expr_3 : Expr := Esize_of (inr (Evar (Lname "foo") ty)) ty.
  Print Esize_of_Expr_1. Print Esize_of_Expr_2. Print Esize_of_Expr_3.

  #[local] Definition Ealign_of_type_1 : Expr := Ealign_of (inl ty) ty.
  #[local] Definition Ealign_of_type_2 : Expr := Ealign_of (inl (Tptr (Tnum W8 Unsigned))) ty.
  #[local] Definition Ealign_of_type_3 : Expr := Ealign_of (inl (Tnamed "Foo")) ty.
  Print Ealign_of_type_1. Print Ealign_of_type_2. Print Ealign_of_type_3.

  #[local] Definition Ealign_of_Expr_1 : Expr := Ealign_of (inr e) ty.
  #[local] Definition Ealign_of_Expr_2 : Expr := Ealign_of (inr (Eint 314 ty)) ty.
  #[local] Definition Ealign_of_Expr_3 : Expr := Ealign_of (inr (Evar (Lname "foo") ty)) ty.
  Print Ealign_of_Expr_1. Print Ealign_of_Expr_2. Print Ealign_of_Expr_3.

  #[local] Definition Eoffset_of_1 : Expr := Eoffset_of (Oo_Field (Build_field "Foo" "bar")) ty.
  Print Eoffset_of_1.

  #[local] Definition Econstructor_nil : Expr := Econstructor "Foo" []%list ty.
  Print Econstructor_nil.

  #[local] Definition Econstructor_cons_nowrap : Expr := Econstructor "Foo" [Eint 42 ty; Ebool false]%list ty.
  Print Econstructor_cons_nowrap.

  (* TODO (JH): Fix up the printing boxes s.t. the widths/splits correspond (and extra
     breaks aren't inserted; cf. [Ecall_cons_wrap_2].
   *)
  #[local] Definition Econstructor_cons_wrap : Expr := Econstructor "Qux::Zop" [Eint 42 ty; Ebool false; Estring "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz" ty]%list ty.
  Print Econstructor_cons_wrap.

  #[local] Definition Eimplicit_1 : Expr := Eimplicit e.
  #[local] Definition Eimplicit_2 : Expr := Eimplicit (Econstructor "Foo" []%list ty).
  Print Eimplicit_1. Print Eimplicit_2.

  #[local] Definition Eimplicit_init_1 : Expr := Eimplicit_init ty.
  #[local] Definition Eimplicit_init_2 : Expr := Eimplicit_init (Tnum W8 Unsigned).
  Print Eimplicit_init_1. Print Eimplicit_init_2.

  #[local] Definition Eif_1 : Expr := Eif (Ebool true) (Ecall (Evar (Lname "fn") ty) []%list ty) (Eassign_op Bmul (Evar (Lname "foo") ty) (Evar (Lname "bar") ty) ty) ty.
  Print Eif_1.

  Check (Ethis ty). Check Enull.

  #[local] Definition Einitlist_nil_1 : Expr := Einitlist []%list None ty.
  #[local] Definition Einitlist_nil_2 : Expr := Einitlist []%list None (Tnum W64 Unsigned).
  Print Einitlist_nil_1. Print Einitlist_nil_2.

  #[local] Definition Einitlist_cons_no_wrap_no_default_1 : Expr := Einitlist [Eint 42 ty; Ebool false]%list None ty.
  #[local] Definition Einitlist_cons_no_wrap_no_default_2 : Expr := Einitlist [Eint 42 ty; Ebool false]%list None (Tnum W64 Unsigned).
  Print Einitlist_cons_no_wrap_no_default_1. Print Einitlist_cons_no_wrap_no_default_2.

  #[local] Definition Einitlist_cons_wrap_no_default_1 : Expr := Einitlist [Eint 42 ty; Ebool false; Estring "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz" ty]%list None ty.
  #[local] Definition Einitlist_cons_wrap_no_default_2 : Expr := Einitlist [Eint 42 ty; Ebool false; Estring "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz" ty]%list None (Tnum W64 Unsigned).
  Print Einitlist_cons_wrap_no_default_1. Print Einitlist_cons_wrap_no_default_2.

  #[local] Definition Einitlist_cons_no_wrap_default_1 : Expr := Einitlist [Eint 42 ty; Ebool false]%list (Some (Eint 314 ty)) ty.
  #[local] Definition Einitlist_cons_no_wrap_default_2 : Expr := Einitlist [Eint 42 ty; Ebool false]%list (Some (Eint 314 ty)) (Tnum W64 Unsigned).
  Print Einitlist_cons_no_wrap_default_1. Print Einitlist_cons_no_wrap_default_2.

  #[local] Definition Einitlist_cons_wrap_default_1 : Expr := Einitlist [Eint 42 ty; Ebool false; Estring "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz" ty]%list (Some (Eint 314 ty)) ty.
  #[local] Definition Einitlist_cons_wrap_default_2 : Expr := Einitlist [Eint 42 ty; Ebool false; Estring "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz" ty]%list (Some (Eint 314 ty)) (Tnum W64 Unsigned).
  Print Einitlist_cons_wrap_default_1. Print Einitlist_cons_wrap_default_2.

  #[local] Definition Enew_nonarray_nil_1 : Expr := Enew ("fn"%bs, ty) []%list ty None (Some e).
  #[local] Definition Enew_nonarray_nil_2 : Expr := Enew ("fn"%bs, ty) []%list (Tnum W8 Unsigned) None None.
  Print Enew_nonarray_nil_1. Print Enew_nonarray_nil_2.

  #[local] Definition Enew_nonarray_cons_1 : Expr := Enew ("fn"%bs, ty) [Eint 42 ty; Ebool false]%list ty None (Some e).
  #[local] Definition Enew_nonarray_cons_2 : Expr := Enew ("fn"%bs, ty) [Eint 42 ty; Ebool false]%list (Tnamed "Foo") None None.
  Print Enew_nonarray_cons_1. Print Enew_nonarray_cons_2.

  #[local] Definition Enew_array_nil_1 : Expr := Enew ("fn"%bs, ty) []%list ty (Some (Eint 314 ty)) (Some e).
  #[local] Definition Enew_array_nil_2 : Expr := Enew ("fn"%bs, ty) []%list (Tnum W8 Unsigned) (Some (Eint 314 ty)) None.
  Print Enew_array_nil_1. Print Enew_array_nil_2.

  #[local] Definition Edelete_nonarray_1 : Expr := Edelete false ("fn"%bs, ty) e ty.
  #[local] Definition Edelete_nonarray_2 : Expr := Edelete false ("fn"%bs, ty) (Evar (Lname "foo") ty) ty.
  Print Edelete_nonarray_1. Print Edelete_nonarray_2.

  #[local] Definition Edelete_array_1 : Expr := Edelete true ("fn"%bs, ty) e ty.
  #[local] Definition Edelete_array_2 : Expr := Edelete true ("fn"%bs, ty) (Evar (Lname "foo") ty) ty.
  Print Edelete_array_1. Print Edelete_array_2.

  #[local] Definition Eandclean_1 : Expr := Eandclean e.
  #[local] Definition Eandclean_2 : Expr := Eandclean (Evar (Lname "foo") ty).
  Print Eandclean_1. Print Eandclean_2.

  #[local] Definition Ematerialize_temp_1 : Expr := Ematerialize_temp e.
  #[local] Definition Ematerialize_temp_2 : Expr := Ematerialize_temp (Evar (Lname "foo") ty).
  Print Ematerialize_temp_1. Print Ematerialize_temp_2.

  Check Bin_alloca. Check Bin_alloca_with_align. Check Bin_launder. Check Bin_expect.
  Check Bin_unreachable. Check Bin_trap. Check Bin_bswap16. Check Bin_bswap32.
  Check Bin_bswap64. Check Bin_bswap128. Check Bin_bzero. Check Bin_ffs. Check Bin_ffsl.
  Check Bin_ffsll. Check Bin_clz. Check Bin_clzl. Check Bin_clzll. Check Bin_ctz.
  Check Bin_ctzl. Check Bin_ctzll. Check Bin_popcount. Check Bin_popcountl.
  Check Bin_unknown "__builtin__foobarbaz"%bs.

  #[local] Definition Ebuiltin_alloca : Expr := Ebuiltin Bin_alloca ty.
  #[local] Definition Ebuiltin_alloca_with_align : Expr := Ebuiltin Bin_alloca_with_align ty.
  #[local] Definition Ebuiltin_launder : Expr := Ebuiltin Bin_launder ty.
  #[local] Definition Ebuiltin_expect : Expr := Ebuiltin Bin_expect ty.
  #[local] Definition Ebuiltin_unreachable : Expr := Ebuiltin Bin_unreachable ty.
  #[local] Definition Ebuiltin_trap : Expr := Ebuiltin Bin_trap ty.
  #[local] Definition Ebuiltin_bswap16 : Expr := Ebuiltin Bin_bswap16 ty.
  #[local] Definition Ebuiltin_bswap32 : Expr := Ebuiltin Bin_bswap32 ty.
  #[local] Definition Ebuiltin_bswap64 : Expr := Ebuiltin Bin_bswap64 ty.
  #[local] Definition Ebuiltin_bswap128 : Expr := Ebuiltin Bin_bswap128 ty.
  #[local] Definition Ebuiltin_bzero : Expr := Ebuiltin Bin_bzero ty.
  #[local] Definition Ebuiltin_ffs : Expr := Ebuiltin Bin_ffs ty.
  #[local] Definition Ebuiltin_ffsl : Expr := Ebuiltin Bin_ffsl ty.
  #[local] Definition Ebuiltin_ffsll : Expr := Ebuiltin Bin_ffsll ty.
  #[local] Definition Ebuiltin_clz : Expr := Ebuiltin Bin_clz ty.
  #[local] Definition Ebuiltin_clzl : Expr := Ebuiltin Bin_clzl ty.
  #[local] Definition Ebuiltin_clzll : Expr := Ebuiltin Bin_clzll ty.
  #[local] Definition Ebuiltin_ctz : Expr := Ebuiltin Bin_ctz ty.
  #[local] Definition Ebuiltin_ctzl : Expr := Ebuiltin Bin_ctzl ty.
  #[local] Definition Ebuiltin_ctzll : Expr := Ebuiltin Bin_ctzll ty.
  #[local] Definition Ebuiltin_popcount : Expr := Ebuiltin Bin_popcount ty.
  #[local] Definition Ebuiltin_popcountl : Expr := Ebuiltin Bin_popcountl ty.
  #[local] Definition Ebuiltin_unknown : Expr := Ebuiltin (Bin_unknown "__builtin_foobarbaz"%bs) ty.
  Print Ebuiltin_alloca. Print Ebuiltin_alloca_with_align. Print Ebuiltin_launder.
  Print Ebuiltin_expect. Print Ebuiltin_unreachable. Print Ebuiltin_trap.
  Print Ebuiltin_bswap16. Print Ebuiltin_bswap32. Print Ebuiltin_bswap64.
  Print Ebuiltin_bswap128. Print Ebuiltin_bzero. Print Ebuiltin_ffs. Print Ebuiltin_ffsl.
  Print Ebuiltin_ffsll. Print Ebuiltin_clz. Print Ebuiltin_clzl. Print Ebuiltin_clzll.
  Print Ebuiltin_ctz. Print Ebuiltin_ctzl. Print Ebuiltin_ctzll. Print Ebuiltin_popcount.
  Print Ebuiltin_popcountl. Print Ebuiltin_unknown.

  #[local] Definition Eva_arg_1 : Expr := Eva_arg e ty.
  #[local] Definition Eva_arg_2 : Expr := Eva_arg (Eint 217 ty) ty.
  Print Eva_arg_1. Print Eva_arg_2.

  #[local] Definition Epseudo_destructor_1 : Expr := Epseudo_destructor ty e.
  #[local] Definition Epseudo_destructor_2 : Expr := Epseudo_destructor ty (Eint 217 ty).
  Print Epseudo_destructor_1. Print Epseudo_destructor_2.

  Check (Eunsupported "This was an unsupported operation" ty).
End TestExprNotations.
