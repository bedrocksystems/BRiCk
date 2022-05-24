(*
 * Copyright (c) 2019-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import bedrock.lang.cpp.ast.

#[local] Open Scope Z_scope.
#[local] Open Scope string_scope.

(* TODO (JH): Look into disabling (selective) scopes *)

Module Export TypeNotations.
  Declare Custom Entry CPP_type.
  Declare Scope CPP_type_scope.
  Delimit Scope CPP_type_scope with cpp_type.

  (* Injection from [constr] in case we're printing this at the top-level *)
  Notation "'{type:' ty '}'"
    := ty
       ( at level 100
       , ty custom CPP_type at level 200
       , format "'[hv' {type:  '/' ty } ']'")
     : CPP_type_scope.
  (* Injection into [constr] in case we're printing a subterm we don't recognize *)
  Notation "'{coq:' ty '}'"
    := ty
       ( in custom CPP_type at level 0
       , ty constr
       , format "'[hv' {coq:  '/' ty } ']'").

  (* [type_qualifiers] - leaf nodes get the highest priority *)
  Notation "'mut'" := QM (in custom CPP_type at level 0).
  Notation "'const'" := QC (in custom CPP_type at level 0).
  Notation "'volatile'" := QV (in custom CPP_type at level 0).
  Notation "'const' 'volatile'"
    := QCV
       ( in custom CPP_type at level 0
       , format "'[' const  volatile ']'").

  (* [Tqualified] types *)
  Notation "'mut' ty"
    := (Qmut ty)
       ( in custom CPP_type at level 100
       , ty custom CPP_type at level 200
       , right associativity
       , format "'[' mut  ty ']'").
  Notation "'const' ty"
    := (Qconst ty)
       ( in custom CPP_type at level 100
       , ty custom CPP_type at level 200
       , right associativity
       , format "'[' const  ty ']'").
  Notation "'volatile' ty"
    := (Qmut_volatile ty)
       ( in custom CPP_type at level 100
       , ty custom CPP_type at level 200
       , right associativity
       , format "'[' volatile  ty ']'").
  Notation "'const' 'volatile' ty"
    := (Qconst_volatile ty)
       ( in custom CPP_type at level 100
       , ty custom CPP_type at level 200
       , right associativity
       , format "'[' const  volatile  ty ']'").

  (* [Tnum] variants *)
  Notation "'int8'" := Ti8 (in custom CPP_type at level 0).
  Notation "'uint8'" := Tu8 (in custom CPP_type at level 0).
  Notation "'int16'" := Ti16 (in custom CPP_type at level 0).
  Notation "'uint16'" := Tu16 (in custom CPP_type at level 0).
  Notation "'int32'" := Ti32 (in custom CPP_type at level 0).
  Notation "'uint32'" := Tu32 (in custom CPP_type at level 0).
  Notation "'int64'" := Ti64 (in custom CPP_type at level 0).
  Notation "'uint64'" := Tu64 (in custom CPP_type at level 0).
  Notation "'int128'" := Ti128 (in custom CPP_type at level 0).
  Notation "'uint128'" := Tu128 (in custom CPP_type at level 0).

  (* The rest of the [type]s *)
  Notation "'ptr<' ty '>'"
    := (Tptr ty)
       ( in custom CPP_type at level 100
       , ty custom CPP_type at level 200
       , left associativity
       , format "'[' ptr< ty > ']'").
  Notation "'ref&<' ty '>'"
    := (Tref ty)
       ( in custom CPP_type at level 100
       , ty custom CPP_type at level 200
       , left associativity
       , format "'[' ref&< ty > ']'").
  Notation "'ref&&<' ty '>'"
    := (Trv_ref ty)
       ( in custom CPP_type at level 100
       , ty custom CPP_type at level 200
       , left associativity
       , format "'[' ref&&< ty > ']'").
  Notation "'void'" := Tvoid (in custom CPP_type at level 0).
  Notation "ty [ N ]"
    := (Tarray ty N)
       ( in custom CPP_type at level 80
       , ty custom CPP_type
       , N constr
       , format "'[' ty [ N ] ']'").
  Notation "nm" := (Tnamed nm) (in custom CPP_type at level 0, nm constr).
  Notation "'extern' cc '???()' '->' rty"
    := (@Tfunction cc Ar_Definite rty nil)
       ( in custom CPP_type at level 100
       , cc constr at level 0
       , rty custom CPP_type at level 200
       , format "'[' extern  cc  ???()  ->  rty ']'").
  Notation "'extern' cc '???(' aty1 , .. , aty2 ')' '->' rty"
    := (@Tfunction cc Ar_Definite rty (cons aty1 .. (cons aty2 nil) ..))
       ( in custom CPP_type at level 100
       , cc constr at level 0
       , rty custom CPP_type at level 200
       , aty1 custom CPP_type at level 200
       , aty2 custom CPP_type at level 200
       , format "'[' extern  cc  ???( '[hv' aty1 ,  '/' .. ,  '/' aty2 ']' )  ->  rty ']'").
  Notation "'extern' cc '???()(...)' '->' rty"
    := (@Tfunction cc Ar_Variadic rty nil)
       ( in custom CPP_type at level 100
       , cc constr at level 0
       , rty custom CPP_type at level 200
       , format "'[' extern  cc  ???()(...)  ->  rty ']'").
  Notation "'extern' cc '???(' aty1 , .. , aty2 ')(...)' '->' rty"
    := (@Tfunction cc Ar_Variadic rty (cons aty1 .. (cons aty2 nil) ..))
       ( in custom CPP_type at level 100
       , cc constr at level 0
       , rty custom CPP_type at level 200
       , aty1 custom CPP_type at level 200
       , aty2 custom CPP_type at level 200
       , format "'[' extern  cc  ???( '[hv' aty1 ,  '/' .. ,  '/' aty2 ']' )(...)  ->  rty ']'").
  Notation "'bool'" := Tbool (in custom CPP_type at level 0).
  Notation "'ptr[' nm ']<' ty '>'"
    := (Tmember_pointer nm ty)
       ( in custom CPP_type at level 100
       , nm constr
       , ty custom CPP_type
       , left associativity
       , format "'[' ptr[ nm ]< ty > ']'").
  Notation "'{float:' sz '}'"
    := (Tfloat sz)
       ( in custom CPP_type at level 0
       , sz constr
       , format "'[hv' {float:  '/' sz } ']'").
  Notation "'(' qual ty ')'"
    := (Tqualified qual ty)
       ( in custom CPP_type at level 100
       , qual custom CPP_type at level 0
       , ty custom CPP_type at level 200
       , format "'[' ( qual  ty ) ']'").
  Notation "'nullptr_t'" := Tnullptr (in custom CPP_type at level 0).
  Notation "'{arch:' nm '}'"
    := (Tarch None nm)
       ( in custom CPP_type at level 0
       , nm constr
       , format "'[hv' {arch:  '/' nm } ']'").
  Notation "'{arch:' nm ';' 'size:' sz '}'"
    := (Tarch (Some sz) nm)
       ( in custom CPP_type at level 0
       , sz constr
       , nm constr
       , format "'[hv' {arch:  nm ;  '/' size:  sz } ']'").
End TypeNotations.

Module Export cpp_expr.
  Declare Custom Entry cpp_expr.
  Declare Scope cppexpr_scope.
  Delimit Scope cppexpr_scope with cexpr.

  (* Quotation mechanism for [Expr]s *)
  Notation "'{expr:' e }" := e
    ( at level 200
    , e custom cpp_expr at level 200
    , format "'[hv' {expr:  '/' e } ']'"
    , only printing) : cppexpr_scope.
End cpp_expr.

Module Export cpp_stmt.
  Declare Custom Entry cpp_stmt.
  Declare Scope cppstmt_scope.
  Delimit Scope cppstmt_scope with cstmt.

  (* Quotation mechanism for [Stmt]s *)
  Notation "'{stmt:' s }" := s
    ( at level 200
    , s custom cpp_stmt at level 200
    , format "'[hv' {stmt:  '/' s } ']'"
    , only printing) : cppstmt_scope.
End cpp_stmt.

Module Export CodeNotations.
  Export TypeNotations.
  (* Export ExprNotations. *)
  (* Export StmtNotations. *)
End CodeNotations.

(* NOTE: The following [Section]s are only used for testing purposes; if you break one of these
   tests - or add a new notation - please update things accordingly.
 *)

Section TestTypeNotations.
  Import TypeNotations. #[local] Open Scope CPP_type_scope.

  #[local] Definition Notation_Tptr_1 : Tptr Tbool = {type: ptr<bool>} := eq_refl.
  #[local] Definition Notation_Tptr_2 ty : Tptr ty = {type: ptr<{coq: ty}>} := eq_refl.

  #[local] Definition Notation_Tref_1 : Tref Tbool = {type: ref&<bool>} := eq_refl.
  #[local] Definition Notation_Tref_2 ty : Tref ty = {type: ref&<{coq: ty}>} := eq_refl.

  #[local] Definition Notation_Trv_ref_1 : Trv_ref Tbool = {type: ref&&<bool>} := eq_refl.
  #[local] Definition Notation_Trv_ref_2 ty : Trv_ref ty = {type: ref&&<{coq: ty}>} := eq_refl.

  #[local] Definition Notation_Tref_Trv_ref ty : Tref (Trv_ref ty) = {type: ref&<ref&&<{coq: ty}>>} := eq_refl.
  #[local] Definition Notation_Trv_ref_Tref_1 ty : Trv_ref (Tref ty) = {type: ref&&<ref&<{coq: ty}>>} := eq_refl.

  #[local] Definition Notation_void : Tvoid = {type: void} := eq_refl.

  #[local] Definition Notation_Tarray_1 : Tarray Tnullptr 100 = {type: nullptr_t[100]} := eq_refl.
  #[local] Definition Notation_Tarray_2 ty n : Tarray ty n = {type: {coq: ty}[n]} := eq_refl.

  #[local] Definition Notation_Tnamed_1 : Tnamed "foobarbaz" = {type: "foobarbaz"} := eq_refl.
  #[local] Definition Notation_Tnamed_2 nm : Tnamed nm = {type: nm} := eq_refl.

  #[local] Definition Notation_Tfunction_novariadic_noargs_1 : Tfunction Tvoid nil = {type: extern CC_C ???() -> void} := eq_refl.
  #[local] Definition Notation_Tfunction_novariadic_noargs_2 rty : Tfunction rty nil = {type: extern CC_C ???() -> {coq: rty}} := eq_refl.

  #[local] Definition Notation_Tfunction_novariadic_args_nowrap_1 : Tfunction Tvoid (cons Tbool (cons Tnullptr nil)) = {type: extern CC_C ???(bool, nullptr_t) -> void} := eq_refl.
  #[local] Definition Notation_Tfunction_novariadic_noargs_nowrap_2 rty aty1 aty2 :
    Tfunction rty (cons aty1 (cons Tvoid (cons aty2 nil))) = {type: extern CC_C ???({coq: aty1}, void, {coq: aty2}) -> {coq: rty}} := eq_refl.

  #[local] Definition Notation_Tfunction_novariadic_args_wrap :
    Tfunction Tvoid (cons (Tnamed "askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk")
                          (cons (Tnamed "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") nil))
      = {type: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk",
                               "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") -> void} := eq_refl.

  #[local] Definition Notation_Tfunction_variadic_noargs_1 : Tfunction (ar:=Ar_Variadic) Tvoid nil = {type: extern CC_C ???()(...) -> void} := eq_refl.
  #[local] Definition Notation_Tfunction_variadic_noargs_2 rty : Tfunction (ar:=Ar_Variadic) rty nil = {type: extern CC_C ???()(...) -> {coq: rty}} := eq_refl.

  #[local] Definition Notation_Tfunction_variadic_args_nowrap_1 : Tfunction (ar:=Ar_Variadic) Tvoid (cons Tbool (cons Tnullptr nil)) = {type: extern CC_C ???(bool, nullptr_t)(...) -> void} := eq_refl.
  #[local] Definition Notation_Tfunction_variadic_noargs_nowrap_2 rty aty1 aty2 :
    Tfunction (ar:=Ar_Variadic) rty (cons aty1 (cons Tvoid (cons aty2 nil))) = {type: extern CC_C ???({coq: aty1}, void, {coq: aty2})(...) -> {coq: rty}} := eq_refl.

  #[local] Definition Notation_Tfunction_variadic_args_wrap :
    Tfunction (ar:=Ar_Variadic)
              Tvoid (cons (Tnamed "askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk")
                          (cons (Tnamed "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") nil))
      = {type: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk",
                               "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk")(...) -> void} := eq_refl.

  #[local] Definition Notation_Tbool : Tbool = {type: bool} := eq_refl.

  #[local] Definition Notation_Tmember_pointer_1 : Tmember_pointer "foobarbaz" Ti8 = {type: ptr["foobarbaz"]<int8>} := eq_refl.

  Section Qualifiers.
    #[local] Definition Notation_mut_1 : Qmut Tbool = {type: mut bool} := eq_refl.
    #[local] Definition Notation_mut_2 : Qmut (Qmut Tbool) = {type: mut (mut bool)} := eq_refl.

    #[local] Definition Notation_const_1 : Qconst Tbool = {type: const bool} := eq_refl.
    #[local] Definition Notation_const_2 : Qconst (Tptr (Qconst Tvoid)) = {type: const ptr<const void>} := eq_refl.

    #[local] Definition Notation_volatile_1 : Qmut_volatile Tbool = {type: volatile bool} := eq_refl.
    #[local] Definition Notation_volatile_2 : Qmut_volatile (Tptr (Qconst Tvoid)) = {type: volatile ptr<const void>} := eq_refl.

    #[local] Definition Notation_const_volatile_1 : Qconst_volatile Tbool = {type: const volatile bool} := eq_refl.
    #[local] Definition Notation_const_volatile_2 : Qconst_volatile (Tptr (Qconst_volatile Tvoid)) = {type: const volatile ptr<const volatile void>} := eq_refl.
  End Qualifiers.
End TestTypeNotations.

(* [cpp2v/theories/auto/cpp/notations/code.v@janno/code-notations], but that branch is out of date
Declare Custom Entry CPP.
Declare Custom Entry CPP_expr.
Declare Custom Entry CPP_stmt.

Declare Scope CPP_scope.
Declare Scope CPP_expr_scope.
Declare Scope CPP_stmt_scope.

Delimit Scope CPP_scope with cpp.
Delimit Scope CPP_expr_scope with cpp_expr.
Delimit Scope CPP_stmt_scope with cpp_stmt.

Module ExprNotations.
End ExprNotations.

Section TestExprNotations.
End TestExprNotations.

Module StmtNotations.
End StmtNotations.

Section TestStmtNotations.
End TestStmtNotations.

(* TODO (JH): Something to test that the signatures are correctly used for all notations *)

(** Notations for expressions *)
Notation "'{expr:' e }"
    := e
       ( at level 200
       , e custom cpp_expr at level 200
       , format "'[hv' {expr:  '/' e } ']'"
       , only printing) : cppexpr_scope.
(*
Notation "( e )" := e (in custom cpp_expr at level 0, e custom cpp_expr at level 200, only printing, format "'[' (  e  ) ']'").
*)



Notation "( ty ){ e1 , .. , e2 }"
    := (Einitlist (cons e1 .. (cons e2 nil) ..) _ ty)
       ( in custom cpp_expr at level 10
       , e1 custom cpp_expr at level 10
       , e2 custom cpp_expr at level 10
       , ty custom cpp_type
       , format "( ty ){  e1 ,  .. ,  e2  }"
       , only printing).
Notation "( ty ){ }"
    := (Einitlist nil _ ty)
       ( in custom cpp_expr at level 10
       , ty custom cpp_type
       , format "( ty ){  }"
       , only printing).



Notation "e '()'"
    := (Ecall e nil _)
       ( in custom cpp_expr at level 200
       , e custom cpp_expr at level 200
       , format "'[' e () ']'"
       , only printing).
Notation "e ( a1 , .. , a2 )"
    := (Ecall e (cons a1 (.. (cons a2 nil) .. )) _)
       ( in custom cpp_expr at level 200
       , e custom cpp_expr at level 200
       , a1 custom cpp_expr at level 200
       , a2 custom cpp_expr at level 200
       , format "e ( a1 ,  .. ,  a2 )"
       , only printing).


Notation "& e"
    := (Eaddrof e _)
       ( in custom cpp_expr at level 10
       , e custom cpp_expr at level 10
       , format "& e"
       , only printing).
Notation "* e"
    := (Ederef e _)
       ( in custom cpp_expr at level 10
       , e custom cpp_expr at level 10
       , format " * e"
       , only printing).
Notation "# v"
    := (Eint v%Z _)
       ( in custom cpp_expr at level 1
       , v constr
       , format "# v"
       , only printing).
Notation "# v"
    := (Ebool v)
       ( in custom cpp_expr at level 1
       , v constr
       , format "# v"
       , only printing).
Notation "# s"
    := (Estring s%bs _)
       ( in custom cpp_expr at level 1
       , s constr
       , format "# s"
       , only printing).


Notation "$ v"
    := (Econst_ref (Lname v%bs) _)
       ( in custom cpp_expr at level 1
       , v constr
       , format "$ v"
       , only printing).
Notation "$ :: v"
    := (Econst_ref (Gname v%bs) _)
       ( in custom cpp_expr at level 1
       , v constr
       , format "$ :: v"
       , only printing).


Notation "e --"
    := (Epostdec e _)
       ( in custom cpp_expr at level 5
       , format "e --"
       , only printing).
Notation "-- e"
    := (Epredec e _)
       ( in custom cpp_expr at level 5
       , e custom cpp_expr at level 5
       , format "-- e"
       , only printing).
Notation "e ++"
    := (Epostinc e _)
       ( in custom cpp_expr at level 5
       , format "e ++"
       , only printing).
Notation "++ e"
    := (Epreinc e _)
       ( in custom cpp_expr at level 5
       , e custom cpp_expr at level 5
       , format "++ e"
       , only printing).
Notation "e1 + e2"
    := (Ebinop Badd e1 e2 _)
       ( in custom cpp_expr at level 50
       , e1 custom cpp_expr
       , e2 custom cpp_expr at level 51
       , left associativity
       , only printing).
Notation "$ v"
    := (Evar (Lname v%bs) _)
       ( in custom cpp_expr at level 1
       , v constr
       , format "$ v"
       , only printing).
Notation "$ :: v"
    := (Evar (Gname v%bs) _)
       ( in custom cpp_expr at level 1
       , v constr
       , format "$ :: v"
       , only printing).

Notation "$ v"
    := (Eread_ref (Evar (Lname v%bs) _))
       ( in custom cpp_expr at level 1
       , v constr
       , format "$ v"
       , only printing).
Notation "$ :: v"
    := (Eread_ref (Evar (Gname v%bs) _))
       ( in custom cpp_expr at level 1
       , v constr
       , format "$ :: v"
       , only printing).


Notation "v = e"
    := (Eassign v e _)
       ( in custom cpp_expr at level 10
       , e custom cpp_expr at level 200
       , v custom cpp_expr
       , format "'[hv  ' v  =  '/' e ']'"
       , only printing).

(* QUESTION (JH): Is this the right level? *)
Notation "op x"
    := (Eunop op x _)
       ( in custom cpp_expr at level 75
       , x custom cpp_expr at level 200
       , op constr
       , format "'[' op x ']'"
       , only printing).
Notation "-" := (Uminus) (at level 200, only printing).
Notation "!" := (Unot) (at level 200, only printing).
Notation "~" := (Ubnot) (at level 200, only printing).
Notation "'{unop:' op }"
    := (Uother op)
       ( at level 200
       , format "'[' {unop:  op } ']'"
       , only printing).

Check (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid).

Notation "'{binop:' op ; x ; y }"
    := (Ebinop op x y _)
       ( in custom cpp_expr at level 1
       , op constr
       , x custom cpp_expr
       , y custom cpp_expr
       , format "'[hv   ' {binop:  '/' op ;  '/' x ;  '/' y } ']'"
       , only printing).


Notation "e"
    := (Ecast _ _ e _)
       ( in custom cpp_expr at level 0
       , e custom cpp_expr at level 200
       , only printing).


(** Notations for statements *)
Notation "'{stmt:' e }"
    := e
       ( at level 0
       , e custom cpp_stmt at level 200
       , format "{stmt:  e }"
       , only printing)
    : cppstmt_scope.

(* Statements that provide their own line break *)
(* NOTE (JH): statements will be enclosed in [{stmt: ...}], so we don't include curly
   braces here.
 *)
(* NOTE (JH): statements terminal [Stmt]s will have notations which insert semicolons
   (and the appropriate spacing after them).
 *)
Notation "'//' 'end' 'block'"
    := (Sseq nil)
       ( in custom cpp_stmt at level 0
       , format "'[' //  end  block ']'"
       , only printing).
Notation "s"
    := (Sseq (cons s nil))
       ( in custom cpp_stmt at level 0
       , s custom cpp_stmt at level 200
       , format "'[' s ']'"
       , only printing).
Notation "s1 .. s2 '//' 'end' 'block'"
    := (Sseq (cons s1 .. (cons s2 (nil)) ..))
       ( in custom cpp_stmt at level 0
       , s1 custom cpp_stmt at level 200
       , s2 custom cpp_stmt at level 200
       , format "'[v' s1 '/' .. '/' s2 '//' //  end  block ']'"
       , only printing).

(* Statements that provide their own line break *)
(* Notation "{ s1 ; .. ; s2 ; }" *)
(*     := (Sseq (cons s1 .. (cons s2 (nil)) ..)) *)
(*        ( in custom cpp_stmt at level 0 *)
(*        , s1 custom cpp_stmt at level 200 *)
(*        , s2 custom cpp_stmt at level 200 *)
(*        , format "'/' { '//'  '[v' s1 ';' '//' .. ';' '//' s2 ';' ']' '//' }" *)
(*        , only printing). *)

(* Notation "{ s1 ; .. ; s2 ; }" := (Sseq (@cons Stmt s1 .. (@cons Stmt s2 (@nil Stmt)) ..)) *)
(*                                (in custom cpp_stmt at level 0, *)
(*                                 s1 custom cpp_stmt at level 200, *)
(*                                 s2 custom cpp_stmt at level 200, *)
(*                                 only printing, *)
(*                                 format "'[  ' { '//' '[v' s1 ';' '//' .. ';' '//' s2 ';' ']' '//' ']' }"). *)

(* Notation "s1 ; .. ; s2 ;" := (Sseq (@cons Stmt s1 .. (@cons Stmt s2 (@nil Stmt)) ..)) *)
(*                                (in custom cpp_stmt_unbraced at level 0, *)
(*                                 s1 custom cpp_stmt at level 200, *)
(*                                 s2 custom cpp_stmt at level 200, *)
(*                                 only printing, *)
(*                                 format "'[v' '//' s1 ';' '//' .. ';' '//' s2 ';' ']' '//'"). *)

(* Notation "s" := (Sseq (@cons s nil)) (in custom cpp_stmt at level 0, s custom cpp_stmt). *)

(* Notation "s" := (s) (in custom cpp_stmt_unbraced at level 0, s custom cpp_stmt at level 200, only printing). *)

Notation "e ;"
    := (Sexpr _ e)
       ( in custom cpp_stmt at level 0
       , e custom cpp_expr at level 200
       , format "'[' e ; ']'"
       , only printing).

(* Check (Sexpr Lvalue (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)). *)

Notation "'continue;'"
    := Scontinue
       ( in custom cpp_stmt at level 0
       , format "'[' continue;  ']'"
       , only printing).
Notation "'break;'"
    := Sbreak
       ( in custom cpp_stmt at level 0
       , format "'[' break;  ']'"
       , only printing).
Notation "'return' e ;"
    := (Sreturn (Some (e)))
       ( in custom cpp_stmt at level 0
       , e custom cpp_expr at level 200
       , format "'[' return  e ;  ']'"
       , only printing).
Notation "'return;'"
    := (Sreturn None)
       ( in custom cpp_stmt at level 199
       , format "'[' return;  ']'"
       , only printing).

Notation "'//' 'empty' 'decl' 'block'"
    := (Sdecl nil)
       ( in custom cpp_stmt at level 0
       , format "//  empty  decl  block"
       , only printing).
Notation "d"
    := (Sdecl (cons d nil))
       ( in custom cpp_stmt at level 0
       , d custom cpp_stmt at level 200
       , format "'[' d ']'"
       , only printing).
Notation "d1 .. d2"
    := (Sdecl (cons d1 .. (cons d2 nil) ..))
       ( in custom cpp_stmt at level 0
       , d1 custom cpp_stmt at level 200
       , d2 custom cpp_stmt at level 200
       , format "'[v' d1 '/' .. '/' d2 ']' '//'"
       , only printing).

Notation "ty $ v = e ;"
    := (Dvar v ty (Some e))
       ( in custom cpp_stmt at level 0
       , e custom cpp_expr at level 200
       , ty custom cpp_type at level 200
       , v constr
       , format "'[' ty  $ v  =  e ; ']'"
       , only printing).


Notation "'if' ( t ) { thn } 'else' { els }"
    := (Sif None t thn els)
       ( in custom cpp_stmt at level 200
       , t custom cpp_expr at level 200
       , thn custom cpp_stmt at level 200
       , els custom cpp_stmt at level 200
       , format "'[hv' if ( t )  { '//'   thn '//' }  else  { '//'   els '//' } ']'"
       , only printing).
Notation "'while' ( t ) { bod }"
    := (Swhile None t bod)
       ( in custom cpp_stmt at level 200
       , t custom cpp_expr at level 200
       , bod at level 100
       , format "'[hv' while ( t )  { '//'   bod '//' } ']'"
       , only printing).
Notation "'while' ( t $ i = e ) { bod }"
    := (Swhile (Some (Dvar i t (Some e))) _ bod)
       ( in custom cpp_stmt at level 200
       , t custom cpp_type at level 100
       , e custom cpp_expr at level 200
       , bod at level 100
       , i constr
       , format "'[hv' while ( '[' t  $ i  =  e ']' )  { '//'   bod '//' } ']'"
       , only printing).


Notation "'do' { bod } 'while' ( e ) ;"
    := (Sdo bod e)
       ( in custom cpp_stmt at level 200
       , e custom cpp_expr at level 200
       , bod custom cpp_stmt at level 200
       , format "'[hv' do  { '//'   bod '//' }  while ( e ) ; ']'"
       , only printing).

(** Tests *)
Definition E (e : Expr) : Prop := True.
Definition S (s : Stmt) : Prop := True.
Definition T (t : type) : Prop := True.

Arguments E (_%cexpr).
Arguments S (_%cstmt).

(*
Check E (Ebinop Badd (Ederef (Eaddrof (Evar (Lname "hello") Tvoid)) Tvoid)
                (Eint 3%Z Tvoid) Tvoid).


Check S (Sseq (Sexpr Lvalue (Evar (Lname "hello") Tvoid) :: Scontinue :: Sbreak :: Sexpr Lvalue (Evar (Lname "world") Tvoid) :: Sif None (Evar (Lname "world") Tvoid) Scontinue Sbreak :: nil)).
*)

Notation "'if' ( t $ i = e ) { thn } 'else' { els }"
    := (Sif (Some (Dvar i%bs t (Some e))) _ thn els)
       ( in custom cpp_stmt at level 200
       , t custom cpp_type at level 100
       , e custom cpp_expr at level 200
       , thn custom cpp_stmt at level 200
       , els custom cpp_stmt at level 200
       , i constr
       , format "'[hv' if ( '[  ' t  $ i  =  e ']' )  { '//'   thn '//' }  else  { '//'   els '//' } ']'"
       , only printing).

Import List.ListNotations.
Set Printing Width 400.
Check
  S (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq [Scontinue;Scontinue;Scontinue;Scontinue])
                Sbreak
              ; Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq [])
                Sbreak
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sexpr Lvalue (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))

              ; Sreturn None
              ]
    )).

Check
  S (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Scontinue)
                (Sseq [Scontinue;Scontinue;Scontinue;Scontinue])
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sreturn None
              ]
    )).

Check
  S (Sseq (
              [ Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Scontinue)
                (Scontinue)
              ; Sreturn (Some (Evar (Lname "x") Ti32))
              ; Sreturn None
              ]
    )).

Check
  S (Sseq (
              (Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq (
                    (Sexpr Prvalue
                      (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                Scontinue) ::
              nil)).

Check
  S (Sseq (
              (Sif
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq (
                    (Sexpr Prvalue
                      (Epostinc (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
                (Sseq (
                    (Sexpr Lvalue
                      (Epredec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) ::
              (Swhile
                (Some (Dvar "x" (Qmut Ti32) (Some (Eint (0) (Qmut Ti32)))))
                (Ecast Cint2bool Prvalue
                    (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32)) (Qmut Tbool))
                (Sseq (
                    (Sexpr Prvalue
                      (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))) :: nil)).

Check
  S (Sseq (
         (Sdo
            (Sseq (
                 (Sexpr Prvalue
                        (Epostdec (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))) :: nil))
            (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))
         ) :: nil)).

Check
  S (Sseq (
         (Sdo
            (Sseq (
                 (Sexpr Lvalue
                        (Eassign (Evar (Lname "foo") Tvoid) (Eunop Unot (Evar (Lname "bar") Tvoid) Tvoid) Tvoid)) :: nil))
            (Ecast Cl2r Lvalue (Evar (Lname  "x") (Qmut Ti32)) (Qmut Ti32))
         ) :: nil)).

Check
  S (Sexpr Lvalue
            (Eassign (Evar (Lname "should_continue") Tbool)
               (Eunop Unot
                  (Ecall
                     (Ecast Cfunction2pointer Lvalue
                        (Evar (Gname "_Z15process_commandPKN4Zeta8Zeta_ctxEPcR9UmxSharedRmR5Admin")
                           (Tfunction Tbool
                              [Tqualified {| q_const := true; q_volatile := false |}
                                 (Tptr
                                    (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                              Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64; 
                              Tref Ti32]))
                        (Tptr
                           (Tfunction Tbool
                              [Tqualified {| q_const := true; q_volatile := false |}
                                 (Tptr
                                    (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                              Tptr Tu8; Tref (Tnamed "_Z9UmxShared"); Tref Tu64; 
                              Tref Ti32])))
(*
                     [Ecast Cl2r Lvalue
                        (Evar (Lname "ctx")
                           (Tqualified {| q_const := true; q_volatile := false |}
                              (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid))))
                        (Tptr (Tqualified {| q_const := true; q_volatile := false |} Tvoid));
                     Ecast Carray2pointer Lvalue (Evar (Lname "buffer") (Tarray Tu8 1024)) (Tptr Tu8);
                     Eread_ref (Evar (Lname "shared") (Tnamed "_Z9UmxShared"));
                     Eread_ref (Evar (Lname "client") Tu64); Evar (Lname "result") Ti32]
*)
                     [] Tbool) Tbool)
               Tbool)).
*)
