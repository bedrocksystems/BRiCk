(*
 * Copyright (c) 2019-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.ZArith.ZArith.

Require bedrock.lang.cpp.ast.
From bedrock.lang.cpp.syntax Require Import names types.

#[local] Open Scope Z_scope.
#[local] Open Scope bs_scope.

Module Export TypeNotations.
  Declare Custom Entry CPP_type.
  Declare Scope CPP_type_scope.
  Delimit Scope CPP_type_scope with cpp_type.
  (* TODO (JH): Determine if we want (something like) this, and then do it. *)
  Bind Scope CPP_type_scope with type.

  (* Injection into [constr] in case we're printing this at the top-level *)
  Notation "'{(type:' ty ')}'"
      := ty
         ( at level 100
         , ty custom CPP_type at level 200
         , format "'[hv' {(type:  '/' ty )} ']'")
       : CPP_type_scope.
  (* Injection from [constr] in case we're printing a subterm we don't recognize *)
  Notation "'{(coq:' ty ')}'"
      := ty
         ( in custom CPP_type at level 0
         , ty constr
         , format "'[hv' {(coq:  '/' ty )} ']'").

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
  Notation "ty [ n ]"
      := (Tarray ty n%N)
         ( in custom CPP_type at level 80
         , ty custom CPP_type
         , n constr
         , format "'[' ty [ n ] ']'").
  Notation "nm" := (Tnamed nm%bs) (in custom CPP_type at level 0, nm constr).
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
      := (Tmember_pointer nm%bs ty)
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
      := (Tarch None nm%bs)
         ( in custom CPP_type at level 0
         , nm constr
         , format "'[hv' {arch:  '/' nm } ']'").
  Notation "'{arch:' nm ';' 'size:' sz '}'"
      := (Tarch (Some sz) nm%bs)
         ( in custom CPP_type at level 0
         , sz constr
         , nm constr
         , format "'[hv' {arch:  nm ;  '/' size:  sz } ']'").
End TypeNotations.

(* NOTE: The following [Section] is only used for testing purposes; if you break one of these
   tests - or add a new notation - please update things accordingly.
 *)

Section TestTypeNotations.
  Import bedrock.lang.cpp.ast.
  Import TypeNotations. #[local] Open Scope CPP_type_scope.

  #[local] Definition Notation_Tptr_1 : Tptr Tbool = {(type: ptr<bool>)} := eq_refl.
  #[local] Definition Notation_Tptr_2 ty : Tptr ty = {(type: ptr<{(coq: ty)}>)} := eq_refl.

  #[local] Definition Notation_Tref_1 : Tref Tbool = {(type: ref&<bool>)} := eq_refl.
  #[local] Definition Notation_Tref_2 ty : Tref ty = {(type: ref&<{(coq: ty)}>)} := eq_refl.

  #[local] Definition Notation_Trv_ref_1 : Trv_ref Tbool = {(type: ref&&<bool>)} := eq_refl.
  #[local] Definition Notation_Trv_ref_2 ty : Trv_ref ty = {(type: ref&&<{(coq: ty)}>)} := eq_refl.

  #[local] Definition Notation_Tref_Trv_ref ty : Tref (Trv_ref ty) = {(type: ref&<ref&&<{(coq: ty)}>>)} := eq_refl.
  #[local] Definition Notation_Trv_ref_Tref_1 ty : Trv_ref (Tref ty) = {(type: ref&&<ref&<{(coq: ty)}>>)} := eq_refl.

  #[local] Definition Notation_void : Tvoid = {(type: void)} := eq_refl.

  #[local] Definition Notation_Tarray_1 : Tarray Tnullptr 100 = {(type: nullptr_t[100])} := eq_refl.
  #[local] Definition Notation_Tarray_2 ty n : Tarray ty n = {(type: {(coq: ty)}[n])} := eq_refl.

  #[local] Definition Notation_Tnamed_1 : Tnamed "foobarbaz" = {(type: "foobarbaz")} := eq_refl.
  #[local] Definition Notation_Tnamed_2 nm : Tnamed nm = {(type: nm)} := eq_refl.

  #[local] Definition Notation_Tfunction_novariadic_noargs_1 : Tfunction Tvoid nil = {(type: extern CC_C ???() -> void)} := eq_refl.
  #[local] Definition Notation_Tfunction_novariadic_noargs_2 rty : Tfunction rty nil = {(type: extern CC_C ???() -> {(coq: rty)})} := eq_refl.

  #[local] Definition Notation_Tfunction_novariadic_args_nowrap_1 : Tfunction Tvoid (cons Tbool (cons Tnullptr nil)) = {(type: extern CC_C ???(bool, nullptr_t) -> void)} := eq_refl.
  #[local] Definition Notation_Tfunction_novariadic_noargs_nowrap_2 rty aty1 aty2 :
    Tfunction rty (cons aty1 (cons Tvoid (cons aty2 nil))) = {(type: extern CC_C ???({(coq: aty1)}, void, {(coq: aty2)}) -> {(coq: rty)})} := eq_refl.

  #[local] Definition Notation_Tfunction_novariadic_args_wrap :
    Tfunction Tvoid (cons (Tnamed "askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk")
                          (cons (Tnamed "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") nil))
      = {(type: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk",
                               "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") -> void)} := eq_refl.

  #[local] Definition Notation_Tfunction_variadic_noargs_1 : Tfunction (ar:=Ar_Variadic) Tvoid nil = {(type: extern CC_C ???()(...) -> void)} := eq_refl.
  #[local] Definition Notation_Tfunction_variadic_noargs_2 rty : Tfunction (ar:=Ar_Variadic) rty nil = {(type: extern CC_C ???()(...) -> {(coq: rty)})} := eq_refl.

  #[local] Definition Notation_Tfunction_variadic_args_nowrap_1 : Tfunction (ar:=Ar_Variadic) Tvoid (cons Tbool (cons Tnullptr nil)) = {(type: extern CC_C ???(bool, nullptr_t)(...) -> void)} := eq_refl.
  #[local] Definition Notation_Tfunction_variadic_noargs_nowrap_2 rty aty1 aty2 :
    Tfunction (ar:=Ar_Variadic) rty (cons aty1 (cons Tvoid (cons aty2 nil))) = {(type: extern CC_C ???({(coq: aty1)}, void, {(coq: aty2)})(...) -> {(coq: rty)})} := eq_refl.

  #[local] Definition Notation_Tfunction_variadic_args_wrap :
    Tfunction (ar:=Ar_Variadic)
              Tvoid (cons (Tnamed "askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk")
                          (cons (Tnamed "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") nil))
      = {(type: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk",
                               "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk")(...) -> void)} := eq_refl.

  #[local] Definition Notation_Tbool : Tbool = {(type: bool)} := eq_refl.

  #[local] Definition Notation_Tmember_pointer_1 : Tmember_pointer "foobarbaz" Ti8 = {(type: ptr["foobarbaz"]<int8>)} := eq_refl.

  Section Qualifiers.
    #[local] Definition Notation_mut_1 : Qmut Tbool = {(type: mut bool)} := eq_refl.
    #[local] Definition Notation_mut_2 : Qmut (Qmut Tbool) = {(type: mut (mut bool))} := eq_refl.

    #[local] Definition Notation_const_1 : Qconst Tbool = {(type: const bool)} := eq_refl.
    #[local] Definition Notation_const_2 : Qconst (Tptr (Qconst Tvoid)) = {(type: const ptr<const void>)} := eq_refl.

    #[local] Definition Notation_volatile_1 : Qmut_volatile Tbool = {(type: volatile bool)} := eq_refl.
    #[local] Definition Notation_volatile_2 : Qmut_volatile (Tptr (Qconst Tvoid)) = {(type: volatile ptr<const void>)} := eq_refl.

    #[local] Definition Notation_const_volatile_1 : Qconst_volatile Tbool = {(type: const volatile bool)} := eq_refl.
    #[local] Definition Notation_const_volatile_2 : Qconst_volatile (Tptr (Qconst_volatile Tvoid)) = {(type: const volatile ptr<const volatile void>)} := eq_refl.
  End Qualifiers.
End TestTypeNotations.
