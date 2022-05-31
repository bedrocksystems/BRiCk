From bedrock.lang Require Import ast syntax.type_notations.

Section TestTypeNotations.
  #[local] Open Scope CPP_type_scope.

  Context (ty rty aty1 aty2 : type) (n : N) (nm : bs).

  #[local] Definition Notation_Tptr_1 : Tptr Tbool = {(type: ptr<bool>)} := eq_refl.
  #[local] Definition Notation_Tptr_2 : Tptr ty = {(type: ptr<{(coq: ty)}>)} := eq_refl.
  Print Notation_Tptr_1. Print Notation_Tptr_2.

  #[local] Definition Notation_Tref_1 : Tref Tbool = {(type: ref&<bool>)} := eq_refl.
  #[local] Definition Notation_Tref_2 : Tref ty = {(type: ref&<{(coq: ty)}>)} := eq_refl.
  Print Notation_Tref_1. Print Notation_Tref_2.

  #[local] Definition Notation_Trv_ref_1 : Trv_ref Tbool = {(type: ref&&<bool>)} := eq_refl.
  #[local] Definition Notation_Trv_ref_2 : Trv_ref ty = {(type: ref&&<{(coq: ty)}>)} := eq_refl.
  Print Notation_Trv_ref_1. Print Notation_Trv_ref_2.

  #[local] Definition Notation_Tref_Trv_ref : Tref (Trv_ref ty) = {(type: ref&<ref&&<{(coq: ty)}>>)} := eq_refl.
  #[local] Definition Notation_Trv_ref_Tref : Trv_ref (Tref ty) = {(type: ref&&<ref&<{(coq: ty)}>>)} := eq_refl.
  Print Notation_Tref_Trv_ref. Print Notation_Trv_ref_Tref.

  #[local] Definition Notation_void : Tvoid = {(type: void)} := eq_refl.
  Print Notation_void.

  #[local] Definition Notation_Tarray_1 : Tarray Tnullptr 100 = {(type: nullptr_t[100])} := eq_refl.
  #[local] Definition Notation_Tarray_2 : Tarray ty n = {(type: {(coq: ty)}[n])} := eq_refl.
  Print Notation_Tarray_1. Print Notation_Tarray_2.

  #[local] Definition Notation_Tnamed_1 : Tnamed "foobarbaz" = {(type: "foobarbaz")} := eq_refl.
  #[local] Definition Notation_Tnamed_2 : Tnamed nm = {(type: nm)} := eq_refl.
  Print Notation_Tnamed_1. Print Notation_Tnamed_2.

  #[local] Definition Notation_Tfunction_novariadic_noargs_1 : Tfunction Tvoid nil = {(type: extern CC_C ???() -> void)} := eq_refl.
  #[local] Definition Notation_Tfunction_novariadic_noargs_2 : Tfunction rty nil = {(type: extern CC_C ???() -> {(coq: rty)})} := eq_refl.
  Print Notation_Tfunction_novariadic_noargs_1. Print Notation_Tfunction_novariadic_noargs_2.

  #[local] Definition Notation_Tfunction_novariadic_args_nowrap_1 : Tfunction Tvoid (cons Tbool (cons Tnullptr nil)) = {(type: extern CC_C ???(bool, nullptr_t) -> void)} := eq_refl.
  #[local] Definition Notation_Tfunction_novariadic_args_nowrap_2 :
    Tfunction rty (cons aty1 (cons Tvoid (cons aty2 nil))) = {(type: extern CC_C ???({(coq: aty1)}, void, {(coq: aty2)}) -> {(coq: rty)})} := eq_refl.
  Print Notation_Tfunction_novariadic_args_nowrap_1.
  Print Notation_Tfunction_novariadic_args_nowrap_2.

  #[local] Definition Notation_Tfunction_novariadic_args_wrap :
    Tfunction Tvoid (cons (Tnamed "askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk")
                          (cons (Tnamed "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") nil))
      = {(type: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk",
                               "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") -> void)} := eq_refl.
  Print Notation_Tfunction_novariadic_args_wrap.

  #[local] Definition Notation_Tfunction_variadic_noargs_1 : Tfunction (ar:=Ar_Variadic) Tvoid nil = {(type: extern CC_C ???()(...) -> void)} := eq_refl.
  #[local] Definition Notation_Tfunction_variadic_noargs_2 : Tfunction (ar:=Ar_Variadic) rty nil = {(type: extern CC_C ???()(...) -> {(coq: rty)})} := eq_refl.
  Print Notation_Tfunction_variadic_noargs_1. Print Notation_Tfunction_variadic_noargs_2.

  #[local] Definition Notation_Tfunction_variadic_args_nowrap_1 : Tfunction (ar:=Ar_Variadic) Tvoid (cons Tbool (cons Tnullptr nil)) = {(type: extern CC_C ???(bool, nullptr_t)(...) -> void)} := eq_refl.
  #[local] Definition Notation_Tfunction_variadic_args_nowrap_2 :
    Tfunction (ar:=Ar_Variadic) rty (cons aty1 (cons Tvoid (cons aty2 nil))) = {(type: extern CC_C ???({(coq: aty1)}, void, {(coq: aty2)})(...) -> {(coq: rty)})} := eq_refl.
  Print Notation_Tfunction_variadic_args_nowrap_1.
  Print Notation_Tfunction_variadic_args_nowrap_2.

  #[local] Definition Notation_Tfunction_variadic_args_wrap :
    Tfunction (ar:=Ar_Variadic)
              Tvoid (cons (Tnamed "askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk")
                          (cons (Tnamed "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk") nil))
      = {(type: extern CC_C ???("askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk",
                               "askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk")(...) -> void)} := eq_refl.
  Print Notation_Tfunction_variadic_args_wrap.

  #[local] Definition Notation_Tbool : Tbool = {(type: bool)} := eq_refl.
  Print Notation_Tbool.

  #[local] Definition Notation_Tmember_pointer_1 : Tmember_pointer "foobarbaz" Ti8 = {(type: ptr["foobarbaz"]<int8>)} := eq_refl.
  Print Notation_Tmember_pointer_1.

  Section Qualifiers.
    #[local] Definition Notation_mut_1 : Qmut Tbool = {(type: mut bool)} := eq_refl.
    #[local] Definition Notation_mut_2 : Qmut (Qmut Tbool) = {(type: mut (mut bool))} := eq_refl.
    Print Notation_mut_1. Print Notation_mut_2.

    #[local] Definition Notation_const_1 : Qconst Tbool = {(type: const bool)} := eq_refl.
    #[local] Definition Notation_const_2 : Qconst (Tptr (Qconst Tvoid)) = {(type: const ptr<const void>)} := eq_refl.
    Print Notation_const_1. Print Notation_const_2.

    #[local] Definition Notation_volatile_1 : Qmut_volatile Tbool = {(type: volatile bool)} := eq_refl.
    #[local] Definition Notation_volatile_2 : Qmut_volatile (Tptr (Qconst Tvoid)) = {(type: volatile ptr<const void>)} := eq_refl.
    Print Notation_volatile_1. Print Notation_volatile_2.

    #[local] Definition Notation_const_volatile_1 : Qconst_volatile Tbool = {(type: const volatile bool)} := eq_refl.
    #[local] Definition Notation_const_volatile_2 : Qconst_volatile (Tptr (Qconst_volatile Tvoid)) = {(type: const volatile ptr<const volatile void>)} := eq_refl.
    Print Notation_const_volatile_1. Print Notation_const_volatile_2.
  End Qualifiers.
End TestTypeNotations.
