(*
 * Copyright (c) 2019-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.ZArith.ZArith.

Require bedrock.lang.cpp.ast.
From bedrock.lang.cpp.syntax Require Import expr names type_notations.

#[local] Open Scope Z_scope.
#[local] Open Scope bs_scope.

(* TODO (JH): Investigate which (if any) of the subsequent notations we can make
   printing/parsing
 *)

Module Export ExprNotations.
  Declare Custom Entry CPP_expr.
  Declare Scope CPP_expr_scope.
  Delimit Scope CPP_expr_scope with cpp_expr.
  (* TODO (JH): Determine if we want (something like) this, and then do it. *)
  Bind Scope CPP_expr_scope with Expr.

  (* NOTE: precedences taken from cppreference
       (cf. https://en.cppreference.com/w/cpp/language/operator_precedence).
   *)

  (* Injection into [constr] in case we're printing this at the top-level *)
  Notation "'{(e:' e ')}'"
      := e
         ( at level 200
         , e custom CPP_expr at level 200
         , format "'[hv' {(e:  '/' e )} ']'"
         , only printing) : CPP_expr_scope.
  (* Injection from [constr] in case we're printing a subterm we don't recognize *)
  Notation "'{(coq:' e ')}'"
      := e
         ( in custom CPP_expr at level 0
         , e constr
         , format "'[hv' {(coq:  '/' e )} ']'").

  Notation "$ v"
      := (Econst_ref (Lname v%bs) _)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' $ v ']'"
         , only printing).
  Notation "$ :: v"
      := (Econst_ref (Gname v%bs) _)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' $ :: v ']'"
         , only printing).

  Notation "$ v"
      := (Evar (Lname v%bs) _)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' $ v ']'"
         , only printing).
  Notation "$ :: v"
      := (Evar (Gname v%bs) _)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' $ :: v ']'"
         , only printing).

  Notation "'ASCII#' ascii_code"
      := (Echar ascii_code%Z _)
         ( in custom CPP_expr at level 0
         , ascii_code constr
         , format "'[' ASCII# ascii_code ']'"
         , only printing).

  Notation "# s"
      := (Estring s%bs _)
         ( in custom CPP_expr at level 0
         , s constr
         , format "'[' # s ']'"
         , only printing).

  Notation "# v"
      := (Eint v%Z _)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' # v ']'"
         , only printing).

  Notation "# v"
      := (Ebool v)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' # v ']'").

  Notation "'-'" := (Uminus) (in custom CPP_expr at level 0).
  Notation "'!'" := (Unot) (in custom CPP_expr at level 0).
  Notation "'~'" := (Ubnot) (in custom CPP_expr at level 0).
  Notation "'{unop:' op }"
      := (Uother op%bs)
         ( in custom CPP_expr at level 0
         , op constr
         , format "'[' {unop:  '/' op } ']'"
         , only printing).

  (* QUESTION (JH): Is this the right level? *)
  Notation "op x"
      := (Eunop op x _)
         ( in custom CPP_expr at level 30
         , x custom CPP_expr at level 200
         , op custom CPP_expr at level 0
         , format "'[' op x ']'"
         , only printing).

  Notation "'+'" := (Badd) (in custom CPP_expr at level 0).
  Notation "'&'" := (Band) (in custom CPP_expr at level 0).
  Notation "'<=>'" := (Bcmp) (in custom CPP_expr at level 0).
  Notation "'/'" := (Bdiv) (in custom CPP_expr at level 0).
  Notation "'=='" := (Beq) (in custom CPP_expr at level 0).
  Notation "'>='" := (Bge) (in custom CPP_expr at level 0).
  Notation "'>'" := (Bgt) (in custom CPP_expr at level 0).
  Notation "'<='" := (Ble) (in custom CPP_expr at level 0).
  Notation "'<'" := (Blt) (in custom CPP_expr at level 0).
  Notation "'*'" := (Bmul) (in custom CPP_expr at level 0).
  Notation "'!='" := (Bneq) (in custom CPP_expr at level 0).
  Notation "'|'" := (Bor) (in custom CPP_expr at level 0).
  Notation "'%'" := (Bmod) (in custom CPP_expr at level 0).
  Notation "'<<'" := (Bshl) (in custom CPP_expr at level 0).
  (* NOTE (JH): The following [Bshr] notation conflicts with parsing nested [ptr<ptr<...>>]
     [type]s, so we leave it disabled and provide explicit notations for the [Ebinop] and
     [Eassign_op] notations.
   *)
  (* Notation "'>>'" := (Bshr) (in custom CPP_expr at level 0). *)
  Notation "'-'" := (Bsub) (in custom CPP_expr at level 0).
  Notation "'^'" := (Bxor) (in custom CPP_expr at level 0).
  Notation "'.*'" := (Bdotp) (in custom CPP_expr at level 0).
  Notation "'->*'" := (Bdotip) (in custom CPP_expr at level 0).

  (* TODO (JH): Look into ways of fusing direct nestings of [{binop: ...}] *)

  Notation "'{binop:' x .* y }"
      := (Ebinop Bdotp x y _)
         ( in custom CPP_expr at level 40
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x .* y } ']'"
         , only printing).
  Notation "'{binop:' x ->* y }"
      := (Ebinop Bdotip x y _)
         ( in custom CPP_expr at level 40
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x ->* y } ']'"
         , only printing).

  Notation "'{binop:' x * y }"
      := (Ebinop Bmul x y _)
         ( in custom CPP_expr at level 50
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  *  y } ']'"
         , only printing).
  Notation "'{binop:' x / y }"
      := (Ebinop Bdiv x y _)
         ( in custom CPP_expr at level 50
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  /  y } ']'"
         , only printing).
  Notation "'{binop:' x % y }"
      := (Ebinop Bmod x y _)
         ( in custom CPP_expr at level 50
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  %  y } ']'"
         , only printing).

  Notation "'{binop:' x + y }"
      := (Ebinop Badd x y _)
         ( in custom CPP_expr at level 60
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  +  y } ']'"
         , only printing).
  Notation "'{binop:' x - y }"
      := (Ebinop Bsub x y _)
         ( in custom CPP_expr at level 60
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  -  y } ']'"
         , only printing).

  Notation "'{binop:' x << y }"
      := (Ebinop Bshl x y _)
         ( in custom CPP_expr at level 70
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  <<  y } ']'"
         , only printing).
  Notation "'{binop:' x >> y }"
      := (Ebinop Bshr x y _)
         ( in custom CPP_expr at level 70
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  >>  y } ']'"
         , only printing).

  Notation "'{binop:' x <=> y }"
      := (Ebinop Bcmp x y _)
         ( in custom CPP_expr at level 80
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  <=>  y } ']'"
         , only printing).

  Notation "'{binop:' x < y }"
      := (Ebinop Blt x y _)
         ( in custom CPP_expr at level 90
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  <  y } ']'"
         , only printing).
  Notation "'{binop:' x <= y }"
      := (Ebinop Ble x y _)
         ( in custom CPP_expr at level 90
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  <=  y } ']'"
         , only printing).
  Notation "'{binop:' x > y }"
      := (Ebinop Bgt x y _)
         ( in custom CPP_expr at level 90
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  >  y } ']'"
         , only printing).
  Notation "'{binop:' x >= y }"
      := (Ebinop Bge x y _)
         ( in custom CPP_expr at level 90
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  >=  y } ']'"
         , only printing).

  Notation "'{binop:' x == y }"
      := (Ebinop Beq x y _)
         ( in custom CPP_expr at level 100
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  ==  y } ']'"
         , only printing).
  Notation "'{binop:' x != y }"
      := (Ebinop Bneq x y _)
         ( in custom CPP_expr at level 100
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  !=  y } ']'"
         , only printing).

  Notation "'{binop:' x & y }"
      := (Ebinop Band x y _)
         ( in custom CPP_expr at level 110
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  &  y } ']'"
         , only printing).

  Notation "'{binop:' x ^ y }"
      := (Ebinop Band x y _)
         ( in custom CPP_expr at level 120
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  ^  y } ']'"
         , only printing).

  Notation "'{binop:' x | y }"
      := (Ebinop Band x y _)
         ( in custom CPP_expr at level 130
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' x  |  y } ']'"
         , only printing).

  Notation "$ v"
      := (Eread_ref (Evar (Lname v%bs) _))
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' $ v ']'"
         , only printing).
  Notation "$ :: v"
      := (Eread_ref (Evar (Gname v%bs) _))
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' $ :: v ']'"
         , only printing).

  Notation "* e"
      := (Ederef e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' * e ']'"
         , only printing).

  Notation "& e"
      := (Eaddrof e)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' & e ']'"
         , only printing).

  Notation "v = e"
      := (Eassign v e _)
         ( in custom CPP_expr at level 160
         , e custom CPP_expr at level 200
         , v custom CPP_expr at level 200
         , format "'[hv  ' v  =  '/' e ']'"
         , only printing).

  Notation "v >>= e"
      := (Eassign_op Bshr v e)
         ( in custom CPP_expr at level 159
         , e custom CPP_expr at level 200
         , v custom CPP_expr at level 200
         , format "'[hv  ' v  >>=  '/' e ']'"
         , only printing).
  Notation "v bop = e"
      := (Eassign_op bop v e)
         ( in custom CPP_expr at level 160
         , e custom CPP_expr at level 200
         , v custom CPP_expr at level 200
         , bop custom CPP_expr at level 0
         , format "'[hv  ' v  bop =  '/' e ']'"
         , only printing).

  Notation "++ e"
      := (Epreinc e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' ++ e ']'"
         , only printing).
  Notation "e ++"
      := (Epostinc e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' e ++ ']'"
         , only printing).
  Notation "-- e"
      := (Epredec e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' -- e ']'"
         , only printing).
  Notation "e --"
      := (Epostdec e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' e -- ']'"
         , only printing).

  Notation "'{binop:' e1 && e2 }"
      := (Eseqand e1 e2)
         ( in custom CPP_expr at level 140
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' e1  &&  e2 } ']'").

  Notation "'{binop:' e1 || e2 }"
      := (Eseqor e1 e2)
         ( in custom CPP_expr at level 150
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , format "'[hv   ' {binop:  '/' e1  ||  e2 } ']'").

  Notation "'{comma:' e1 , e2 }"
      := (Ecomma _ e1 e2)
         ( in custom CPP_expr at level 170
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , format "'[hv   ' {comma:  '/' e1 ,  e2 } ']'").

  Notation "e '()'"
      := (Ecall e nil _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , format "'[' e () ']'"
         , only printing).
  Notation "e ( a1 , .. , a2 )"
      := (Ecall e (cons a1 (.. (cons a2 nil) .. )) _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , a1 custom CPP_expr at level 200
         , a2 custom CPP_expr at level 200
         , format "'[' e ( '[hv' a1 ,  '/' .. ,  '/' a2 ']' ) ']'"
         , only printing).

  (* TODO (JH): Determine which casts we actually want to print something for *)
  Notation "e"
      := (Ecast _ _ e _)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).

  Notation "e . fld"
      := (Emember _ e (Build_field _ fld%bs) _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , fld constr
         , format "'[' e . fld ']'"
         , only printing).

  (* NOTE (JH): [Emember_call (inr ...) ...] doesn't seem to be used so we don't
     include a notation for it.
   *)
  Notation "e . fn ()"
      := (Emember_call (inl (fn%bs, _, _)) _ e nil _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , fn constr
         , format "'[' e . fn () ']'"
         , only printing).
  Notation "e . fn ( a1 , .. , a2 )"
      := (Emember_call (inl (fn, _, _)) _ e (cons a1 .. (cons a2 nil) ..) _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , a1 custom CPP_expr at level 200
         , a2 custom CPP_expr at level 200
         , fn constr
         , format "'[' e . fn ( '[hv' a1 ,  '/' .. ,  '/' a2 ']' ) ']'"
         , only printing).

  Notation "e [ n ]"
      := (Esubscript e n _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , n custom CPP_expr at level 200
         , format "'[' e [ n ] ']'"
         , only printing).

  Notation "'sizeof(ty:' ty )"
      := (Esize_of (inl ty) _)
         ( in custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' sizeof(ty:  ty ) ']'"
         , only printing).
  Notation "'sizeof(expr:' e )"
      := (Esize_of (inr e) _)
         ( in custom CPP_expr at level 200
         , e custom CPP_expr at level 200
         , format "'[' sizeof(expr:  e ) ']'"
         , only printing).

  Notation "'alignof(ty:' ty )"
      := (Ealign_of (inl ty) _)
         ( in custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' alignof(ty:  ty ) ']'"
         , only printing).
  Notation "'alignof(expr:' e )"
      := (Ealign_of (inr e) _)
         ( in custom CPP_expr at level 200
         , e custom CPP_expr at level 200
         , format "'[' alignof(expr:  e ) ']'"
         , only printing).

  Notation "f"
      := (Oo_Field f)
         ( in custom CPP_expr at level 0
         , f custom CPP_expr at level 200
         , format "'[' f ']'"
         , only printing).

  Notation "'offsetof(' offset_info )"
      := (Eoffset_of offset_info _)
         ( in custom CPP_expr at level 200
         , offset_info custom CPP_expr at level 200
         , format "'[' offsetof( offset_info ) ']'"
         , only printing).

  Notation "'#' cls ()"
      := (Econstructor cls%bs nil _)
         ( in custom CPP_expr at level 20
         , cls constr
         , format "'[' # cls () ']'"
         , only printing).
  Notation "'#' cls ( a1 , .. , a2 )"
      := (Econstructor cls%bs (cons a1 .. (cons a2 nil) ..) _)
         ( in custom CPP_expr at level 20
         , a1 custom CPP_expr at level 200
         , a2 custom CPP_expr at level 200
         , cls constr
         , format "'[' # cls ( '[hv' a1 ,  '/' .. ,  '/' a2 ']' ) ']'"
         , only printing).

  Notation "e"
      := (Eimplicit e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "ty '{{VALUE' 'INIT}}'"
      := (Eimplicit_init ty)
         ( in custom CPP_expr at level 0
         , ty custom CPP_type at level 200
         , format "'[' ty {{VALUE  INIT}} ']'"
         , only printing).

  Notation "c ? t : e"
      := (Eif c t e _)
         ( in custom CPP_expr at level 160
         , c custom CPP_expr at level 200
         , t custom CPP_expr at level 200
         , e custom CPP_expr at level 200
         , format "'[hv   ' c  '/' ?  t  '/' :  e ']'"
         , only printing).

  Notation "'this'" := (Ethis _) (in custom CPP_expr at level 0, only printing).
  Notation "'nullptr'" := (Enull) (in custom CPP_expr at level 0).

  (* NOTE: [Einitlist nil (Some _) _] corresponds to an ill-formed program
     (cf. the [Lt] case of [wp_array_init_fill])
   *)
  Notation "( ty ){ }"
      := (Einitlist nil None ty)
         ( in custom CPP_expr at level 100
         , ty custom CPP_type at level 200
         , format "'[' ( ty ){  } ']'").
  Notation "( ty ){ e1 , .. , e2 }"
      := (Einitlist (cons e1 .. (cons e2 nil) ..) None ty)
         ( in custom CPP_expr at level 100
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' ( ty ){ '[hv' e1 ,  '/' .. ,  '/' e2 ']' } ']'").
  Notation "( ty ){ e1 , .. , e2 '}{default:' edefault '}'"
      := (Einitlist (cons e1 .. (cons e2 nil) ..) (Some edefault) ty)
         ( in custom CPP_expr at level 100
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , edefault custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' ( ty ){ '[hv' e1 ,  '/' .. ,  '/' e2 ']' }{default:  '/' edefault } ']'").

  Notation "'new' '(nothrow)' ty"
      := (Enew _ nil ty None _)
         ( in custom CPP_expr at level 30
         , ty custom CPP_type at level 200
         , format "'[' new  (nothrow)  ty ']'"
         , only printing).
  Notation "'new' '(nothrow)' ty ( a1 , .. , a2 )"
      := (Enew _ (cons a1 .. (cons a2 nil) ..) ty None _)
         ( in custom CPP_expr at level 30
         , a1 custom CPP_expr at level 200
         , a2 custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' new  (nothrow)  ty ( '[hv' a1 ,  '/' .. ,  '/' a2 ']' ) ']'"
         , only printing).

  (* NOTE (JH): array-[new] expressions shouldn't have argument lists *)
  Notation "'new' '(nothrow)' ty [ esz ]"
      := (Enew _ _ ty (Some esz) _)
         ( in custom CPP_expr at level 30
         , esz custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' new  (nothrow)  ty [ esz ] ']'"
         , only printing).

  Notation "'delete' e"
      := (Edelete false _ e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' delete  e ']'"
         , only printing).

  Notation "'delete[]' e"
      := (Edelete true _ e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' delete[]  e ']'"
         , only printing).

  (* QUESTION (JH): should we have notations which display sequence points? *)
  Notation "e"
      := (Eandclean e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "e"
      := (Ematerialize_temp e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).

  Notation "'__builtin_alloca'" := (Bin_alloca) ( in custom CPP_expr at level 0).
  Notation "'__builtin_alloca_with_align'" := (Bin_alloca_with_align) ( in custom CPP_expr at level 0).
  Notation "'__builtin_launder'" := (Bin_launder) ( in custom CPP_expr at level 0).
  Notation "'__builtin_expect'" := (Bin_expect) ( in custom CPP_expr at level 0).
  Notation "'__builtin_unreachable'" := (Bin_unreachable) ( in custom CPP_expr at level 0).
  Notation "'__builtin_trap'" := (Bin_trap) ( in custom CPP_expr at level 0).
  Notation "'__builtin_bswap16'" := (Bin_bswap16) ( in custom CPP_expr at level 0).
  Notation "'__builtin_bswap32'" := (Bin_bswap32) ( in custom CPP_expr at level 0).
  Notation "'__builtin_bswap64'" := (Bin_bswap64) ( in custom CPP_expr at level 0).
  Notation "'__builtin_bswap128'" := (Bin_bswap128) ( in custom CPP_expr at level 0).
  Notation "'__builtin_bzero'" := (Bin_bzero) ( in custom CPP_expr at level 0).
  Notation "'__builtin_ffs'" := (Bin_ffs) ( in custom CPP_expr at level 0).
  Notation "'__builtin_ffsl'" := (Bin_ffsl) ( in custom CPP_expr at level 0).
  Notation "'__builtin_ffsll'" := (Bin_ffsll) ( in custom CPP_expr at level 0).
  Notation "'__builtin_clz'" := (Bin_clz) ( in custom CPP_expr at level 0).
  Notation "'__builtin_clzl'" := (Bin_clzl) ( in custom CPP_expr at level 0).
  Notation "'__builtin_clzll'" := (Bin_clzll) ( in custom CPP_expr at level 0).
  Notation "'__builtin_ctz'" := (Bin_ctz) ( in custom CPP_expr at level 0).
  Notation "'__builtin_ctzl'" := (Bin_ctzl) ( in custom CPP_expr at level 0).
  Notation "'__builtin_ctzll'" := (Bin_ctzll) ( in custom CPP_expr at level 0).
  Notation "'__builtin_popcount'" := (Bin_popcount) ( in custom CPP_expr at level 0).
  Notation "'__builtin_popcountl'" := (Bin_popcountl) ( in custom CPP_expr at level 0).
  Notation "'__builtin_UNKNOWN_' nm"
      := (Bin_unknown nm%bs)
         ( in custom CPP_expr at level 0
         , nm constr
         , format "'[' __builtin_UNKNOWN_ nm ']'").

  Notation "'{builtin:' bin ';' 'signature:' ty '}'"
      := (Ebuiltin bin ty)
         ( in custom CPP_expr at level 20
         , bin custom CPP_expr at level 0
         , ty custom CPP_type at level 200
         , format "'[' {builtin:  bin ;  signature:  ty } ']'").

  (* TODO (JH): [Eatomic] *)

  (* QUESTION (JH): is this notation sufficient for [Eva_arg]? *)
  Notation "e"
      := (Eva_arg e _)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).

  (* QUESTION (JH): is this notation sufficient for [Epseudo_destructor]? *)
  Notation "e"
      := (Epseudo_destructor _ e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).


  (* TODO (JH): [Earrayloop_init]/[Earrayloop_index]/[Eopaque_ref] *)

  Notation "'{UNSUPPORTED:' msg }"
      := (Eunsupported msg%bs _)
         ( in custom CPP_expr at level 0
         , msg constr
         , format "'[hv   ' {UNSUPPORTED:  '/' msg } ']'"
         , only printing).
End ExprNotations.

(* NOTE: The following [Section]s are only used for testing purposes; if you break one of these
   tests - or add a new notation - please update things accordingly.
 *)

Section TestExprNotations.
  Import bedrock.lang.cpp.ast.
  Import TypeNotations. #[local] Open Scope CPP_type_scope.
  Import ExprNotations. #[local] Open Scope CPP_expr_scope.

  (* Check (Ebinop Badd (Ederef (Eaddrof (Evar (Lname "hello") Tvoid)) Tvoid) *)
  (*               (Eint 3%Z Tvoid) Tvoid). *)
End TestExprNotations.
