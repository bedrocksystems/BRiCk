(*
 * Copyright (c) 2019-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
From bedrock.lang.cpp Require Import ast parser.

#[local] Open Scope Z_scope.
#[local] Open Scope string_scope.

(* TODO (JH): Look into disabling (selective) scopes *)

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

(* TODO (JH): Investigate which (if any) of the subsequent notations we can make
   printing/parsing
 *)

Module Export ExprNotations.
  Declare Custom Entry CPP_expr.
  Declare Scope CPP_expr_scope.
  Delimit Scope CPP_expr_scope with cpp_expr.

  (* NOTE: precedences taken from cppreference
       (cf. https://en.cppreference.com/w/cpp/language/operator_precedence).
   *)

  (* Injection into [constr] in case we're printing this at the top-level *)
  Notation "'{(expr:' e ')}'"
      := e
         ( at level 200
         , e custom CPP_expr at level 200
         , format "'[hv' {(expr:  '/' e )} ']'"
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
      := (Eaddrof e _)
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

  (* TODO (JH): [Ebuiltin] *)
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
         ( in custom CPP_expr at level 200
         , msg constr
         , format "'[hv   ' {UNSUPPORTED:  '/' msg } ']'"
         , only printing).
End ExprNotations.

Module Export StmtNotations.
  Declare Custom Entry CPP_stmt.
  Declare Scope CPP_stmt_scope.
  Delimit Scope CPP_stmt_scope with cpp_stmt.

  (* Quotation mechanism for [Stmt]s *)
  Notation "'{stmt:' s }" := s
    ( at level 200
    , s custom CPP_stmt at level 200
    , format "'[hv' {stmt:  '/' s } ']'"
    , only printing) : CPP_stmt_scope.
End StmtNotations.

Module Export CodeNotations.
  Export TypeNotations.
  Export ExprNotations.
  Export StmtNotations.
End CodeNotations.

(* NOTE: The following [Section]s are only used for testing purposes; if you break one of these
   tests - or add a new notation - please update things accordingly.
 *)

Section TestTypeNotations.
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

Section TestExprNotations.
End TestExprNotations.

Section TestStmtNotations.
End TestStmtNotations.

(* [cpp2v/theories/auto/cpp/notations/code.v@janno/code-notations], but that branch is out of date
Declare Custom Entry CPP.
Declare Scope CPP_scope.
Delimit Scope CPP_scope with cpp.

(** Notations for expressions *)





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
