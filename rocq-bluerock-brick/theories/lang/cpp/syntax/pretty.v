(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.bytestring_core.
Require Import bedrock.prelude.bytestring.

Require Import bedrock.lang.cpp.syntax.core.

(** Pretty printing of C++ terms *)

Definition printOO (oo : OverloadableOperator) : bs :=
  match oo with
  | OOTilde => "~"
  | OOExclaim => "!"
  | OOPlusPlus => "++"
  | OOMinusMinus => "--"
  | OOStar => "*"
  | OOPlus => "+"
  | OOMinus => "-"
  | OOSlash => "/"
  | OOPercent => "%"
  | OOCaret => "^"
  | OOAmp => "&"
  | OOPipe => "|"
  | OOEqual => "="
  | OOLessLess => "<<"
  | OOGreaterGreater => ">>"
  | OOPlusEqual => "+="
  | OOMinusEqual => "-="
  | OOStarEqual => "*="
  | OOSlashEqual => "/="
  | OOPercentEqual => "%="
  | OOCaretEqual => "^="
  | OOAmpEqual => "&="
  | OOPipeEqual => "|="
  | OOLessLessEqual => "<<="
  | OOGreaterGreaterEqual => ">>="
  | OOEqualEqual => "=="
  | OOExclaimEqual => "!="
  | OOLess => "<"
  | OOGreater => ">"
  | OOLessEqual => "<="
  | OOGreaterEqual => ">="
  | OOSpaceship => "<=>"
  | OOComma => ","
  | OOArrowStar => "->*"
  | OOArrow => "->"
  | OOSubscript => "[]"
  | OOAmpAmp => "&&"
  | OOPipePipe => "||"
  | OONew array => if array then " new[]" else " new"
  | OODelete array => if array then " delete[]" else " delete"
  | OOCall => "()"
  | OOCoawait => " coawait"
  end%bs.

Section with_lang.

  #[local] Open Scope bs_scope.

  Definition showN (n : N) : bs :=
    BS.of_string $ pretty.pretty_N n.

  Definition parens (b : bs) : bs := "(" ++ b ++ ")".
  Definition angles (b : bs) : bs := "<" ++ b ++ ">".

  #[local] Open Scope bs_scope.

  Section atomic_name.
    Context {type Expr : Set} (printType : type -> bs) (printExpr : Expr -> bs).
    Variable top : option bs.

    Definition printFN (fn : function_name_ type) : bs :=
      match fn with
      | Nf nm => nm
      | Nctor =>
          match top with
          | None => "<ctor>"
          | Some cls => cls
          end
      | Ndtor =>
          match top with
          | None => "<dtor>"
          | Some cls => "~" ++ cls
          end
      | Nop o =>
          let o := printOO o in
          "operator" ++ o
      | Nop_conv t => "operator " ++ printType t
      | Nop_lit i => "operator """"_" ++ i
      | Nunsupported_function note => "?" ++ note
      end.

    Definition with_space (b : bs) : bs :=
      match b with
      | BS.EmptyString => ""
      | _ => " " ++ b
      end.

    Definition printFQ (fq : function_qualifiers.t) : bs :=
      let c := if function_qualifiers.is_const fq then ["const"] else [] in
      let v := if function_qualifiers.is_volatile fq then ["volatile"] else [] in
      let vc := match function_qualifiers.vc_of fq with
                | Prvalue => []
                | Lvalue => ["&"]
                | Xvalue => ["&&"]
                end in
      BS.concat " " $ (c ++ v ++ vc)%list.

    Definition printAN (an : atomic_name_ type) : bs :=
      match an with
      | Nid id => id
      | Nfunction quals nm args =>
          printFN nm ++ (parens $ BS.concat ", " $ printType <$> args) ++ with_space (printFQ quals)
      | Nanon n => "@" ++ showN n
      | Nanonymous => "(anon)"
      | Nfirst_decl n => "#" ++ n
      | Nfirst_child n => "." ++ n
      | Nunsupported_atomic note => "?" ++ note
      end%bs.
  End atomic_name.

  Fixpoint topName (nm : name) : option bs :=
    match nm with
    | Nglobal (Nid id) => Some id
    | Nscoped _ (Nid id) => Some id
    | Ninst nm _ => topName nm
    | _ => None
    end.

  Definition printUO (o : overloadable.RUnOp) : bs :=
    match o with
    | overloadable.Rpreinc => "(++_)"
    | overloadable.Rpostinc => "(_++)"
    | overloadable.Rpredec => "(--_)"
    | overloadable.Rpostdec => "(_--)"
    | overloadable.Rstar => "*"
    | overloadable.Rarrow => "->"
    | overloadable.Runop op =>
        match op with
        | Uminus => "-"
        | Uplus => "+"
        | Unot => "!"
        | Ubnot => "~"
        | Uunsupported n => n
        end
    end.

  Definition printBO (o : overloadable.RBinOp) : bs :=
    let printBO o :=
      match o with
      | Badd => "+"
      | Band => "&&"
      | Bcmp => "<=>"
      | Bdiv => "/"
      | Beq => "=="
      | Bge => ">="
      | Bgt => ">"
      | Ble => "<="
      | Blt => "<"
      | Bmul => "*"
      | Bneq => "!="
      | Bor => "||"
      | Bmod => "%"
      | Bshl => "<<"
      | Bshr => ">>"
      | Bsub => "-"
      | Bxor => "^"
      | Bdotp => ".*"
      | Bdotip => "->*"
      | Bunsupported b => b
      end
    in
    match o with
    | overloadable.Rbinop b => printBO b
    | overloadable.Rassign => "="
    | overloadable.Rassign_op b => printBO b ++ "="
    | overloadable.Rsubscript => "[]"
    end.

  Section printTA.
    Context (printN : name -> bs) (printT : type -> bs) (printE : Expr -> bs).

    Fixpoint printTA (ta : temp_arg_ name type Expr) : list bs :=
      match ta with
      | Atype t => [printT t]
      | Avalue e => [printE e]
      | Apack ls => concat (List.map printTA ls)
      | Atemplate n => ["<>" ++ printN n]
      | Aunsupported note => [note]
      end.
  End printTA.

  Fixpoint printN (nm : name) : bs :=
    match nm with
    | Nglobal an => printAN printT None an
    | Ndependent an => printT an
    | Nscoped base Nanonymous => printN base
    | Nscoped base n => printN base ++ "::" ++ printAN printT (topName base) n
    | Ninst base i =>
        printN base ++ angles (BS.concat ", " $ concat (List.map (printTA printN printT printE) i))
    | Nunsupported note => "?" ++ note
    end

  with printT (ty : type) : bs :=
    match ty with
    | Tint => "int"
    | Tuint => "unsigned int"
    | Tchar => "char"
    | Tuchar => "unsigned char"
    | Tschar => "signed char"
    | Tshort => "short"
    | Tushort => "unsigned short"
    | Tlong => "long"
    | Tulong => "unsigned long"
    | Tlonglong => "long long"
    | Tulonglong => "unsigned long long"
    | Tnum int_rank.I128 Signed => "int128_t"
    | Tnum int_rank.I128 Unsigned => "uint128_t"
    | Twchar => "wchar_t"
    | Tchar8 => "char8_t"
    | Tchar16 => "char16_t"
    | Tchar32 => "char32_t"
    | Tfloat => "float"
    | Tfloat16 => "float16"
    | Tfloat128 => "float128"
    | Tdouble => "double"
    | Tlongdouble => "long double"
    | Tbool => "bool"
    | Tnullptr => "nullptr_t"
    | Tptr t => printT t ++ "*"
    | Tref t => printT t ++ "&"
    | Trv_ref t => printT t ++ "&&"
    | Tmember_pointer cls t => printT t ++ " " ++ printT cls ++ "::*"
    | Tqualified q t =>
        BS.concat " " $ (printT t :: (if q_const q then ["const"] else []) ++
        (if q_volatile q then ["volatile"] else []))%list
    | Tvoid => "void"
    | Tarray t n => printT t ++ "[" ++ showN n ++ "]"
    | Tincomplete_array t => printT t ++ "[]"
    | Tvariable_array t e => printT t ++ "[" ++ printE e ++ "]"
    | Tdecltype e => "decltype((" ++ printE e ++ "))"
    | Texprtype e => "decltype(" ++ printE e ++ ")"
    | Tnamed nm | Tenum nm => printN nm
    | Tfunction ft =>
        (parens $ printT ft.(ft_return) ++ "*") ++
        (parens $ BS.concat ", " $ printT <$> ft.(ft_params))
    | Tarch _ note => "?" ++ note
    | Tunsupported note => "?" ++ note
    | Tparam nm => nm
    | Tresult_param nm => "decltype(" ++ nm ++ ")"
    | Tresult_global nm => "decltype(" ++ printN nm ++ ")"
    | Tresult_unop op t => "decltype(" ++ printUO op ++ "(?" ++ printT t ++ "))"
    | Tresult_binop op t1 t2 =>
        "decltype(" ++ printBO op ++ "(?" ++ printT t1 ++ ",?" ++ printT t2 ++ "))"
    | Tresult_call _ _
    | Tresult_member_call _ _ _
    | Tresult_parenlist _ _
    | Tresult_member _ _ => "!nyi"
    end
  with printE (e : Expr) : bs :=
    match e with
    | Eglobal nm _ => printN nm
    | _ => "!nyi"
    end.

End with_lang.

Definition print_name (input : name) : list Byte.byte :=
  BS.print $ printN input.

Definition TEST (nm : name) (result : bs) : Prop :=
  BS.parse (print_name nm) = result.

Succeed Example _0 : TEST (Nglobal $ Nid "foo") "foo" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nfunction function_qualifiers.N (Nop OOPlusPlus) []) "operator++()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nfunction function_qualifiers.N (Nop $ OONew true) []) "operator new[]()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nfunction function_qualifiers.N (Nop $ OONew false) []) "operator new()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nfunction function_qualifiers.N (Nop $ OODelete true) []) "operator delete[]()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nfunction function_qualifiers.N (Nop $ OODelete false) []) "operator delete()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nfunction function_qualifiers.N (Nop $ OOCoawait) []) "operator coawait()" := eq_refl.
