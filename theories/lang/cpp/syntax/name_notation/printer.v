(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.bytestring_core.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.upoly.base.
Require Import bedrock.upoly.upoly.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.types.
Require Import bedrock.lang.cpp.syntax.pretty.

(* UPSTREAM? *)
Module showN.
  Definition showZ (z : Z) : bs :=
    (if bool_decide (z < 0)%Z then
      "-" ++ showN (Z.to_N $ Z.opp z)
    else showN $ Z.to_N z)%bs.
End showN.

(** Pretty printing of C++ names
    This printer is quite similar to the <pretty.v> printer, but this one is more
    restricted becuase it is important that this function is invertible by the parser
    in <parser.v>.
 *)
Section with_lang.
  Import UPoly.
  #[local] Open Scope bs_scope.
  Fixpoint sepBy (sep : bs) (ls : list bs) : bs :=
    match ls with
    | nil => ""
    | l :: nil => l
    | l :: ls => l ++ sep ++ sepBy sep ls
    end.
  Definition parens (b : bs) : bs := "(" ++ b ++ ")".
  Definition angles (b : bs) : bs := "<" ++ b ++ ">".

  #[local] Open Scope bs_scope.

  Definition prefix : bs -> bs -> bs := BS.append.
  Definition postfix (a b : bs) : bs := BS.append b a.

  Section atomic_name.
    Context {type Expr : Set} (printType : type -> option bs) (printExpr : Expr -> option bs).
    Variable top : option bs.

    Definition printFN (fn : function_name_ type) : option bs :=
      match fn with
      | Nf nm =>
          if bool_decide (nm = "") then mfail else mret nm
      | Nctor =>
          match top with
          | None => mfail
          | Some cls => mret cls
          end
      | Ndtor =>
          match top with
          | None => mfail
          | Some cls => mret $ "~" ++ cls
          end
      | Nop o =>
          match o with
          | OONew _ | OODelete _ | OOCoawait =>
            mret $ "operator" ++ printOO o
          | _ => mret $ "operator" ++ printOO o
          end
      | Nop_conv t => prefix "operator " <$> printType t
      | Nop_lit i => mret $ "operator """"_" ++ i
      | Nunsupported_function note => mfail
      end.

    #[local] Open Scope monad_scope.
    Definition printAN inst (an : atomic_name_ type) : option bs :=
      match an with
      | Nid id =>
          if bool_decide (id = "") then mfail else mret $ id ++ inst
      | Nfunction quals nm args =>
          let* nm := printFN nm in
          let* args := traverse (F:=eta option) printType args in
          mret $ nm ++ inst ++ parens (sepBy ", " args) ++
                 pretty.with_space (pretty.printFQ quals)
      | Nanonymous =>
          match inst with
          | BS.EmptyString => mret $ "(anon)"
          | _ => None
          end
      | Nanon n => mret $ "@" ++ showN n ++ inst
      | Nfirst_decl n => mret $ "@" ++ n ++ inst
      | Nfirst_child n => mret $ "." ++ n ++ inst
      | Nunsupported_atomic note => mfail
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

  Definition printBO (o : overloadable.RBinOp) : option bs :=
    let printBO o :=
      match o with
      | Badd => mret "+"
      | Band => mret "&&"
      | Bcmp => mret "<=>"
      | Bdiv => mret "/"
      | Beq => mret "=="
      | Bge => mret ">="
      | Bgt => mret ">"
      | Ble => mret "<="
      | Blt => mret "<"
      | Bmul => mret "*"
      | Bneq => mret "!="
      | Bor => mret "||"
      | Bmod => mret "%"
      | Bshl => mret "<<"
      | Bshr => mret ">>"
      | Bsub => mret "-"
      | Bxor => mret "^"
      | Bdotp => mret ".*"
      | Bdotip => mret "->*"
      | Bunsupported b => mfail
      end
    in
    match o with
    | overloadable.Rbinop b => printBO b
    | overloadable.Rassign => mret "="
    | overloadable.Rassign_op b => (fun a => a ++ "=") <$> printBO b
    | overloadable.Rsubscript => mret "[]"
    end.

  Fixpoint printN (inst : bs) (nm : name) : option bs :=
    match nm with
    | Nglobal an => printAN printT None inst an
    | Ndependent an => printT an
    | Nscoped base n =>
        (fun b n => b ++ "::" ++ n) <$> printN "" base <*> printAN printT (topName base) inst n
    | Ninst base i =>
        let printTA ta :=
          match ta with
          | Atype t => printT t
          | Avalue e => printE e
          | Apack _ => mfail
          | Aunsupported note => mfail
          end
        in
        ((fun tas => angles $ sepBy ", " tas) <$> traverse printTA i) ≫= fun tas =>
        printN tas base
    | Nunsupported note => mfail
    end

  with printT (ty : type) : option bs :=
    match ty with
    | Tint => mret "int"
    | Tuint => mret "unsigned int"
    | Tchar => mret "char"
    | Tuchar => mret "unsigned char"
    | Tschar => mret "signed char"
    | Tshort => mret "short"
    | Tushort => mret "unsigned short"
    | Tlong => mret "long"
    | Tulong => mret "unsigned long"
    | Tlonglong => mret "long long"
    | Tulonglong => mret "unsigned long long"
    | Tnum int_rank.I128 Signed => mret "int128_t"
    | Tnum int_rank.I128 Unsigned => mret "uint128_t"
    | Twchar => mret "wchar_t"
    | Tchar8 => mret "char8_t"
    | Tchar16 => mret "char16_t"
    | Tchar32 => mret "char32_t"
    | Tfloat => mret "float"
    | Tfloat16 => mret "float16"
    | Tfloat128 => mret "float128"
    | Tdouble => mret "double"
    | Tlongdouble => mret "long double"
    | Tbool => mret "bool"
    | Tnullptr => mret "nullptr_t"
    | Tptr (Tfunction (@FunctionType _ cc ar ret args)) =>
        if cc is CC_C then
          let add_dots (ls : list bs) :=
            match ar with
            | Ar_Variadic => (ls ++ ["..."])%list
            | _ => ls
            end
          in
          (fun ret args => ret ++ "(*)(" ++ sepBy "," (add_dots args) ++ ")")
            <$> printT ret <*> traverse printT args
        else mfail
    | Tptr t => postfix "*" <$> printT t
    | Tref t =>
        match t with
        | Tref _ | Trv_ref _ => postfix " &" <$> printT t
        | _ => postfix "&" <$> printT t
        end
    | Trv_ref t =>
        match t with
        | Tref _ | Trv_ref _ => postfix " &&" <$> printT t
        | _ => postfix "&&" <$> printT t
        end
    | Tmember_pointer cls t => (fun t c => t ++ " " ++ c ++ "::*") <$> printT t <*> printT cls
    | Tqualified QM _ => mfail
    | Tqualified q (Tqualified _ _) => mfail
       (* ^^ we reject sequences of [Tqualified] because it is not invertible *)
    | Tqualified cv t =>
        let q_ls := ((if q_const cv then ["const"] else []) ++
                    (if q_volatile cv then ["volatile"] else []))%list in
        match t with
        | Tptr _ | Tref _ | Trv_ref _ => fun t => sepBy " " $ t :: q_ls
        | _ => fun t => sepBy " " $ q_ls ++ [t]
        end%list <$> printT t
    | Tvoid => mret "void"
    | Tarray t n => (fun t => t ++ "[" ++ showN n ++ "]") <$> printT t
    | Tincomplete_array t => postfix "[]" <$> printT t
    | Tvariable_array t e => (fun t n => t ++ "[" ++ n ++ "]") <$> printT t <*> printE e
    | Tdecltype e => (fun e => "decltype((" ++ e ++ "))") <$> printE e
    | Texprtype e => (fun e => "decltype(" ++ e ++ ")") <$> printE e
    | Tnamed nm => printN "" nm
    | Tenum nm => prefix "enum " <$> printN "" nm
    | Tfunction ft =>
        let add_dots (ls : list bs) :=
          match ft.(ft_arity) with
          | Ar_Variadic => (ls ++ ["..."])%list
          | _ => ls
          end
        in
        if ft.(ft_cc) is CC_C then
          (fun t tas => t ++ "()" ++ parens (sepBy ", " $ add_dots tas))
            <$> printT ft.(ft_return)
            <*> traverse (T:=eta list) (F:=eta option) printT ft.(ft_params)
        else mfail
    | Tarch _ note => mfail
    | Tunsupported note => mfail
    | Tparam nm => mret $ "$" ++ nm
    | _ => mfail
    end

  with printE (e : Expr) : option bs :=
    match e with
    | Eglobal nm _ =>
      (* We can not support this in an invertible manner because of the type. *)
        None
    | Eint z ty => (fun suffix => showN.showZ z ++ suffix) <$>
        match ty with
        | Tint => mret ""
        | Tuint => mret "u"
(*        | Tlong => mret "l"
        | Tulong => mret "ul" *)
        | Tlonglong => mret "ll"
        | Tulonglong => mret "ull"
        | _ => mfail
        end
    | Ebool b => mret $ if b then "true" else "false"
    | Enull => mret "nullptr"
    | _ => mfail
    end.

End with_lang.

Definition print_name (input : name) : option (list Byte.byte) :=
  BS.print <$> printN "" input.

Definition print_type (input : type) : option (list Byte.byte) :=
  BS.print <$> printT input.

Module Type TESTS.
  #[local] Definition TEST (input : bs) (nm : name) : Prop :=
    (BS.parse <$> print_name nm) = Some input.

  #[local] Definition Msg : name := Nglobal $ Nid "Msg".

  Succeed Example _0 : TEST "Msg" Msg := eq_refl.
  Succeed Example _0 : TEST "Msg::@0" (Nscoped Msg (Nanon 0)) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg()" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::~Msg()" (Nscoped Msg (Nfunction function_qualifiers.N Ndtor [])) := eq_refl.

  Succeed Example _0 : TEST "Msg::Msg(int& &)" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Tref (Tref Tint)])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(int&& &)" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Tref (Trv_ref Tint)])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(int& &&)" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Trv_ref (Tref Tint)])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(int&& &&)" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Trv_ref (Trv_ref Tint)])) := eq_refl.


(*
  Example _0 :
    let targs := Avalue <$> [Eint 1 Tulong;
                             Eint (-2) Tlong;
                             Eint 3 Tulonglong;
                             Eint (-4) Tlonglong;
                             Eint 5 Tuint;
                             Eint 6 Tint] in
    TEST "Msg<1ul, -2l, 3ull, -4ll, 5u, 6>::Msg()" (Nscoped (Ninst Msg targs) (Nfunction function_qualifiers.N Nctor [])). compute.
  Succeed Example _0 :
    let targs := Atype <$> [Tulong;
                            Tlong;
                            Tulonglong;
                            Tlonglong;
                            Tuint; Tint] in
    TEST "Msg<unsigned long, long, unsigned long long, long long, unsigned int, int>::Msg()" (Nscoped (Ninst Msg targs) (Nfunction function_qualifiers.N Nctor [])) := eq_refl.
  *)
  Succeed Example _0 : TEST "Msg::Msg(int)" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Tint])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(long)" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Tlong])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator=(const Msg&)" (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator=(const Msg&&)" (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOEqual) [Trv_ref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator new()" (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OONew false)) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator new[]()" (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OONew true)) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator delete[]()" (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OODelete true)) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator int()" (Nscoped Msg (Nfunction function_qualifiers.N (Nop_conv Tint) [])) := eq_refl.
  Succeed Example _0 : TEST "foo_client(int[2]&, const int*, bool*, int**, char*)" (Nglobal (Nfunction function_qualifiers.N (Nf "foo_client") [Tref (Tarray Tint 2); Tptr (Tconst Tint); Tptr Tbool; Tptr (Tptr Tint); Tptr Tchar])) := eq_refl.
  Succeed Example _0 : TEST "DlistInternal::iterator::operator!=(const DlistInternal::iterator&) const"
                 (Nscoped (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))
                    (Nfunction function_qualifiers.Nc (Nop OOExclaimEqual) [Tref (Tqualified QC (Tnamed (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))))])) := eq_refl.
  Succeed Example _0 : TEST "intrusive::List_internal::iterator::iterator(intrusive::List_internal::Node*)"
                 (Nscoped (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "iterator"))
                    (Nfunction function_qualifiers.N Nctor [Tptr (Tnamed (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "Node")))])) := eq_refl.
  Succeed Example _0 : TEST "span<const int, 1ull>::span(const int*, unsigned long)"
                         (Nscoped (Ninst (Nglobal (Nid "span")) [Atype (Tqualified QC Tint);
                                                                 Avalue (Eint 1 Tulonglong)])
                            (Nfunction function_qualifiers.N Nctor [Tptr (Tqualified QC Tint); Tulong])) := eq_refl.
  Succeed Example _0 : TEST "integral" (Nglobal $ Nid "integral") := eq_refl.
  Succeed Example _0 : TEST "f<int>(int, int)" (Ninst (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tint; Tint]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f<int>(enum @1, enum en)" (Ninst (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tenum (Nglobal (Nanon 1)); Tenum (Nglobal (Nid "en"))]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f<int>(int(*)())" (Ninst (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tptr (Tfunction (FunctionType Tint []))]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f<int>(int()())" (Ninst (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tfunction (FunctionType Tint [])]) [Atype Tint]) := eq_refl.


End TESTS.
