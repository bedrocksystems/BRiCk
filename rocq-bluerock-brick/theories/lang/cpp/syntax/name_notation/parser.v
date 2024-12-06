(*
 * Copyright (C) BlueRock Security Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.prelude.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.upoly.upoly.
Require Import bedrock.upoly.option.
Require Import bedrock.upoly.list.
Require Import bedrock.prelude.parsec.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.types.


(** ** A parser for C++ names.

    This does not currently support all of C++ names, e.g. those
    that contain expressions. In general, it may be difficult to support
    some expressions.
 *)

Definition ident_char (b : Byte.byte) : bool :=
  let n := Byte.to_N b in
  bool_decide ((Reduce (Byte.to_N "a") ≤ n ≤ Reduce (Byte.to_N "z")) \/
               (Reduce (Byte.to_N "A") ≤ n ≤ Reduce (Byte.to_N "Z")) \/
               b = "_"%byte)%N.

Module parser.
  Import parsec.
  Import UPoly.

  #[local] Open Scope monad_scope.

  Section with_M.
    Context {Mbase : Type -> Type}.
    Context {RET : MRet Mbase} {FMAP : FMap Mbase} {AP : Ap Mbase} {MBIND : MBind Mbase}.

    Notation M := (parsec.M@{Set _ _ _ _ _ _} Byte.byte Mbase).

    Definition digit_char (b : Byte.byte) : bool :=
      bool_decide (Byte.to_N "0" ≤ Byte.to_N b ≤ Byte.to_N "9")%N.

    Definition ident : M bs :=
      let* f := char ident_char in
      (fun xs _ => BS.String f $ BS.parse xs)
        <$> star (char ident_char <|> digit)
        <*> not (charP (fun a => ident_char a || digit_char a)).

    Notation exact bs := (exact_bs bs).

    (* a maximal identifier *)
    Definition keyword (b : bs) : M unit :=
      let* _ := ws in
      let* _ := exact b in
      let* _ := not $ char (fun a => ident_char a || digit_char a) in
      ws.

    Definition punct_char (b : Byte.byte) : Prop :=
      let c : N := Byte.to_N b in
      (Reduce (Byte.to_N "!") <= c < Reduce (Byte.to_N "0"))%N \/
      (Reduce (Byte.to_N "9") < c < Reduce (Byte.to_N "A"))%N \/
      (Reduce (Byte.to_N "Z") < c < Reduce (Byte.to_N "a"))%N \/
      (Reduce (Byte.to_N "z") < c < 127)%N.

    Definition space_char (b : Byte.byte) : Prop :=
      let c : N := Byte.to_N b in
      c ∈ [9; 10; 11; 12; 13; 32]%N.

    (* TODO: ideally, i would like to say that this does not contain additional characters. *)
    Definition op_token (b : bs) : M unit :=
      let* _ := ws in
      let* _ := exact b in
      ws.

    Definition decimal : M N :=
      let make ls := fold_left (fun acc x => 10 * acc + x)%N ls 0%N in
      make <$> plus ((fun x => Byte.to_N x - Byte.to_N "0")%N <$> digit).

    Definition parse_qualifiers : M function_qualifiers.t :=
      let quals :=
        star (anyOf $ [const function_qualifiers.Nc <$> keyword "const";
                       const function_qualifiers.Nv <$> keyword "volatile";
                       const function_qualifiers.Nr <$> op_token "&&";
                       const function_qualifiers.Nl <$> op_token "&"]) in
      fold_right function_qualifiers.join function_qualifiers.N <$> quals.

    Definition basic_types {lang} : list (list bs * type' lang) :=
      let s_or_u_l (b : list bs) (s u : type' lang) :=
        [(b, s); ("signed" :: b, s); ("unsigned" :: b, u)]%bs
      in
      let s_or_u b := s_or_u_l [b] in
      [ (["bool"], Tbool)
      ; (["void"], Tvoid)
      ; (["nullptr_t"], Tnullptr)
      ; (["float16"], Tfloat16)
      ; (["float128"], Tfloat128)
      ; (["float"], Tfloat)
      ; (["double"], Tdouble)
      ; (["long"; "double"], Tlongdouble)
      ; (["char"], Tchar)
      ; (["unsigned"; "char"], Tuchar)
      ; (["signed"; "char"], Tschar)
      ; (["uint128_t"], Tuint128_t)
      ; (["int128_t"], Tint128_t) ]%bs ++
      s_or_u "int128"%bs Tint128_t Tuint128_t ++
      s_or_u "__int128"%bs Tint128_t Tuint128_t ++
      s_or_u "short"%bs Tshort Tushort ++
      s_or_u "int"%bs Tint Tuint ++
      s_or_u_l ["long";"long"]%bs Tlonglong Tulonglong ++
      s_or_u "long"%bs Tlong Tulong ++
      [ (["unsigned"], Tuint)
      ; (["signed"], Tint) ]%bs.

    Definition basic_type {lang} : M (type' lang) :=
      let os : list (M (type' lang)) :=
        fmap (M:=eta list) (fun '(tkns, val) => fmap (M:=M) (fun _ => val) (seqs $ fmap (M:=eta list) keyword tkns)) basic_types in
      anyOf os.

    Definition operators : list (bs * OverloadableOperator) :=
      (* this is used in an early commit manner, so longer operators
         need to come first
         TODO: list is incomplete
       *)
      [ ("~", OOTilde)
      ; ("<=>", OOSpaceship)
      ; ("!=", OOExclaimEqual)
      ; ("!", OOExclaim)
      ; ("++", OOPlusPlus)
      ; ("--", OOMinusMinus)
      ; ("&&", OOAmpAmp)
      ; ("||", OOPipePipe)
      ; ("==", OOEqualEqual)
      ; ("=", OOEqual)
      ; ("<<=", OOLessLessEqual)
      ; (">>=", OOGreaterGreaterEqual)
      ; ("<=", OOLessEqual)
      ; ("<<", OOLessLess)
      ; (">=", OOGreaterEqual)
      ; (">>", OOGreaterGreater)
      ; ("+=", OOPlusEqual)
      ; ("-=", OOMinusEqual)
      ; ("%=", OOPercentEqual)
      ; ("/=", OOSlashEqual)
      ; ("*=", OOStarEqual)
      ; ("&=", OOAmpEqual)
      ; ("|=", OOPipeEqual)
      ; ("^=", OOCaretEqual)
      ; ("->*", OOArrowStar)
      ; ("->", OOArrow)
      ; ("<", OOLess)
      ; (">", OOGreater)
      ; ("[]", OOSubscript)
      ; ("()", OOCall)
      ; ("new[]", OONew true)
      ; ("delete[]", OODelete true)
      ; ("new", OONew false)
      ; ("delete", OODelete false)
      ; ("co_await", OOCoawait)
      ; (",", OOComma)
      ; ("*", OOStar)
      ; ("+", OOPlus)
      ; ("-", OOMinus)
      ; ("/", OOSlash)
      ; ("%", OOPercent)
      ; ("&", OOAmp)
      ; ("^", OOCaret)
      ; ("|", OOPipe)
      ]%bs.

    Definition operator : M OverloadableOperator :=
      let* _ := ws in
      let* res := (anyOf $ (fun '(lex, syn) => const syn <$> exact lex) <$> operators) in
      let* _ := ws in
      mret res.

    Definition spaced (b : bs) : M unit :=
      let* _ := ws in
      let* _ := exact b in
      ws.

    Definition get_args {lang} (ls : list (type' lang)) : list (type' lang) :=
      match ls with
      | [Tvoid] => []
      | _ => ls
      end.

    Definition NEXT {T} (n : nat) (f : nat -> M T) : M T :=
      match n with
      | 0 => mfail
      | S n => f n
      end.

  End with_M.

  #[local] Definition M := (parsec.M Byte.byte (eta option)).

  #[local] Instance M_ret : MRet M := _.
  #[local] Instance M_map : FMap M := _.
  #[local] Instance M_ap : Ap M := _.
  #[local] Instance M_bind : MBind M := _.
  #[local] Instance M_alt : Alternative M := _.

  Definition run {T} (m : M T) (str : bs) : option (bs * T) :=
    match parsec.run_bs m str with
    | Some (Datatypes.Some (rest, result)) => Some (rest, result)
    | _ => None
    end.

  Definition run_full {T} (p : M T) (str : bs) : option T :=
    let m : M T := (fun x _ => x) <$> p <*> eos in
    fmap (M:=eta option) (fun '(_,b) => b) $ run m str.

  Notation exact bs := (exact_bs bs).

  Section with_lang.
    Context {lang : lang.t}.
    Notation type := (type' lang).
    Notation name := (name' lang).

    (** classification of names based to account for destructors and overloadable
        operators. *)
    Variant name_type : Set :=
      | Simple (_ : bs)
      | Dtor (_ : bs)
      | FirstDecl (_ : bs)
      | FirstChild (_ : bs)
      | Anon (_ : N)
      | Op (_ : OverloadableOperator)
      | OpConv (_ : type)
      | OpLit (_ : bs).


    Section body.
      Variable parse_type : unit -> M type.
      Variable parse_name : unit -> M name.
      Variable parse_name_component : unit -> M (atomic_name' lang * option (list (temp_arg' lang))).
      Variable parse_expr : unit -> M (Expr' lang).

      Definition parse_args : M (list type * function_arity) :=
        let args := sepBy (spaced ",") (parse_type ()) in
        let arity :=
          let arity a :=
            match a with
            | None => Ar_Definite
            | Some _ => Ar_Variadic
            end
          in
          arity <$> optional ((fun _ _ => ()) <$> spaced "," <*> spaced "...")
        in
        quoted (spaced "(") (spaced ")") (pair <$> (get_args <$> args) <*> arity).

      Definition parse_postfix_type : M (type -> type) :=
        let entry :=
          let* _ := ws in
          (let* _ := exact "&&" in mret Trv_ref) <|>
            (let* _ := exact "&" in mret Tref) <|>
            (let* _ := exact "*" in mret Tptr) <|>
            (let* _ := keyword "const" in mret $ fun x => tqualified QC x) <|>
            (let* _ := keyword "volatile" in mret $ fun x => tqualified QV x) <|>
            (let* _ := spaced "[]" in
             mret (fun x => Tincomplete_array x)) <|>
            (let* _ := exact "[" in
             let* n := decimal in
             let* _ := exact "]" in
             mret (fun x => Tarray x n))  <|>
            (let* _ := exact "[" in
             let* n := parse_expr () in
             let* _ := exact "]" in
             mret (fun x => Tvariable_array x n)) <|>
            (let* _ := spaced "(" in
             let* _ := exact "*" in
             let* _ := spaced ")" in
             let* '(args, ar) := parse_args in
             mret (fun rt => Tptr $ Tfunction (FunctionType (ft_arity:=ar) rt args))) <|>
            (let* _ := spaced "(" in
             let* nm := parse_name () in
             let* _ := spaced "::" in
             let* _ := exact "*" in
             let* _ := spaced ")" in
             let* '(args, ar) := parse_args in
             mret (fun rt => Tmember_pointer (Tnamed nm) $ Tfunction (FunctionType (ft_arity:=ar) rt args)))
        in
        fold_left (fun t f => f t) <$> star entry.


    (* The core parsers are based on fuel to handle the mutual recursion *)
    Definition parse_type' : M type :=
      let* quals :=
        star (((fun _ => tqualified (lang:=lang) QC) <$> keyword "const") <|>
              ((fun _ => tqualified QV) <$> keyword "volatile"))
      in
      let* t :=
        basic_type <|>
        ((fun _ => Tparam) <$> exact "$" <*> ident) <|>
        ((fun _ => Tenum) <$> (exact "#" <|> spaced "enum") <*> parse_name ()) <|>
        ((fun _ => Tnamed) <$> optional (spaced "struct" <|> spaced "class") <*> parse_name ())
      in
      let* post := parse_postfix_type in
      mret $ post (List.fold_right (fun f x => f x) t quals).

   Definition parse_name': M name :=
     ((fun _ => Ndependent) <$> spaced "typename" <*> parse_type ()) <|>
     (let* (x : list (atomic_name' _ * _)) :=
        (fun _ x => x) <$> optional (spaced "::") <*> sepBy (spaced "::") (parse_name_component ())
      in
      match x with
      | nil => mfail (* unreachable *)
      | (nm, oinst) :: xs =>
          let sp oi :=
            match oi with
            | None => fun x => x
            | Some i => fun x => Ninst x i
            end
          in
          let* root :=
            (mret $ sp oinst $ Nglobal nm)
          in
          mret (List.fold_left (fun '(acc, last) '(nm, oinst) =>
                                  match nm with
                                  | Nfunction function_qualifiers.N (Nf fnm) args =>
                                      if bool_decide (Nid fnm = last) then
                                        (sp oinst (Nscoped acc $ Nfunction function_qualifiers.N Nctor args), nm)
                                      else
                                        (sp oinst (Nscoped acc nm), nm)
                                  | _ =>
                                      (sp oinst (Nscoped acc nm), nm)
                                  end) xs
            (root, nm)).1
      end).

    (* name components basically amount to atomic names with an optional template
       specialization after them. They are complex because function names include their
       arguments.
     *)
    Definition parse_name_component' : M (atomic_name' lang * option (list (temp_arg' _))) :=
      let* (nm : name_type) :=
        let* op := optional (keyword "operator") in
        match op with
        | None => let* d := optional (op_token "~") in
                 match d with
                 | None =>
                     let* d := optional (exact "@") in
                     match d with
                     | None =>
                         let* d := optional (exact ".") in
                         match d with
                         | None => Simple <$> ident
                         | Some _ => FirstChild <$> ident
                         end
                     | Some _ => (Anon <$> decimal) <|> (FirstDecl <$> ident)
                     end
                 | Some _ => Dtor <$> ident
                 end
        | Some _ =>
            (Op <$> operator) <|>
            (OpConv <$> parse_type ()) <|>
            (const OpLit <$> exact """""_" <*> ident)
        end
      in
      let mk_atomic_name (nm : name_type) (args : option _) : M (atomic_name' _) :=
        match args with
        | None => match nm with
                 | Simple nm => mret $ Nid nm
                 | FirstDecl nm => mret $ Nfirst_decl nm
                 | FirstChild nm => mret $ Nfirst_child nm
                 | Anon n => mret $ Nanon n
                 | Dtor _
                 | Op _
                 | OpLit _
                 | OpConv _ => mfail
                 end
        | Some (args, ar, quals) =>
            (fun nm => Nfunction quals nm args) <$>
              match nm with
              | Dtor _ => mret $ Ndtor
              | Simple nm => mret $ Nf nm
              | Op oo => mret $ Nop oo
              | OpConv t => mret $ Nop_conv t
              | OpLit n => mret $ Nop_lit n
              | FirstDecl n => mfail
              | FirstChild n => mfail
              | Anon _ => mfail
              end
        end
      in
      let parse_args : M _ :=
        optional (let* '(args, arity) := parse_args in
                  let* quals := parse_qualifiers in
                  mret (args, arity, quals))
      in
      let* template_args :=
        let template_arg :=
          (Atype <$> parse_type ()) <|> (Avalue <$> parse_expr ()) in
        optional (quoted (spaced "<") (spaced ">") $ sepBy (op_token ",") template_arg) in
      let* nm := let* a := parse_args in mk_atomic_name nm a in
      mret (nm, template_args)
    .

    Definition parse_z : M Z :=
      let num sgn n :=
        match sgn with
        | None => Z.of_N n
        | Some _ => Z.opp $ Z.of_N n
        end
      in
      num <$> optional (op_token "-") <*> decimal.

    Definition parse_expr' : M (Expr' lang) :=
      let* _ := ws in
      let int_literal :=
        let* num := parse_z in
        let* suffix := optional (anyOf [(const Tlonglong <$> keyword "ll");
                                        (const Tlong <$> keyword "l");
                                        (const Tulonglong <$> keyword "ull");
                                        (const Tulong <$> keyword "ul");
                                        (const Tuint <$> keyword "u")]) in
        let ty :=
          match suffix with
          | None => Tint
          | Some ty => ty
          end
        in
        mret $ Eint num ty
      in
      let char_literal :=
        let* ty := optional (anyOf [(const Tchar8 <$> keyword "u8");
                                     (const Tchar16 <$> keyword "u");
                                     (const Tchar32 <$> keyword "U");
                                     (const Twchar <$> keyword "L")]) in
        let ty : type :=
          match ty with
          | None => Tchar
          | Some t => t
          end
        in
        let* _ := optional (exact "'") in
        mfail
      in
      let simple_literal :=
        anyOf [(const (Ebool true) <$> keyword "true");
                 (const (Ebool false) <$> keyword "false");
                 (const Enull <$> keyword "nullptr")]
      in
      let global :=
        (* NOTE: there is no way to get the type of the global here.
           To make this work, we need to remove this information from
           the expression. *)
        Eglobal <$> parse_name () <*> mfail
      in
      int_literal <|> char_literal <|> simple_literal <|> global.
    End body.

    Fixpoint parse_type (fuel : nat) :=
      parse_type' (fun _ => NEXT fuel parse_type) (fun _ => NEXT fuel parse_name) (fun _ => NEXT fuel parse_expr)
    with parse_name (fuel : nat) :=
      parse_name' (fun _ => NEXT fuel parse_type) (fun _ => NEXT fuel parse_name_component)
    with parse_name_component (fuel : nat) :=
      parse_name_component' (fun _ => NEXT fuel parse_type) (fun _ => NEXT fuel parse_expr)
    with parse_expr (fuel : nat) :=
      parse_expr' (fun _ => NEXT fuel parse_name).

  End with_lang.

End parser.

Definition parse_name (input : list Byte.byte) : option name :=
  parser.run_full (parser.parse_name 1000) $ BS.parse input.

Definition parse_type (input : list Byte.byte) : option type :=
  parser.run_full (parser.parse_type 1000) $ BS.parse input.

Module Type TESTS.
  #[local] Definition TEST (input : bs) (nm : name) : Prop :=
    (parse_name $ BS.print input) = Some nm.

  #[local] Definition Msg : name := Nglobal $ Nid "Msg".

  Succeed Example _0 : TEST "Msg" Msg := eq_refl.
  Succeed Example _0 : TEST "::Msg" Msg := eq_refl.
  Succeed Example _0 : TEST "Msg::@0" (Nscoped Msg (Nanon 0)) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg()" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::~Msg()" (Nscoped Msg (Nfunction function_qualifiers.N Ndtor [])) := eq_refl.
  Succeed Example _0 :
    let targs := Avalue <$> [Eint 1 Tulong;
                             Eint (-2) Tlong;
                             Eint 3 Tulonglong;
                             Eint (-4) Tlonglong;
                             Eint 5 Tuint;
                             Eint 6 Tint] in
    TEST "Msg<1ul, -2l, 3ull, -4ll, 5u, 6>::Msg()" (Nscoped (Ninst Msg targs) (Nfunction function_qualifiers.N Nctor [])) := eq_refl.
  Succeed Example _0 :
    let targs := Atype <$> [Tulong;
                            Tlong;
                            Tulonglong;
                            Tlonglong;
                            Tuint; Tint] in
    TEST "Msg<unsigned long, long, unsigned long long, long long, unsigned int, int>::Msg()" (Nscoped (Ninst Msg targs) (Nfunction function_qualifiers.N Nctor [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(int)" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Tint])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(long)" (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Tlong])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator=(const Msg&)" (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator=(const Msg&&)" (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOEqual) [Trv_ref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator new()" (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OONew false)) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator new[]()" (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OONew true)) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator   delete()" (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OODelete false)) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator delete[]()" (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OODelete true)) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator int()" (Nscoped Msg (Nfunction function_qualifiers.N (Nop_conv Tint) [])) := eq_refl.
  Succeed Example _0 : TEST "foo_client(int[2]&, int const*, bool*, int**, char*)" (Nglobal (Nfunction function_qualifiers.N (Nf "foo_client") [Tref (Tarray Tint 2); Tptr (Tconst Tint); Tptr Tbool; Tptr (Tptr Tint); Tptr Tchar])) := eq_refl.
  Succeed Example _0 : TEST "DlistInternal::iterator::operator!=(const DlistInternal::iterator&) const"
                 (Nscoped (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))
                    (Nfunction function_qualifiers.Nc (Nop OOExclaimEqual) [Tref (Tqualified QC (Tnamed (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))))])) := eq_refl.
  Succeed Example _0 : TEST "intrusive::List_internal::iterator::iterator(intrusive::List_internal::Node*)"
                 (Nscoped (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "iterator"))
                    (Nfunction function_qualifiers.N Nctor [Tptr (Tnamed (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "Node")))])) := eq_refl.
  Succeed Example _0 : TEST "span<const int, 1ul>::span(const int*, unsigned long)"
                         (Nscoped (Ninst (Nglobal (Nid "span")) [Atype (Tqualified QC Tint);
                                                                 Avalue (Eint 1 Tulong)])
                            (Nfunction function_qualifiers.N Nctor [Tptr (Tqualified QC Tint); Tulong])) := eq_refl.
  Succeed Example _0 : TEST "integral" (Nglobal $ Nid "integral") := eq_refl.
  Succeed Example _0 : TEST "f<int>(int, int)" (Ninst (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tint; Tint]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f<int>(#e1, const #e2)" (Ninst (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tenum (Nglobal (Nid "e1")); Tconst $ Tenum (Nglobal (Nid "e2"))]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f(int[], int[3])" (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tincomplete_array Tint; Tarray Tint 3]) := eq_refl.
  Succeed Example _0 : TEST "f(const volatile int[], int[3])" (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tincomplete_array (Tqualified QCV Tint); Tarray Tint 3]) := eq_refl.
  Succeed Example _0 : TEST "f(void)" (Nglobal $ Nfunction function_qualifiers.N (Nf "f") []) := eq_refl.
  Succeed Example _0 : TEST "::f(void)" (Nglobal $ Nfunction function_qualifiers.N (Nf "f") []) := eq_refl.
  Succeed Example _0 : TEST "::f(#::foo)" (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tenum $ Nglobal $ Nid "foo"]) := eq_refl.

  Succeed Example _0 : TEST "operator """"_f(enum ::foo)" (Nglobal $ Nfunction function_qualifiers.N (Nop_lit "f") [Tenum $ Nglobal $ Nid "foo"]) := eq_refl.


  Succeed Example _0 : TEST "::f(enum ::foo)" (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tenum $ Nglobal $ Nid "foo"]) := eq_refl.
  Succeed Example _0 : TEST "::f(struct ::foo)" (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tnamed $ Nglobal $ Nid "foo"]) := eq_refl.
  Succeed Example _0 : TEST "::f(class ::foo)" (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tnamed $ Nglobal $ Nid "foo"]) := eq_refl.
  Succeed Example _0 : TEST "::f(::foo)" (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tnamed $ Nglobal $ Nid "foo"]) := eq_refl.
  Succeed Example _0 : TEST "CpuSet::forall(void (*)(int)) const"
                 (Nscoped (Nglobal (Nid "CpuSet")) (Nfunction function_qualifiers.Nc (Nf "forall") [Tptr $ Tfunction (FunctionType Tvoid [Tint])])) := eq_refl.
  Succeed Example _0 : TEST "CpuSet::forall(void (C::*)(int)) const"
                         (Nscoped (Nglobal (Nid "CpuSet")) (Nfunction function_qualifiers.Nc (Nf "forall") [Tmember_pointer (Tnamed (Nglobal $ Nid "C")) $ Tfunction (FunctionType Tvoid [Tint])])) := eq_refl.

  Succeed Example _0 : TEST "CpuSet::forall(void (C::*)(int), ...) const"
                         (Nscoped (Nglobal (Nid "CpuSet")) (Nfunction function_qualifiers.Nc (Nf "forall") [Tmember_pointer (Tnamed (Nglobal $ Nid "C")) $ Tfunction (FunctionType Tvoid [Tint])])) := eq_refl.
  Succeed Example _0 : TEST "CpuSet::forall(void (C::*)(int, ...), ...) const"
                         (Nscoped (Nglobal (Nid "CpuSet")) (Nfunction function_qualifiers.Nc (Nf "forall") [Tmember_pointer (Tnamed (Nglobal $ Nid "C")) $ Tfunction (FunctionType (ft_arity:=Ar_Variadic) Tvoid [Tint])])) := eq_refl.

  Succeed Example _0 : TEST "foo(unsigned int128, int128)" (Nglobal (Nfunction function_qualifiers.N (Nf "foo") [Tuint128_t; Tint128_t])) := eq_refl.

  (* NOTE: non-standard names *)
  Succeed Example _0 : TEST "Msg::@msg" (Nscoped Msg (Nfirst_decl "msg")) := eq_refl.
  Succeed Example _0 : TEST "Msg::.msg" (Nscoped Msg (Nfirst_child "msg")) := eq_refl.
  Succeed Example _0 : TEST "typename foo" (Ndependent (Tnamed (Nglobal (Nid "foo")))) := eq_refl.
  Succeed Example _0 : TEST "typename foo<int>::type"
                 (Ndependent (Tnamed (Nscoped (Ninst (Nglobal (Nid "foo")) [Atype Tint]) (Nid "type")))) := eq_refl.

  Succeed Example _0 : TEST "Msg<int& &&>" (Ninst (Nglobal (Nid "Msg")) [Atype (Trv_ref (Tref Tint))]) := eq_refl.

End TESTS.
