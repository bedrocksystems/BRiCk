(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.syntax.prelude.
Require Import bedrock.lang.cpp.syntax.core.

(* parsing the left will produce the righ *and* printing the right will produce the left *)
Definition canonical : list (bs * name) :=
  let Msg : name := Nglobal $ Nid "Msg" in
  [ ("Msg", Msg)
  ; ("Msg::@0", (Nscoped Msg (Nanon 0)))
  ; ("Msg::Msg()", (Nscoped Msg (Nfunction function_qualifiers.N Nctor [])))
  ; ("Msg::~Msg()", (Nscoped Msg (Nfunction function_qualifiers.N Ndtor [])))
  ; ("Msg::Msg(int)", (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Tint])) )
  ; ("Msg::Msg(long)", (Nscoped Msg (Nfunction function_qualifiers.N Nctor [Tlong])) )
  ; ("Msg::operator=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator<(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOLess) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator>(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOGreater) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator==(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOEqualEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator!=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOExclaimEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator<=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOLessEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator>=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOGreaterEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator>>=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOGreaterGreaterEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator<<=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOLessLessEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator+=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOPlusEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator-=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOMinusEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator*=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOStarEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator/=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOSlashEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator%=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOPercentEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator|=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOPipeEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator&=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOAmpEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator^=(const Msg&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOCaretEqual) [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )

  ; ("Msg::operator=(const Msg&&)", (Nscoped Msg (Nfunction function_qualifiers.N (Nop OOEqual) [Trv_ref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator new()", (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OONew false)) [])) )
  ; ("Msg::operator new[]()", (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OONew true)) [])) )
  ; ("Msg::operator delete[]()", (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OODelete true)) [])) )
  ; ("Msg::operator int()", (Nscoped Msg (Nfunction function_qualifiers.N (Nop_conv Tint) [])) )
  ; ("foo_client(int[2]&, const int*, bool*, int**, char*)", (Nglobal (Nfunction function_qualifiers.N (Nf "foo_client") [Tref (Tarray Tint 2); Tptr (Tconst Tint); Tptr Tbool; Tptr (Tptr Tint); Tptr Tchar])) )
  ; ("DlistInternal::iterator::operator!=(const DlistInternal::iterator&) const",
                 (Nscoped (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))
                    (Nfunction function_qualifiers.Nc (Nop OOExclaimEqual) [Tref (Tqualified QC (Tnamed (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))))])))
  ; ("intrusive::List_internal::iterator::iterator(intrusive::List_internal::Node*)",
                 (Nscoped (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "iterator"))
                    (Nfunction function_qualifiers.N Nctor [Tptr (Tnamed (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "Node")))])))
  ; ("integral", (Nglobal $ Nid "integral") )
  ; ("f<int>(int, int)", (Ninst (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tint; Tint]) [Atype Tint]) )
  ; ("f<int>(enum @1, enum en)", (Ninst (Nglobal $ Nfunction function_qualifiers.N (Nf "f") [Tenum (Nglobal (Nanon 1)); Tenum (Nglobal (Nid "en"))]) [Atype Tint]))
  ]%bs.

(* parsing the left will produce the right *)
Definition parse_only : list (bs * name) :=
  let Msg : name := Nglobal $ Nid "Msg" in
  [ ("::Msg", Msg)
  ; ("Msg::operator   delete()", (Nscoped Msg (Nfunction function_qualifiers.N (Nop (OODelete false)) [])) )
  ; ("span<const int, 1ul>::span(const int*, unsigned long)",
        (Nscoped (Ninst (Nglobal (Nid "span")) [Atype (Tqualified QC Tint);
                                                Avalue (Eint 1 Tulong)])
           (Nfunction function_qualifiers.N Nctor [Tptr (Tqualified QC Tint); Tulong])))
  ; let targs := Avalue <$> [Eint 1 Tulong;
                              Eint (-2) Tlong;
                              Eint 3 Tulonglong;
                              Eint (-4) Tlonglong;
                              Eint 5 Tuint;
                              Eint 6 Tint] in
    ("Msg<1ul, -2l, 3ull, -4ll, 5u, 6>::Msg()", (Nscoped (Ninst Msg targs) (Nfunction function_qualifiers.N Nctor [])))
  ; let targs := Atype <$> [Tulong;
                            Tlong;
                            Tulonglong;
                            Tlonglong;
                            Tuint; Tint] in
    ("Msg<unsigned long, long, unsigned long long, long long, unsigned int, int>::Msg()", (Nscoped (Ninst Msg targs) (Nfunction function_qualifiers.N Nctor [])))
  ; ("foo_client(int[2]&, const int*, bool*, int**, char*)", (Nglobal (Nfunction function_qualifiers.N (Nf "foo_client") [Tref (Tarray Tint 2); Tptr (Tconst Tint); Tptr Tbool; Tptr (Tptr Tint); Tptr Tchar])) )
  ]%bs.
