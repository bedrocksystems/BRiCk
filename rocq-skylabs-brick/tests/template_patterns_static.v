(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Template patterns belong to the template tables ([mtypes], [msymbols],
    [maliases]), not to the static ones ([types], [symbols]). Patterns
    reached outside a class template's body (out-of-line member definitions)
    used to land in the static tables when templates are enabled, so the
    static part of a translation unit depended on [no_templates]. libstdc++ has all the shapes below (e.g.
    [std::num_put<$_CharT, $_OutIter>::do_put(...)::__cache_type],
    [std::basic_istream<$_CharT, $_Traits>::sentry],
    [__gnu_cxx::__numeric_traits_integer<$_Value>::__min]). *)

Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.sub_module.

#[with_templates]
cpp.prog with_tpl prog cpp:{{
  // A local typedef and a local class in an out-of-line member definition.
  template<class T> struct Box { T v; int get() const; };
  template<class T> int Box<T>::get() const {
    typedef T elem;
    struct L { elem e; };
    L l{v};
    return sizeof(l);
  }
  int use_box() { Box<int> b{1}; return b.get(); }

  // An out-of-line static data member.
  template<class T> struct Traits { static const int digits; };
  template<class T> const int Traits<T>::digits = sizeof(T) * 8;
  int use_traits() { return Traits<int>::digits; }

  // An out-of-line member class.
  template<class T> struct Outer { struct Inner; };
  template<class T> struct Outer<T>::Inner { typedef T type; T t; };
  Outer<int>::Inner use_outer;
}}.

#[no_templates]
cpp.prog without_tpl prog cpp:{{
  // A local typedef and a local class in an out-of-line member definition.
  template<class T> struct Box { T v; int get() const; };
  template<class T> int Box<T>::get() const {
    typedef T elem;
    struct L { elem e; };
    L l{v};
    return sizeof(l);
  }
  int use_box() { Box<int> b{1}; return b.get(); }

  // An out-of-line static data member.
  template<class T> struct Traits { static const int digits; };
  template<class T> const int Traits<T>::digits = sizeof(T) * 8;
  int use_traits() { return Traits<int>::digits; }

  // An out-of-line member class.
  template<class T> struct Outer { struct Inner; };
  template<class T> struct Outer<T>::Inner { typedef T type; T t; };
  Outer<int>::Inner use_outer;
}}.

(** The static entries that only exist with templates enabled. *)
Definition only_with_templates {A} (with_ without : NM.t A) : list name :=
  filter (fun n => bool_decide (without !! n = None)) (NM.elements with_).*1.

Eval vm_compute in only_with_templates with_tpl.(types) without_tpl.(types).
Eval vm_compute in only_with_templates with_tpl.(symbols) without_tpl.(symbols).

(** Enabling templates does not change the static part, so units generated
    with and without templates are [sub_module]s of each other. *)
Example static_part_independent_of_templates :
  module_le with_tpl without_tpl && module_le without_tpl with_tpl = true.
Proof. vm_compute. reflexivity. Qed.

(** * The patterns are in the static tables of neither unit... *)

Example local_typedef_not_static :
  with_tpl.(types) !! "Box<$T>::get() const::elem"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example local_class_not_static :
  with_tpl.(types) !! "Box<$T>::get() const::L"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example static_member_not_static :
  with_tpl.(symbols) !! "Traits<$T>::digits"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example member_class_not_static :
  with_tpl.(types) !! "Outer<$T>::Inner"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example member_class_typedef_not_static :
  with_tpl.(types) !! "Outer<$T>::Inner::type"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

(** * ...while the instances are *)

Example local_typedef_instance :
  is_Some (with_tpl.(types) !! "Box<int>::get() const::elem"%cpp_name).
Proof. vm_compute. eauto. Qed.

Example static_member_instance :
  is_Some (with_tpl.(symbols) !! "Traits<int>::digits"%cpp_name).
Proof. vm_compute. eauto. Qed.

Example member_class_instance :
  is_Some (with_tpl.(types) !! "Outer<int>::Inner"%cpp_name).
Proof. vm_compute. eauto. Qed.

(** * The patterns are in the template tables *)

Example local_typedef_pattern :
  is_Some (translation_unit.maliases with_tpl !! "Box<$T>::get() const::elem"%cpp_name).
Proof. vm_compute. eauto. Qed.

Example local_class_pattern :
  is_Some (translation_unit.mtypes with_tpl !! "Box<$T>::get() const::L"%cpp_name).
Proof. vm_compute. eauto. Qed.

Example static_member_pattern :
  is_Some (translation_unit.msymbols with_tpl !! "Traits<$T>::digits"%cpp_name).
Proof. vm_compute. eauto. Qed.

Example member_class_pattern :
  is_Some (translation_unit.mtypes with_tpl !! "Outer<$T>::Inner"%cpp_name).
Proof. vm_compute. eauto. Qed.

Example member_class_typedef_pattern :
  is_Some (translation_unit.maliases with_tpl !! "Outer<$T>::Inner::type"%cpp_name).
Proof. vm_compute. eauto. Qed.
