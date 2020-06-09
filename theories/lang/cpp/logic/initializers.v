(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Local Open Scope Z_scope.

Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred call wp.

Module Type Init.

  Section with_resolve.
    Context `{Σ : cpp_logic thread_info} {σ:genv}.
    Variables (M : coPset) (ti : thread_info) (ρ : region).

    Local Notation wp := (wp (resolve:=σ) M ti ρ).
    Local Notation wpi := (wpi (resolve:=σ) M ti ρ).
    Local Notation wpe := (wpe (resolve:=σ) M ti ρ).
    Local Notation wp_lval := (wp_lval (resolve:=σ) M ti ρ).
    Local Notation wp_rval := (wp_rval (resolve:=σ) M ti ρ).
    Local Notation wp_prval := (wp_prval (resolve:=σ) M ti ρ).
    Local Notation wp_xval := (wp_xval (resolve:=σ) M ti ρ).
    Local Notation wp_init := (wp_init (resolve:=σ) M ti ρ).
    Local Notation wp_args := (wp_args (σ:=σ) M ti ρ).
    Local Notation fspec := (fspec ti).

    Local Notation _global := (_global (resolve:=σ)) (only parsing).
    Local Notation _field := (_field (resolve:=σ)) (only parsing).
    Local Notation _sub := (_sub (resolve:=σ)) (only parsing).
    Local Notation _super := (_super (resolve:=σ)) (only parsing).
    Local Notation primR := (primR (resolve:=σ)) (only parsing).
    Local Notation anyR := (anyR (resolve:=σ)) (only parsing).
    Local Notation offset_for := (offset_for σ) (only parsing).


    (* this is really about expression evaluation, so it doesn't make sense for
     * it to be recursive on a type.
     *)
    Fixpoint wp_initialize (ty : type) (addr : val) (init : Expr) (k : FreeTemps -> mpred)
    {struct ty} : mpred :=
      match ty with
      | Tvoid => lfalse
      | Tpointer _
      | Tmember_pointer _ _
      | Tbool
      | Tint _ _ =>
        wp_prval init (fun v free =>
                         _at (_eqv addr) (anyR (erase_qualifiers ty) 1) **
                         (   _at (_eqv addr) (primR (erase_qualifiers ty) 1 v)
                          -* k free))

        (* non-primitives are handled via prvalue-initialization semantics *)
      | Tarray _ _
      | Tnamed _ => wp_init ty addr (not_mine init) k

      | Treference t => lfalse (* reference fields are not supported *)
      | Trv_reference t => lfalse (* reference fields are not supported *)
      | Tfunction _ _ => lfalse (* functions not supported *)

      | Tqualified _ ty => wp_initialize ty addr init k
      | Tnullptr => lfalse (* nullptr fields are not supported *)
      | Tarch _ _ => lfalse (* vendor-specific types are not supported *)
      | Tfloat _ => lfalse (* floating point numbers are not supported *)
      end.

    Axiom wpi_initialize : forall this_val i cls Q,
        Exists a,
          _offsetL (offset_for cls i.(init_path)) (_eqv this_val) &~ a ** ltrue //\\
        wp_initialize (erase_qualifiers i.(init_type)) (Vptr a) i.(init_init) Q
        |-- wpi cls this_val i Q.

    Fixpoint wpis (cls : globname) (this : val)
             (inits : list Initializer)
             (Q : mpred -> mpred) : mpred :=
      match inits with
      | nil => Q empSP
      | i :: is' => wpi cls this i (fun f => f ** wpis cls this is' Q)
      end.

    Axiom wp_init_constructor : forall cls addr cnd es Q ty,
      wp_args es (fun ls free =>
         Exists ctor, _global cnd &~ ctor **
                              |> fspec (Vptr ctor) (addr :: ls) (fun _ => Q free))
      |-- wp_init (Tnamed cls) addr (Econstructor cnd es ty) Q.

    Definition build_array (es : list Expr) (fill : option Expr) (sz : nat)
    : option (list (Z * Expr)) :=
      if Nat.ltb (List.length es) sz then
        match fill with
        | None => None
        | Some f =>
          Some (List.combine (List.map Z.of_nat (seq 0 sz))
                             (List.app es (map (fun _ => f) (seq (List.length es) (sz - 1)))))
        end
      else
        Some (List.combine (List.map Z.of_nat (seq 0 sz))
                           (firstn sz es)).

    Fixpoint wp_array_init (ety : type) (base : val) (es : list (Z * Expr)) (Q : mpred -> mpred) : mpred :=
      match es with
      | nil => Q empSP
      | (i,e) :: es =>
        Forall a, _offsetL (_sub ety i) (_eqv base) &~ a -*
        Exists Qi, wp_init ety (Vptr a) e Qi **
        wp_array_init ety base es (fun free' =>
          Forall free, Qi free -* Q (free ** free'))
      end.


    Axiom wp_init_initlist_array :forall ls fill ety sz addr Q,
      match build_array ls fill (N.to_nat sz) with
      | None => lfalse
      | Some array_list =>
        (* _at (_eqv addr) (anyR (erase_qualifiers (Tarray ety sz)) 1) ** *)
        wp_array_init ety addr array_list (fun free => Q free)
      end
      |-- wp_init (Tarray ety sz) addr (Einitlist ls fill (Tarray ety sz)) Q.

    Axiom wp_init_cast_noop : forall e ty loc ty' Q,
        wp_init loc ty e Q
        |-- wp_init loc ty (Ecast Cnoop (Rvalue, e) ty') Q.

    Axiom wp_init_clean : forall e ty ty' addr Q,
        wp_init ty' addr e Q
        |-- wp_init ty' addr (Eandclean e ty) Q.
    Axiom wp_init_const : forall ty addr e Q,
        wp_init ty addr e Q
        |-- wp_init (Qconst ty) addr e Q.
    Axiom wp_init_mut : forall ty addr e Q,
        wp_init ty addr e Q
        |-- wp_init (Qmut ty) addr e Q.

  End with_resolve.

End Init.

Declare Module IN : Init.

Export IN.
