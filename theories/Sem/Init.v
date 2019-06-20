(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Util Logic PLogic Semantics Wp Typing.

Module Type Init.

  Section with_resolve.
    Context {resolve : genv}.
    Variable ti : thread_info.
    Variable ρ : region.

    Local Notation wp := (wp (resolve:=resolve)  ti ρ).
    Local Notation wpe := (wpe (resolve:=resolve) ti ρ).
    Local Notation wp_lhs := (wp_lhs (resolve:=resolve) ti ρ).
    Local Notation wp_rhs := (wp_rhs (resolve:=resolve) ti ρ).
    Local Notation wpAny := (wpAny (resolve:=resolve) ti ρ).
    Local Notation wpAnys := (wpAnys (resolve:=resolve) ti ρ).
    Local Notation fspec := (fspec (resolve:=resolve)).

  (** initialization lists *)
  Parameter wpi
  : forall {resolve : genv} (ti : thread_info) (ρ : region)
      (cls : globname) (this : val) (init : FieldOrBase * Expr)
      (Q : mpred), mpred.

  Fixpoint wpis (cls : globname) (this : val)
           (inits : list (FieldOrBase * Expr))
           (Q : mpred) : mpred :=
    match inits with
    | nil => Q
    | i :: is => @wpi resolve ti ρ cls this i (wpis cls this is Q)
    end.

  Fixpoint wpi_field (cls : globname) (this : Loc)
           (ty : type) (f : field) (init : Expr)
           (k : mpred)
  : mpred :=
    match ty with
    | Trv_reference t
    | Treference t =>
      (* i should use the type here *)
      wp_lhs init (fun a free =>
            (* note(gmm): this is consistent with the specification, but also very strange *)
            _offsetL (_field f) this &~ a
         -* (free ** k))
    | Tfunction _ _ =>
      (* fields can not be function type *)
      lfalse
    | Tvoid => lfalse
    | Tpointer _
    | Tbool
    | Tchar _ _
    | Tint _ _ =>
      wp_rhs init (fun v free =>
         _at (_offsetL (_field f) this) (uninit ty) **
         (   _at (_offsetL (_field f) this) (tprim ty v)
          -* (free ** k)))
    | Tarray _ _ => lfalse (* todo(gmm): arrays not yet supported *)
    | Tref gn =>
      match init with
      | Econstructor cnd es _ =>
        (* todo(gmm): constructors need to be handled through `cglob`.
         *)
        Exists ctor, [| glob_addr resolve cnd ctor |] **
        (* todo(gmm): is there a better way to get the destructor? *)
        wps wpAnys es (fun vs free =>
            Forall a, (_offsetL (_field f) this &~ a ** ltrue) //\\
            |> fspec (Vptr ctor) (a :: vs) ti (fun _ =>
               (free ** k))) empSP
      | _ => lfalse
        (* ^ all non-primitive declarations must have initializers *)
      end
    | Tqualified _ ty => wpi_field cls this ty f init k
    end.

  Axiom wpi_field_at : forall this_val x e cls Q,
      wpi_field cls (_eq this_val) (drop_qualifiers (type_of e)) {| f_type := cls ; f_name := x |} e Q
      |-- @wpi resolve ti ρ cls this_val (Field x, e) Q.

  End with_resolve.

End Init.

Declare Module IN : Init.

Export IN.
