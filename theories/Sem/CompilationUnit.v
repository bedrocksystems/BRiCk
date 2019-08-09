(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Coq.Classes Require Import
     RelationClasses Morphisms DecidableClass.

Require Import Coq.Lists.List.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

Require Import Cpp.Util.
From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Util Logic Semantics PLogic.


Module Type modules.

  Definition denoteSymbol (n : obj_name) (o : ObjValue) : mpred :=
    match o with
    | Ovar _ _ =>
      Exists a, with_genv (fun resolve => [| glob_addr resolve n a |])
    | Ofunction f =>
      match f.(f_body) return mpred with
      | None =>
        Exists a, with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\
                  code_at f a
      end
    | Omethod m =>
      match m.(m_body) return mpred with
      | None =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\
                  code_at {| f_return := m.(m_return)
                           ; f_params := ("#this"%string, Tqualified m.(m_this_qual) (Tref m.(m_class))) :: m.(m_params)
                           ; f_body := m.(m_body) |} a
      end
    | Oconstructor c =>
      match c.(c_body) return mpred with
      | None =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\ ctor_at a c
      end
    | Odestructor d =>
      match d.(d_body) return mpred with
      | None =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\ dtor_at a d
      end
    end.

  Definition find_struct (nm : globname) (m : compilation_unit) : option Struct :=
    match CompilationUnit.lookup_global m nm with
    | Some (Gstruct s) => Some s
    | _ => None
    end.

  Definition denoteGlobal (gn : globname) (g : GlobDecl) : mpred :=
    match g with
    | Gtypedef _ => empSP
      (* note(gmm): this is compile time, and shouldn't be a problem.
       *)
    | Gstruct _ => empSP
      (* ^ this should record size and offset information *)
    | Gunion _ => empSP
      (* ^ this should record size and offset information *)
    | Genum _ => empSP
      (* ^ this should record enumeration information *)
    | Gconstant val _ => empSP
      (* ^ this should record constant information *)
    | Gtypedec => empSP
    end.

  Definition denoteModule (d : compilation_unit) : mpred :=
    sepSPs (List.map (fun '(gn,g) => denoteGlobal gn g) d.(globals)) **
    sepSPs (List.map (fun '(on,o) => denoteSymbol on o) d.(symbols)).

  Axiom denoteModule_weaken : forall m, denoteModule m |-- empSP.

  (* Axiom denote_module_dup : forall module, *)
  (*     denoteModule module -|- denoteModule module ** denoteModule module. *)

  Theorem denoteModule_link : forall a b c,
      link a b = Some c ->
      denoteModule c -|- denoteModule a ** denoteModule b.
  Proof. Admitted.

End modules.

Declare Module M : modules.

Export M.

Arguments denoteModule _ : simpl never.
