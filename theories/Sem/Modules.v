(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
From Coq.Classes Require Import
     RelationClasses Morphisms.

Require Import Coq.Lists.List.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.


From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     Util Logic Semantics PLogic.

Module Type modules.

  (* this is the denotation of modules *)

  (* note(gmm): two ways to support initializer lists.
   * 1/ add them to all functions (they are almost always empty
   * 2/ make a `ctor_at` (similar to `code_at`) that handles
   *    constructors.
   * ===
   * 2 seems like the more natural way to go.
   *)

  (* note(gmm): the denotation of modules should be moved to another module.
   *)
  Fixpoint denoteDecl (d : Decl) : mpred :=
    match d with
    | Dvar n _ _ =>
      Exists a, with_genv (fun resolve => [| glob_addr resolve n a |])
    | Dtypedef gn _ => empSP
                       (* note(gmm): this is compile time, and shouldn't be a
                        * problem.
                        *)
    | Dfunction n f =>
      match f.(f_body) return mpred with
      | None =>
        Exists a, with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\
                  code_at f a
      end
    | Dmethod n m =>
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
    | Dconstructor n m =>
      match m.(c_body) return mpred with
      | None =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\ ctor_at a m
      end
    | Ddestructor n m =>
      match m.(d_body) return mpred with
      | None =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |])
      | Some body =>
        Exists a,
        with_genv (fun resolve => [| glob_addr resolve n a |]) //\\ dtor_at a m
      end
    | Dstruct gn _ => empSP
      (* ^ this should record size and offset information
       *)
    | Denum gn _ _ => empSP
      (* ^ this should record enumeration information
       *)
    | Dconstant gn val _ => empSP
    (* | Dnamespace ds => *)
    (*   sepSPs (map denoteDecl ds) *)
    (* | Dextern ds => *)
    (*   sepSPs (map denoteDecl ds) *)
    end.

  Fixpoint denoteModule (d : list Decl) : mpred :=
    match d with
    | nil => empSP
    | d :: ds => denoteDecl d ** denoteModule ds
    end.


  Axiom denoteModule_weaken : forall m, denoteModule m |-- empSP.

  Axiom denote_module_dup : forall module,
      denoteModule module -|- denoteModule module ** denoteModule module.

End modules.

Declare Module M : modules.

Export M.

Arguments denoteModule _ : simpl never.