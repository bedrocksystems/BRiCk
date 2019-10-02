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

Require Import Cpp.Util.
From Cpp Require Import
     Ast.
From Cpp.Sem Require Import
     ChargeUtil Logic Semantics PLogic.

From Cpp Require Import IrisBridge.
Import ChargeNotation.

Module Type modules.

  Section with_Σ.
  Context {Σ:gFunctors}.

  Notation mpred := (mpred Σ) (only parsing).
  Notation Offset := (Offset Σ) (only parsing).

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

  Definition OffsetOf (f : Offset) (n : Z) : mpred :=
    Forall l, _offsetL f (_eq l) &~ offset_ptr l n.

  Local Fixpoint ranges_to_list {T} (P : T -> Z * N -> mpred) (ls : list T) (rs : list (Z * N)) : mpred :=
    match ls with
    | nil => [| rs = nil |]
    | l :: ls =>
      Exists os, P l os **
      Exists rs', ranges_to_list P ls rs' ** [| rs = os :: rs' |]
    end.

  Fixpoint disjoint (ls : list (Z * N)) : Prop :=
    match ls with
    | nil => True
    | (o,s) :: ls =>
      let non_overlapping '(o',s') :=
          ((o <= o' /\ o + Z.of_N s <= o') \/ (o' <= o /\ o' + Z.of_N s' <= o))%Z
      in
      List.Forall non_overlapping ls /\ disjoint ls
    end.

  Definition denoteGlobal (gn : globname) (g : GlobDecl) : mpred :=
    match g with
    | Gtypedef _ => empSP
      (* note(gmm): this is compile time, and shouldn't be a problem.
       *)
    | Gstruct str =>
      sepSPs (map (fun '(nm, li) => OffsetOf (_super gn nm) li.(li_offset)) str.(s_bases)) **
      sepSPs (map (fun '(nm, _, li) => OffsetOf (_field {| f_type := gn ; f_name := nm |}) li.(li_offset)) str.(s_fields)) **
      Exists os, Exists os',
      ranges_to_list (fun '(nm,li) '(off,sz) => with_genv (fun prg =>
                        [| off = li.(li_offset) |] **
                        [| @size_of prg (Tref nm) sz |])) str.(s_bases) os **
      ranges_to_list (fun '(_,ty,li) '(off,sz) => with_genv (fun prg =>
                        [| off = li.(li_offset) |] **
                        [| @size_of prg ty sz |])) str.(s_fields) os' **
      [| List.Forall (fun '(off,sz) => 0 <= off /\ off + Z.of_N sz <= Z.of_N str.(s_size))%Z (os ++ os') |] **
      [| disjoint (os ++ os') |]
      (* ^ this should record size and offset information *)
    | Gunion uni =>
      sepSPs (map (fun '(nm, _, li) => OffsetOf (_field {| f_type := gn ; f_name := nm |}) li.(li_offset)) uni.(u_fields)) **
      Exists os,
      ranges_to_list (fun '(_,ty,li) '(off,sz) => with_genv (fun prg =>
                        [| off = li.(li_offset) |] **
                        [| @size_of prg ty sz |])) uni.(u_fields) os **
      [| List.Forall (fun '(off,sz) => 0 <= off /\ off + Z.of_N sz <= Z.of_N uni.(u_size))%Z os |]
      (* ^ this should record size and offset information *)
    | Genum _ => empSP
      (* ^ this should record enumeration information *)
    | Gconstant val _ => empSP
      (* ^ this should record constant information *)
    | Gtypedec => empSP
    | Gtype => empSP
    end.

  Definition denoteModule_def (d : compilation_unit) : mpred :=
    sepSPs (List.map (fun '(gn,g) => denoteGlobal gn g) d.(globals)) **
    sepSPs (List.map (fun '(on,o) => denoteSymbol on o) d.(symbols)).
  Definition denoteModule_aux : seal (@denoteModule_def). by eexists. Qed.
  Definition denoteModule := denoteModule_aux.(unseal).
  Definition denoteModule_eq : @denoteModule = _ := denoteModule_aux.(seal_eq).

  Axiom denoteModule_weaken : forall m, denoteModule m |-- empSP.

  (* Axiom denote_module_dup : forall module, *)
  (*     denoteModule module -|- denoteModule module ** denoteModule module. *)

  Theorem denoteModule_link : forall a b c,
      link a b = Some c ->
      denoteModule c -|- denoteModule a ** denoteModule b.
  Proof. Admitted.
  End with_Σ.

End modules.

Declare Module M : modules.

Export M.

Arguments denoteModule _ : simpl never.
