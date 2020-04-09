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

From bedrock Require Import IrisBridge.
Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp Require Import
     semantics logic.pred logic.heap_pred.

Import ChargeNotation.

Module Type modules.

  Section with_Σ.
  Context {Σ:gFunctors} {resolve:genv}.

  Notation mpred := (mpred Σ) (only parsing).
  Local Notation _global := (@_global resolve) (only parsing).
  Local Notation code_at := (@code_at Σ resolve) (only parsing).
  Local Notation ctor_at := (@ctor_at Σ resolve) (only parsing).
  Local Notation dtor_at := (@dtor_at Σ resolve) (only parsing).
  Local Notation _field := (@_field resolve) (only parsing).
  Local Notation _super := (@_super resolve) (only parsing).
  Local Notation _sub := (@_sub resolve) (only parsing).

  Definition denoteSymbol (n : obj_name) (o : ObjValue) : mpred :=
    match o with
    | Ovar _ _ =>
      Exists a, _global n &~ a
    | Ofunction f =>
      match f.(f_body) return mpred with
      | None =>
        Exists a, _global n &~ a
      | Some body =>
        Exists a, _global n &~ a //\\
                  code_at f a
      end
    | Omethod m =>
      match m.(m_body) return mpred with
      | None =>
        Exists a, _global n &~ a
      | Some body =>
        Exists a, _global n &~ a //\\
                  code_at {| f_return := m.(m_return)
                           ; f_params := ("#this"%string, Tqualified m.(m_this_qual) (Tnamed m.(m_class))) :: m.(m_params)
                           ; f_body := m.(m_body) |} a
      end
    | Oconstructor c =>
      match c.(c_body) return mpred with
      | None =>
        Exists a, _global n &~ a
      | Some body =>
        Exists a, _global n &~ a //\\ ctor_at a c
      end
    | Odestructor d =>
      match d.(d_body) return mpred with
      | None =>
        Exists a, _global n &~ a
      | Some body =>
        Exists a, _global n &~ a //\\ dtor_at a d
      end
    end.

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

  Definition denoteModule_def (d : compilation_unit) : mpred :=
    sepSPs (List.map (fun '(on,o) => denoteSymbol on o) d.(symbols)) **
    [| module_le d resolve.(genv_cu) |].
  Definition denoteModule_aux : seal (@denoteModule_def). by eexists. Qed.
  Definition denoteModule := denoteModule_aux.(unseal).
  Definition denoteModule_eq : @denoteModule = _ := denoteModule_aux.(seal_eq).

  Axiom denoteModule_weaken : forall m, denoteModule m |-- empSP.

  Lemma subModuleModels a b σ: module_le a b = true -> b ⊧ σ -> a ⊧ σ.
  Proof using.
  Admitted.

  (* Axiom denote_module_dup : forall module, *)
  (*     denoteModule module -|- denoteModule module ** denoteModule module. *)

  (* Theorem denoteModule_link : forall a b c, *)
  (*     link a b = Some c -> *)
  (*     denoteModule c -|- denoteModule a ** denoteModule b. *)
  (* Proof. Admitted. *)
  End with_Σ.

End modules.

Declare Module M : modules.

Export M.

Arguments denoteModule _ : simpl never.
