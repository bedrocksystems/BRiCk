(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import base.
From bedrock.lang.cpp.syntax Require Export names types stmt translation_unit.
From bedrock.lang.cpp.semantics Require Export sub_module.

(**
A [genv] describes the dynamic semantics of a potentially incomplete program,
comprising one or more C++ translation units.
Most proofs only quantify over a single `σ : genv`, representing the complete
program being verified.

The interface includes:
- an injection of C++ translation units to genvs (which represents compilation).
- and a composition of [genv]s (which represents linking).

Today, we compose [genv]s by composing [translation_unit]s, but this is an
implementation detail that might change (see FM-2738).

A [genv] contains the result of linking translation units, plus any additional
information supplied by compiler/linker/loader/...

If we add support for dynamic linking, additional [genv]s might be involved.

If we want to do things like word-size agnostic verification, then
information about sizes etc. would need to move in here as well.

TODO: seal this?
*)
Record genv : Type :=
{ genv_tu : translation_unit
  (* ^ Implementation detail: the result of merging all the [translation_unit]s
  in the program. Might be replaced when fixing FM-2738. *)
; pointer_size_bitsize : bitsize
  (* ^ the size of a pointer *)
}.
Existing Class genv.
Definition genv_byte_order (g : genv) : endian :=
  g.(genv_tu).(byte_order).
Definition pointer_size (g : genv) := bytesN (pointer_size_bitsize g).

(** * global environments *)

(** [genv_leq a b] states that [b] is an extension of [a] *)
Record genv_leq {l r : genv} : Prop :=
{ tu_le : sub_module l.(genv_tu) r.(genv_tu)
; pointer_size_le : l.(pointer_size_bitsize) = r.(pointer_size_bitsize) }.
Arguments genv_leq _ _ : clear implicits.

#[global] Instance PreOrder_genv_leq : PreOrder genv_leq.
Proof.
  constructor.
  { constructor; auto; reflexivity. }
  { red. destruct 1; destruct 1; constructor; try etransitivity; eauto. }
Qed.
#[global] Instance: RewriteRelation genv_leq := {}.

Definition genv_eq (l r : genv) : Prop :=
  genv_leq l r /\ genv_leq r l.

#[global] Instance genv_tu_proper : Proper (genv_leq ==> sub_module) genv_tu.
Proof. solve_proper. Qed.
#[global] Instance genv_tu_flip_proper : Proper (flip genv_leq ==> flip sub_module) genv_tu.
Proof. solve_proper. Qed.

(* Sadly, neither instance is picked up by [f_equiv]. *)
#[global] Instance pointer_size_bitsize_proper : Proper (genv_leq ==> eq) pointer_size_bitsize.
Proof. solve_proper. Qed.
#[global] Instance pointer_size_bitsize_flip_proper : Proper (flip genv_leq ==> eq) pointer_size_bitsize.
Proof. by intros ?? <-. Qed.
#[global] Instance pointer_size_proper : Proper (genv_leq ==> eq) pointer_size.
Proof. unfold pointer_size; intros ???. f_equiv. exact: pointer_size_bitsize_proper. Qed.
#[global] Instance pointer_size_flip_proper : Proper (flip genv_leq ==> eq) pointer_size.
Proof. by intros ?? <-. Qed.

#[global] Instance genv_byte_order_proper : Proper (genv_leq ==> eq) genv_byte_order.
Proof. intros ???. apply sub_module.byte_order_proper. solve_proper. Qed.
#[global] Instance genv_byte_order_flip_proper : Proper (flip genv_leq ==> eq) genv_byte_order.
Proof. by intros ?? <-. Qed.
(* this states that the [genv] is compatible with the given [translation_unit]
 * it essentially means that the [genv] records all the types from the
 * compilation unit and that the [genv] contains addresses for all globals
 * defined in the [translation_unit]
 *)
Class genv_compat {tu : translation_unit} {g : genv} : Prop :=
{ tu_compat : sub_module tu g.(genv_tu) }.
Arguments genv_compat _ _ : clear implicits.
Infix "⊧" := genv_compat (at level 1).

Theorem genv_byte_order_tu tu g :
    tu ⊧ g ->
    genv_byte_order g = translation_unit.byte_order tu.
Proof. intros. apply byte_order_flip_proper, tu_compat. Qed.

Theorem genv_compat_submodule : forall m σ, m ⊧ σ -> sub_module m σ.(genv_tu).
Proof. by destruct 1. Qed.

#[global] Instance genv_compat_proper : Proper (flip sub_module ==> genv_leq ==> impl) genv_compat.
Proof.
  intros ?? Heq1 ?? [Heq2 _] [Heq3]; constructor.
  by rewrite Heq1 Heq3.
Qed.
#[global] Instance genv_compat_flip_proper : Proper (sub_module ==> flip genv_leq ==> flip impl) genv_compat.
Proof. solve_proper. Qed.

Lemma module_le_genv_tu_models X σ :
  module_le X (genv_tu σ) ->
  X ⊧ σ.
Proof.
  generalize (module_le_sound X (genv_tu σ)).
  unfold Is_true in *.
  case_match; try contradiction. intros.
  apply Build_genv_compat. assumption.
Qed.

(** TODO deprecate this in favor of inlining it *)
Definition glob_def (g : genv) (gn : globname) : option GlobDecl :=
  g.(genv_tu) !! gn.

(* Supersedes glob_def_submodule *)
Lemma glob_def_genv_compat_struct {σ gn tu} {Hσ : tu ⊧ σ} st
  (Hl : tu !! gn = Some (Gstruct st)) :
  glob_def σ gn = Some (Gstruct st).
Proof. move: Hσ Hl => /genv_compat_submodule. apply: sub_module_preserves_gstruct. Qed.

Lemma glob_def_genv_compat_union {σ gn tu} {Hσ : tu ⊧ σ} st
  (Hl : tu !! gn = Some (Gunion st)) :
  glob_def σ gn = Some (Gunion st).
Proof. move: Hσ Hl => /genv_compat_submodule. apply: sub_module_preserves_gunion. Qed.


(* XXX rename/deprecate? *)
Theorem subModuleModels a b σ : b ⊧ σ -> sub_module a b -> a ⊧ σ.
Proof. by intros ? ->. Qed.

(** compute the type of a [class] or [union] field *)
Section type_of_field.
  Context {σ: genv}.

  Definition type_of_field (cls : globname) (f : ident) : option type :=
    match σ.(genv_tu) !! cls with
    | None => None
    | Some (Gstruct st) =>
      match List.find (fun m => bool_decide (f = m.(mem_name))) st.(s_fields) with
      | Some m => Some m.(mem_type)
      | _ => None
      end
    | Some (Gunion u) =>
      match List.find (fun m => bool_decide (f = m.(mem_name))) u.(u_fields) with
      | Some m => Some m.(mem_type)
      | _ => None
      end
    | _ => None
    end.

  Definition type_of_path (from : globname) (p : InitPath) : option type :=
    match p with
    | InitThis => Some (Tnamed from)
    | InitField fn => type_of_field from fn
    | InitBase gn => Some (Tnamed gn)
    | InitIndirect ls i =>
      (* this is a little bit awkward because we assume the correctness of
         the type annotations in the path
       *)
      (fix go (from : globname) (ls : _) : option type :=
         match ls with
         | nil => type_of_field from i
         | (_, gn) :: ls => go gn ls
         end) from ls
    end.

End type_of_field.
