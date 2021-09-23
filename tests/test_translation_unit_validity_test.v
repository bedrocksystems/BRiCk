(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From stdpp Require Import fin_maps.
From bedrock.prelude Require Import base bytestring.
From bedrock.lang.cpp Require Import syntax.translation_unit syntax.types.

Require Import bedrocktest.test_translation_unit_validity_cpp.

#[local] Hint Constructors complete_decl complete_basic_type complete_type
  complete_pointee_type wellscoped_type wellscoped_types : core.
#[local] Hint Constructors valid_decl : core.
#[local] Hint Extern 10 => done : core.

Instance: OMap avl.IM.t. Admitted.
Instance: FinMap bs avl.IM.t. Admitted.

#[local] Hint Extern 10 => match goal with
| H : In _ _ |- _ => simpl in *; intuition simplify_eq
end : core.

Goal complete_translation_unit (globals module) (symbols module).
Proof.
  rewrite /complete_translation_unit /complete_type_table /complete_symbol_table.
  (* split; (unshelve eapply map_Forall_to_list; refine _; [shelve..|]). *)
  split; apply map_Forall_to_list.
  all: remember (map_to_list _) as l; lazy in Heql; subst.
  #[local] Opaque module.
  all: repeat apply List.Forall_cons; rewrite /type_of_value/=/qual_norm/=; eauto 20.
Qed.
#[local] Transparent module.

(* XXX These settings are only good to print raw contents. *)
Module view_awl.
  Export avl.IM.Raw(Leaf, Node).
  Export avl.IM(bst, Bst).

  (* Can these settings be #[export]? Not a priority. *)

  (* Hide proof [I] *)
  Add Printing Constructor avl.IM.bst.
  Arguments avl.IM.Bst {_} _ {_}.

  Arguments avl.IM.Raw.Leaf {_}.
  Arguments avl.IM.Raw.Node {_} _ _ _ _ {_}. (* Hide AVL depth *)

  (* Only for debugging, disabled in CI. *)
  (* Eval cbv in globals module. *)
  (* Eval cbv in map snd $ map_to_list (globals module). *)
End view_awl.
