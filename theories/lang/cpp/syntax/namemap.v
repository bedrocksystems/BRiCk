(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Structures.OrderedTypeAlt.
Require Import Stdlib.FSets.FMapAVL.
Require Import bedrock.prelude.avl.
Require Import bedrock.prelude.compare.
Require Import bedrock.lang.cpp.syntax.prelude.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.compare.

(** ** Name maps *)

#[global] Declare Instance name_comparison {lang} :
  Comparison (compareN (lang:=lang)).	(** TODO *)

Module Import internal.

  Module Type LANG.
    Parameter Inline lang : lang.t.
  End LANG.

  Module NameMap (Lang : LANG).
    Module Compare.
      Definition t : Type := name' Lang.lang.
      #[local] Definition compare : t -> t -> comparison := compareN.
      #[local] Infix "?=" := compare.
      #[local] Lemma compare_sym x y : (y ?= x) = CompOpp (x ?= y).
      Proof. exact: compare_antisym. Qed.
      #[local] Lemma compare_trans c x y z : (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
      Proof. exact: base.compare_trans. Qed.
    End Compare.
    Module Key := OrderedType_from_Alt Compare.
    Lemma eqL : forall a b, Key.eq a b -> @eq _ a b.
    Proof. (* proof the comparison equality is Leibnize equality *) Admitted.
    Include FMapAVL.Make Key.
    Include FMapExtra.MIXIN Key.
    Include FMapExtra.MIXIN_LEIBNIZ Key.
  End NameMap.

End internal.

Module NM.
  #[local] Definition lang := lang.cpp.
  Include NameMap.
End NM.

Module TM.
  #[local] Definition lang := lang.temp.
  Include NameMap.
End TM.
